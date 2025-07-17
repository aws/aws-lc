# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing
from enum import Enum

from aws_cdk import Stack, Environment, Duration
from aws_cdk import (
    pipelines,
    aws_codestarconnections as codestarconnections,
    aws_codepipeline as codepipeline,
    aws_iam as iam,
    aws_events as events,
    aws_events_targets as targets,
    aws_codebuild as codebuild,
)
from aws_cdk.pipelines import CodeBuildStep, ManualApprovalStep
from constructs import Construct

from pipeline.ci_stage import CiStage
from pipeline.linux_docker_image_build_stage import LinuxDockerImageBuildStage
from pipeline.setup_stage import SetupStage
from pipeline.windows_docker_image_build_stage import WindowsDockerImageBuildStage
from util.metadata import *


class DeployEnvironmentType(Enum):
    PRE_PROD = "Staging"
    PROD = "Prod"
    DEV = "Dev"


class AwsLcCiPipeline(Stack):
    def __init__(
        self,
        scope: Construct,
        id: str,
        **kwargs,
    ) -> None:
        super().__init__(
            scope,
            id,
            **kwargs,
        )

        gh_connection = codestarconnections.CfnConnection(
            self,
            "GitHubConnection",
            connection_name="AwsLcCiPipelineGitHubConnection",
            provider_type="GitHub",
        )

        cross_account_role = iam.Role(
            self,
            "CrossAccountPipelineRole",
            role_name="CrossAccountPipelineRole",
            assumed_by=iam.CompositePrincipal(
                iam.ServicePrincipal("codebuild.amazonaws.com"),
                iam.ServicePrincipal("codepipeline.amazonaws.com"),
            ),
        )

        cross_account_role.add_to_policy(
            iam.PolicyStatement(
                effect=iam.Effect.ALLOW,
                resources=["*"],
                actions=[
                    "codepipeline:GetPipelineExecution",
                    "secretsmanager:GetSecretValue",
                    "kms:Decrypt",
                ],
            )
        )

        source = pipelines.CodePipelineSource.connection(
            f"{GITHUB_REPO_OWNER}/{GITHUB_REPO_NAME}",
            GITHUB_SOURCE_VERSION,
            connection_arn=gh_connection.attr_connection_arn,
            code_build_clone_output=True,
        )

        # Create a base pipeline to upgrade the default pipeline type
        base_pipeline = codepipeline.Pipeline(
            self,
            "AwsLcCiPipeline",
            execution_mode=codepipeline.ExecutionMode.QUEUED,
            pipeline_type=codepipeline.PipelineType.V2,
            pipeline_name="AwsLcCiPipeline",
            cross_account_keys=True,
            enable_key_rotation=True,
            restart_execution_on_update=True,
        )

        # Bucket contains artifacts from old pipeline executions
        # These artifacts are kept for 60 days in case we need to do a rollback
        base_pipeline.artifact_bucket.add_lifecycle_rule(
            enabled=True,
            expiration=Duration.days(60),
        )

        cdk_env = {
            "GITHUB_REPO_OWNER": GITHUB_REPO_OWNER,
            "GITHUB_REPO_NAME": GITHUB_REPO_NAME,
            "GITHUB_SOURCE_VERSION": GITHUB_SOURCE_VERSION,
            "GITHUB_TOKEN_SECRET_NAME": GITHUB_TOKEN_SECRET_NAME,
            "PIPELINE_ACCOUNT": PIPELINE_ACCOUNT,
            "PIPELINE_REGION": PIPELINE_REGION,
            "WIN_EC2_TAG_KEY": WIN_EC2_TAG_KEY,
            "WIN_EC2_TAG_VALUE": WIN_EC2_TAG_VALUE,
            "WIN_DOCKER_BUILD_SSM_DOCUMENT": SSM_DOCUMENT_NAME,
            "LINUX_AARCH_ECR_REPO": LINUX_AARCH_ECR_REPO,
            "LINUX_X86_ECR_REPO": LINUX_X86_ECR_REPO,
            "WINDOWS_X86_ECR_REPO": WINDOWS_X86_ECR_REPO,
            "IS_DEV": str(IS_DEV),
        }

        if DEPLOY_ACCOUNT is not None and DEPLOY_REGION is not None:
            cdk_env["DEPLOY_ACCOUNT"] = DEPLOY_ACCOUNT
            cdk_env["DEPLOY_REGION"] = DEPLOY_REGION

        pipeline = pipelines.CodePipeline(
            self,
            "CdkPipeline",
            code_pipeline=base_pipeline,
            # pipeline_name="AwsLcCiPipeline",
            synth=pipelines.ShellStep(
                "Synth",
                input=source,
                commands=[
                    'echo "Environment variables:"',
                    "env",
                    "npm install -g aws-cdk",
                    "cd tests/ci",
                    "python -m pip install -r requirements.txt",
                    "cd cdk",
                    "cdk synth",
                ],
                env=cdk_env,
                primary_output_directory="tests/ci/cdk/cdk.out",
            ),
            self_mutation=True,
            code_build_defaults=pipelines.CodeBuildOptions(
                build_environment=codebuild.BuildEnvironment(
                    compute_type=codebuild.ComputeType.MEDIUM,
                ),
                role_policy=[
                    iam.PolicyStatement(
                        effect=iam.Effect.ALLOW,
                        resources=["*"],
                        actions=["sts:AssumeRole"],
                        conditions={
                            "StringEquals": {
                                "iam:ResourceTag/aws-cdk:bootstrap-role": "lookup",
                            }
                        },
                    ),
                ],
            ),
        )

        if IS_DEV:
            self.deploy_to_environment(
                DeployEnvironmentType.DEV,
                pipeline=pipeline,
                source=source,
                cross_account_role=cross_account_role,
            )
        else:
            self.deploy_to_environment(
                DeployEnvironmentType.PRE_PROD,
                pipeline=pipeline,
                source=source,
                cross_account_role=cross_account_role,
            )

            self.deploy_to_environment(
                DeployEnvironmentType.PROD,
                pipeline=pipeline,
                source=source,
                cross_account_role=cross_account_role,
            )

        pipeline.build_pipeline()

        # Schedule pipeline to run every Tuesday 15:00 UTC or 7:00 PST
        events.Rule(
            self,
            "WeeklyCodePipelineRun",
            schedule=events.Schedule.cron(
                minute="0",
                hour="15",
                week_day="TUE",
            ),
            targets=[targets.CodePipeline(pipeline=base_pipeline)],
        )

        # Pipeline is run everytime we push to main branch. Avoid unnecessary hold up if these updates are non-CI related
        if not IS_DEV:
            start_index = next(
                (i for i, stage in enumerate(base_pipeline.stages) if stage.stage_name == "PromoteToProduction"),
                None
            )

            override_condition = {
                "Conditions": [
                    {
                        "Result": "SKIP",
                        "Rules": [
                            {
                                "Name": "Skip_Prod_Deployment",
                                "RuleTypeId": {
                                    "Category": "Rule",
                                    "Owner": "AWS",
                                    "Provider": "VariableCheck",
                                    "Version": "1"
                                },
                                "Configuration": {
                                    "Variable": "#{Staging-CiTests@PrebuildCheck.NEED_REBUILD}",
                                    "Value": "0",
                                    "Operator": "NE"
                                },
                            }
                        ]
                    }
                ]
            }

            l1_pipeline = base_pipeline.node.default_child

            for i in range(start_index, int(base_pipeline.stage_count)):
                l1_pipeline.add_override(
                    f"Properties.Stages.{i}.BeforeEntry",
                    override_condition
                )

    def deploy_to_environment(
        self,
        deploy_environment_type: DeployEnvironmentType,
        pipeline: pipelines.CodePipeline,
        source: pipelines.CodePipelineSource,
        cross_account_role: iam.Role,
        codebuild_environment_variables: typing.Optional[
            typing.Mapping[str, str]
        ] = None,
    ):
        pipeline_environment = Environment(
            account=PIPELINE_ACCOUNT, region=PIPELINE_REGION
        )

        if deploy_environment_type == DeployEnvironmentType.PRE_PROD:
            deploy_environment = Environment(
                account=PRE_PROD_ACCOUNT, region=PRE_PROD_REGION
            )
        elif deploy_environment_type == DeployEnvironmentType.DEV:
            deploy_environment = Environment(
                account=DEPLOY_ACCOUNT, region=DEPLOY_REGION
            )
        else:
            deploy_environment = Environment(account=PROD_ACCOUNT, region=PROD_REGION)

        codebuild_environment_variables = (
            codebuild_environment_variables if codebuild_environment_variables else {}
        )

        codebuild_environment_variables = {
            **codebuild_environment_variables,
            "PIPELINE_EXECUTION_ID": "#{codepipeline.PipelineExecutionId}",
            "DEPLOY_ACCOUNT": deploy_environment.account,
            "DEPLOY_REGION": deploy_environment.region,
        }

        cross_account_role.add_to_policy(
            iam.PolicyStatement(
                effect=iam.Effect.ALLOW,
                resources=[
                    f"arn:aws:iam::{deploy_environment.account}:role/CrossAccountBuildRole"
                ],
                actions=["sts:AssumeRole"],
            )
        )

        if deploy_environment_type == DeployEnvironmentType.PROD:
            pipeline.add_wave(
                "PromoteToProduction",
                pre=[ManualApprovalStep("PromoteToProduction")]
            )

        setup_stage = SetupStage(
            self,
            f"{deploy_environment_type.value}-Setup",
            pipeline_environment=pipeline_environment,
            deploy_environment=deploy_environment,
        )

        pipeline.add_stage(setup_stage)

        docker_build_wave = pipeline.add_wave(
            f"{deploy_environment_type.value}-DockerImageBuild"
        )

        linux_stage = LinuxDockerImageBuildStage(
            self,
            f"{deploy_environment_type.value}-LinuxDockerImageBuild",
            pipeline_environment=pipeline_environment,
            deploy_environment=deploy_environment,
        )

        linux_stage.add_stage_to_wave(
            wave=docker_build_wave,
            input=source.primary_output,
            role=cross_account_role,
            additional_stacks=setup_stage.stacks,
            max_retry=MAX_TEST_RETRY,
            env=codebuild_environment_variables,
        )

        windows_stage = WindowsDockerImageBuildStage(
            self,
            f"{deploy_environment_type.value}-WindowsDockerImageBuild",
            pipeline_environment=pipeline_environment,
            deploy_environment=deploy_environment,
        )

        windows_stage.add_stage_to_wave(
            wave=docker_build_wave,
            input=source.primary_output,
            role=cross_account_role,
            additional_stacks=setup_stage.stacks,
            max_retry=MAX_TEST_RETRY,
            env=codebuild_environment_variables,
        )

        docker_build_wave.add_post(
            CodeBuildStep(
                f"{deploy_environment_type.value}-FinalizeImages",
                input=source,
                commands=[
                    "cd tests/ci/cdk/pipeline/scripts",
                    './finalize_images.sh --repos "${ECR_REPOS}"',
                ],
                env={
                    **codebuild_environment_variables,
                    "ECR_REPOS": f"{' '.join(linux_stage.ecr_repo_names)} {' '.join(windows_stage.ecr_repo_names)}",
                },
                role=cross_account_role,
            )
        )

        ci_stage = CiStage(
            self,
            f"{deploy_environment_type.value}-CiTests",
            pipeline_environment=pipeline_environment,
            deploy_environment=deploy_environment,
        )

        ci_stage.add_stage_to_pipeline(
            pipeline=pipeline,
            input=source.primary_output,
            role=cross_account_role,
            max_retry=MAX_TEST_RETRY,
            env={
                **codebuild_environment_variables,
                "PREVIOUS_REBUILDS": f"{linux_stage.need_rebuild} {linux_stage.need_rebuild}",
            },
        )
