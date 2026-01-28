# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing
from enum import Enum

from aws_cdk import Stack, Environment, Duration
from aws_cdk import (
    pipelines,
    aws_codestarconnections as codestarconnections,
    aws_codepipeline as codepipeline,
    aws_codepipeline_actions as codepipeline_actions,
    aws_iam as iam,
    aws_codebuild as codebuild,
)
from aws_cdk.pipelines import ManualApprovalStep
from constructs import Construct

from pipeline.ci_stage import CiStage
from pipeline.ecr_stage import EcrStage
from pipeline.github_actions_stage import GitHubActionsStage
from pipeline.setup_stage import SetupStage
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

        source_output = codepipeline.Artifact()

        source_action = codepipeline_actions.CodeStarConnectionsSourceAction(
            connection_arn=gh_connection.attr_connection_arn,
            owner=GITHUB_REPO_OWNER,
            repo=GITHUB_REPO_NAME,
            branch=GITHUB_SOURCE_VERSION,
            action_name='GitHub_Source',
            output=source_output,
            code_build_clone_output=True,
            trigger_on_push=True
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
            triggers=[codepipeline.TriggerProps(
                provider_type=codepipeline.ProviderType.CODE_STAR_SOURCE_CONNECTION,
                git_configuration=codepipeline.GitConfiguration(
                    source_action=source_action,
                    push_filter=[codepipeline.GitPushFilter(
                        branches_includes=[GITHUB_SOURCE_VERSION],
                        file_paths_includes=[
                            'tests/ci/cdk/**',
                            'tests/ci/setup.py',
                            'tests/ci/requirements.txt',
                            'tests/ci/lambda/**'])],
                ),
            )]
        )

        base_pipeline.add_stage(stage_name='Source', actions=[source_action])

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

        source_file_set = pipelines.CodePipelineFileSet.from_artifact(
            source_output)

        pipeline = pipelines.CodePipeline(
            self,
            "CdkPipeline",
            code_pipeline=base_pipeline,
            # pipeline_name="AwsLcCiPipeline",
            synth=pipelines.ShellStep(
                "Synth",
                input=source_file_set,
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
                source=source_file_set,
                cross_account_role=cross_account_role,
            )
        else:
            self.deploy_to_environment(
                DeployEnvironmentType.PRE_PROD,
                pipeline=pipeline,
                source=source_file_set,
                cross_account_role=cross_account_role,
            )

            self.deploy_to_environment(
                DeployEnvironmentType.PROD,
                pipeline=pipeline,
                source=source_file_set,
                cross_account_role=cross_account_role,
            )

        pipeline.build_pipeline()

    def deploy_to_environment(
        self,
        deploy_environment_type: DeployEnvironmentType,
        pipeline: pipelines.CodePipeline,
        source: pipelines.CodePipelineFileSet,
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
            deploy_environment = Environment(
                account=PROD_ACCOUNT, region=PROD_REGION)

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

        ecr_stage = EcrStage(self, f"{deploy_environment_type.value}-EcrRepositories",
                             pipeline_environment=pipeline_environment,
                             deploy_environment=deploy_environment)
        pipeline.add_stage(ecr_stage)

        gh_actions_stage = GitHubActionsStage(self, f"{deploy_environment_type.value}-GithubActions",
                                              pipeline_environment=pipeline_environment,
                                              deploy_environment=deploy_environment)
        pipeline.add_stage(gh_actions_stage)

        ci_stage = CiStage(
            self,
            f"{deploy_environment_type.value}-CiTests",
            pipeline_environment=pipeline_environment,
            deploy_environment=deploy_environment,
        )

        ci_stage.add_stage_to_pipeline(
            pipeline=pipeline,
            input=source,
            role=cross_account_role,
            max_retry=MAX_TEST_RETRY,
            env={
                **codebuild_environment_variables,
            },
        )
