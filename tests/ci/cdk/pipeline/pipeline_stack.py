# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

from aws_cdk import Stack, Environment, Duration
from aws_cdk import (
    aws_codebuild as codebuild,
    pipelines,
    aws_codestarconnections as codestarconnections,
    aws_codepipeline as codepipeline,
    aws_iam as iam,
    aws_events as events,
    aws_events_targets as targets,
    aws_cloudwatch as cloudwatch
)
from aws_cdk.pipelines import CodeBuildStep
from constructs import Construct

from pipeline.ci_stage import CiStage
from pipeline.deploy_util import DeployEnvironmentType
from pipeline.linux_docker_image_build_stage import LinuxDockerImageBuildStage
from pipeline.setup_stage import SetupStage
from pipeline.windows_docker_image_build_stage import WindowsDockerImageBuildStage
from util.metadata import (
    AWS_ACCOUNT,
    AWS_REGION,
    GITHUB_REPO_NAME,
    GITHUB_REPO_OWNER,
    GITHUB_SOURCE_VERSION, PIPELINE_ACCOUNT, PIPELINE_REGION,
)

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
            "CrossAccountCodeBuildRole",
            role_name="CrossAccountCodeBuildRole",
            assumed_by=iam.CompositePrincipal(
                iam.ServicePrincipal("codebuild.amazonaws.com"),
                iam.ServicePrincipal("codepipeline.amazonaws.com")
            ),
        )

        cross_account_role.add_to_policy(
            iam.PolicyStatement(
                effect=iam.Effect.ALLOW,
                resources=[
                    f'arn:aws:iam::{AWS_ACCOUNT}:role/CrossAccountCodeBuildRole'
                ],
                actions=["sts:AssumeRole"],
            )
        )

        cross_account_role.add_to_policy(
            iam.PolicyStatement(
                effect=iam.Effect.ALLOW,
                resources=['*'],
                actions=["codepipeline:GetPipelineExecution"],
            )
        )

        source = pipelines.CodePipelineSource.connection(
            f"{GITHUB_REPO_OWNER}/{GITHUB_REPO_NAME}",
            "ci-pipeline",
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
            restart_execution_on_update=True
        )

        # Bucket contains artifacts from old pipeline executions
        # These artifacts are kept for 60 days in case we need to do a rollback
        base_pipeline.artifact_bucket.add_lifecycle_rule(
            enabled=True,
            expiration=Duration.days(60),
        )

        pipeline = pipelines.CodePipeline(
            self,
            "CdkPipeline",
            code_pipeline=base_pipeline,
            # pipeline_name="AwsLcCiPipeline",
            synth=pipelines.ShellStep(
                "Synth",
                input=source,
                commands=[
                    "echo \"Environment variables:\"",
                    "env",
                    "npm install -g aws-cdk",
                    "cd tests/ci",
                    "python -m pip install -r requirements.txt",
                    "cd cdk",
                    "cdk synth"
                ],
                env={
                    "CDK_DEPLOY_ACCOUNT": AWS_ACCOUNT,
                    "CDK_DEPLOY_REGION": AWS_REGION,
                    "GITHUB_REPO_OWNER": GITHUB_REPO_OWNER,
                    "GITHUB_REPO_NAME": GITHUB_REPO_NAME,
                    "GITHUB_SOURCE_VERSION": GITHUB_SOURCE_VERSION,
                    "PIPELINE_ACCOUNT": PIPELINE_ACCOUNT,
                    "PIPELINE_REGION": PIPELINE_REGION,
                },
                primary_output_directory="tests/ci/cdk/cdk.out",
            ),
            self_mutation=True,
            code_build_defaults=pipelines.CodeBuildOptions(
                role_policy=[
                    iam.PolicyStatement(
                        effect=iam.Effect.ALLOW,
                        resources=["*"],
                        actions=["sts:AssumeRole"],
                        conditions={
                            "StringEquals": {
                                "iam:ResourceTag/aws-cdk:bootstrap-role": "lookup",
                            }
                        }
                    ),
                ],
            ),
        )
        
        deploy_environment = DeployEnvironmentType.PRE_PROD.value

        setup_stage = SetupStage(
            self,
            f"{deploy_environment}-Setup",
            env=Environment(account=PIPELINE_ACCOUNT, region=PIPELINE_REGION)
        )

        pipeline.add_stage(setup_stage)

        docker_build_wave = pipeline.add_wave(f"{deploy_environment}-DockerImageBuild")

        linux_stage = LinuxDockerImageBuildStage(
            self,
            f"{deploy_environment}-LinuxDockerImageBuild",
            env=Environment(account=PIPELINE_ACCOUNT, region=PIPELINE_REGION)
        )

        linux_stage.add_stage_to_wave(
            wave=docker_build_wave,
            input=source.primary_output,
            role=cross_account_role,
            deploy_environment=deploy_environment,
            additional_stacks=setup_stage.stacks,
            env={
                "PIPELINE_EXECUTION_ID": "#{codepipeline.PipelineExecutionId}",
                "DEPLOY_ACCOUNT": AWS_ACCOUNT,
                "DEPLOY_REGION": AWS_REGION
            },
        )

        windows_stage = WindowsDockerImageBuildStage(
            self,
            f"{deploy_environment}-WindowsDockerImageBuild",
            env=Environment(account=PIPELINE_ACCOUNT, region=PIPELINE_REGION)
        )

        windows_stage.add_stage_to_wave(
            wave=docker_build_wave,
            input=source.primary_output,
            role=cross_account_role,
            deploy_environment=deploy_environment,
            additional_stacks=setup_stage.stacks,
            env={
                "PIPELINE_EXECUTION_ID": "#{codepipeline.PipelineExecutionId}",
                "DEPLOY_ACCOUNT": AWS_ACCOUNT,
                "DEPLOY_REGION": AWS_REGION
            },
        )

        docker_build_wave.add_post(
            CodeBuildStep(
                f"{deploy_environment}-CompleteDockerBuild",
                input=source,
                commands=[
                    "cd tests/ci/cdk/pipeline/scripts",
                    "chmod +x docker_image_cleanup.sh",
                    "./docker_image_cleanup.sh",
                ],
                env={
                    "PIPELINE_EXECUTION_ID": "#{codepipeline.PipelineExecutionId}",
                    "DEPLOY_ACCOUNT": AWS_ACCOUNT,
                    "DEPLOY_REGION": AWS_REGION
                },
                role=cross_account_role,
            )
        )

        ci_stage = CiStage(
            self,
            f"{deploy_environment}-CiTests",
            env=Environment(account=PIPELINE_ACCOUNT, region=PIPELINE_REGION)
        )

        ci_stage.add_stage_to_pipeline(
            pipeline=pipeline,
            input=source.primary_output,
            role=cross_account_role,
            deploy_environment=deploy_environment,
            env={
                "PIPELINE_EXECUTION_ID": "#{codepipeline.PipelineExecutionId}",
                "DEPLOY_ACCOUNT": AWS_ACCOUNT,
                "DEPLOY_REGION": AWS_REGION,
                "PREVIOUS_REBUILDS": f'{linux_stage.need_rebuild} {linux_stage.need_rebuild}'
            },
        )

        pipeline.build_pipeline()

        # Schedule pipeline to run every Tuesday 15:00 UTC or 7:00 PST
        events.Rule(
            self, "WeeklyCodePipelineRun",
            schedule=events.Schedule.cron(
                minute="0",
                hour="15",
                # weekday="TUE", #TODO: Uncomment this line. It's running everyday now to make sure I didn't break anything
            ),
            targets=[
                targets.CodePipeline(
                    pipeline=base_pipeline
                )
            ]
        )

        


