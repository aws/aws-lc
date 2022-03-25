# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core, aws_codebuild as codebuild, aws_iam as iam, aws_ec2 as ec2, aws_efs as efs

from util.ecr_util import ecr_arn
from util.iam_policies import code_build_publish_metrics_in_json
from util.metadata import AWS_ACCOUNT, AWS_REGION, GITHUB_REPO_OWNER, GITHUB_REPO_NAME
from util.yml_loader import YmlLoader


class AwsLcGitHubAnalyticsStack(core.Stack):
    """Define a stack used to batch execute AWS-LC tests in GitHub."""

    def __init__(self,
                 scope: core.Construct,
                 id: str,
                 x86_ecr_repo_name: str,
                 arm_ecr_repo_name: str,
                 spec_file_path: str,
                 **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Define CodeBuild resource.
        git_hub_source = codebuild.Source.git_hub(
            owner=GITHUB_REPO_OWNER,
            repo=GITHUB_REPO_NAME,
            webhook=True,
            webhook_filters=[
                codebuild.FilterGroup.in_event_of(codebuild.EventAction.PUSH)
            ],
            webhook_triggers_batch_build=True)

        # Define a IAM role for this stack.
        metrics_policy = iam.PolicyDocument.from_json(code_build_publish_metrics_in_json())
        inline_policies = {"metric_policy": metrics_policy}
        role = iam.Role(scope=self,
                        id="{}-role".format(id),
                        assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
                        inline_policies=inline_policies)

        # Create build spec.
        placeholder_map = {"X86_ECR_REPO_PLACEHOLDER": ecr_arn(x86_ecr_repo_name),
                           "ARM_ECR_REPO_PLACEHOLDER": ecr_arn(arm_ecr_repo_name)}
        build_spec_content = YmlLoader.load(spec_file_path, placeholder_map)

        # Define CodeBuild.
        analytics = codebuild.Project(
            scope=self,
            id="AnalyticsCodeBuild",
            project_name=id,
            source=git_hub_source,
            role=role,
            timeout=core.Duration.minutes(120),
            environment=codebuild.BuildEnvironment(compute_type=codebuild.ComputeType.LARGE,
                                                   privileged=True,
                                                   build_image=codebuild.LinuxBuildImage.STANDARD_4_0),
            build_spec=codebuild.BuildSpec.from_object(build_spec_content))
        analytics.enable_batch_builds()
