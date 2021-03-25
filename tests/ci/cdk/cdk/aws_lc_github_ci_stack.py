# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core, aws_codebuild as codebuild, aws_iam as iam
from util.iam_policies import code_build_batch_policy_in_json, ecr_pull_only_policy_in_json
from util.metadata import AWS_ACCOUNT, AWS_REGION, GITHUB_REPO_OWNER, GITHUB_REPO_NAME
from util.yml_loader import YmlLoader


class AwsLcGitHubCIStack(core.Stack):
    """Define a stack used to batch execute AWS-LC tests in GitHub."""

    def __init__(self,
                 scope: core.Construct,
                 id: str,
                 ecr_repo_name: str,
                 spec_file_path: str,
                 **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Define CodeBuild resource.
        git_hub_source = codebuild.Source.git_hub(
            owner=GITHUB_REPO_OWNER,
            repo=GITHUB_REPO_NAME,
            webhook=True,
            webhook_filters=[
                codebuild.FilterGroup.in_event_of(
                    codebuild.EventAction.PULL_REQUEST_CREATED,
                    codebuild.EventAction.PULL_REQUEST_UPDATED,
                    codebuild.EventAction.PULL_REQUEST_REOPENED)
            ],
            clone_depth=1)

        # Define a IAM role for this stack.
        code_build_batch_policy = iam.PolicyDocument.from_json(
            code_build_batch_policy_in_json([id])
        )
        ecr_pull_only_policy = iam.PolicyDocument.from_json(
            ecr_pull_only_policy_in_json(ecr_repo_name)
        )
        inline_policies = {"code_build_batch_policy": code_build_batch_policy,
                           "ecr_pull_only_policy": ecr_pull_only_policy}
        role = iam.Role(scope=self,
                        id="{}-role".format(id),
                        assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
                        inline_policies=inline_policies)

        # Create build spec.
        ecr_repo_full_name = "{}.dkr.ecr.{}.amazonaws.com/{}".format(AWS_ACCOUNT, AWS_REGION, ecr_repo_name)
        placeholder_map = {"AWS_ACCOUNT_ID_PLACEHOLDER": AWS_ACCOUNT, "AWS_REGION_PLACEHOLDER": AWS_REGION,
                           "ECR_REPO_PLACEHOLDER": ecr_repo_full_name}
        build_spec_content = YmlLoader.load(spec_file_path, placeholder_map)

        # Define CodeBuild.
        project = codebuild.Project(
            scope=self,
            id=id,
            project_name=id,
            source=git_hub_source,
            role=role,
            timeout=core.Duration.minutes(120),
            environment=codebuild.BuildEnvironment(compute_type=codebuild.ComputeType.SMALL,
                                                   privileged=False,
                                                   build_image=codebuild.LinuxBuildImage.STANDARD_4_0),
            build_spec=codebuild.BuildSpec.from_object(build_spec_content))

        # TODO: add build type BUILD_BATCH when CFN finishes the feature release. See CryptoAlg-575.

        # Add 'BuildBatchConfig' property, which is not supported in CDK.
        # CDK raw overrides: https://docs.aws.amazon.com/cdk/latest/guide/cfn_layer.html#cfn_layer_raw
        # https://docs.aws.amazon.com/AWSCloudFormation/latest/UserGuide/aws-resource-codebuild-project.html#aws-resource-codebuild-project-properties
        cfn_build = project.node.default_child
        cfn_build.add_override("Properties.BuildBatchConfig", {
            "ServiceRole": role.role_arn,
            "TimeoutInMins": 120
        })
