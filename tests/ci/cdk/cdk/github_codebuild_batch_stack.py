# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import typing
from util.util import EnvUtil

from aws_cdk import core, aws_codebuild as codebuild, aws_iam as iam, aws_ecr as ecr


class GitHubCodeBuildBatchStack(core.Stack):
    """Define a stack used to batch execute AWS-LC tests."""

    def __init__(self,
                 scope: core.Construct,
                 id: str,
                 build_spec_file: str,
                 **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Fetch environment variables.
        github_repo_owner = EnvUtil.get("GITHUB_REPO_OWNER", "awslabs")
        github_repo = EnvUtil.get("GITHUB_REPO", "aws-lc")

        # Define CodeBuild resource.
        git_hub_source = codebuild.Source.git_hub(
            owner=github_repo_owner,
            repo=github_repo,
            webhook=True,
            webhook_filters=[
                codebuild.FilterGroup.in_event_of(
                    codebuild.EventAction.PULL_REQUEST_CREATED,
                    codebuild.EventAction.PULL_REQUEST_UPDATED,
                    codebuild.EventAction.PULL_REQUEST_REOPENED)
            ],
            clone_depth=1)

        # Define a role.
        env = kwargs['env']
        codebuild_batch_policy = iam.PolicyDocument.from_json(
            {
                "Version": "2012-10-17",
                "Statement": [
                    {
                        "Effect": "Allow",
                        "Action": [
                            "codebuild:StartBuild",
                            "codebuild:StopBuild",
                            "codebuild:RetryBuild"
                        ],
                        "Resource": [
                            "arn:aws:codebuild:{}:{}:project/{}*".format(env['region'], env['account'], id),
                        ]
                    }
                ]
            }
        )
        inline_policies = {"codebuild_batch_policy": codebuild_batch_policy}
        role = iam.Role(scope=self,
                        id="{}-role".format(id),
                        assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
                        inline_policies=inline_policies,
                        managed_policies=[
                            iam.ManagedPolicy.from_aws_managed_policy_name("AmazonEC2ContainerRegistryReadOnly")
                        ])

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
            build_spec=codebuild.BuildSpec.from_source_filename(build_spec_file))

        # Add 'BuildBatchConfig' property, which is not supported in CDK.
        # CDK raw overrides: https://docs.aws.amazon.com/cdk/latest/guide/cfn_layer.html#cfn_layer_raw
        # https://docs.aws.amazon.com/AWSCloudFormation/latest/UserGuide/aws-resource-codebuild-project.html#aws-resource-codebuild-project-properties
        cfn_build = project.node.default_child
        cfn_build.add_override("Properties.BuildBatchConfig", {
            "ServiceRole": role.role_arn,
            "TimeoutInMins": 120
        })
