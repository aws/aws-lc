# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from util.util import EnvUtil

from aws_cdk import core, aws_codebuild as codebuild, aws_iam as iam


class LinuxDockerImagesBuildStack(core.Stack):
    """Define a stack used to build Linux Docker images."""

    def __init__(self, scope: core.Construct, id: str, ecr_repo: str,
                 build_spec_file: str, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Fetch environment variables.
        ecr_linux_aarch_repo_name = EnvUtil.get("ECR_LINUX_AARCH_REPO_NAME", "aws-lc-test-docker-images-linux-aarch")
        ecr_linux_x86_repo_name = EnvUtil.get("ECR_LINUX_X86_REPO_NAME", "aws-lc-test-docker-images-linux-x86")
        github_repo_owner = EnvUtil.get("GITHUB_REPO_OWNER", "awslabs")
        github_repo = EnvUtil.get("GITHUB_REPO", "aws-lc")

        # Define CodeBuild resource.
        git_hub_source = codebuild.Source.git_hub(
            owner=github_repo_owner,
            repo=github_repo,
            webhook=True,
            clone_depth=1)

        # Define a role.
        ecr_power_user_policy = iam.PolicyDocument.from_json(
            {
                "Version": "2012-10-17",
                "Statement": [
                    {
                        "Effect": "Allow",
                        "Action": [
                            "ecr:GetAuthorizationToken",
                            "ecr:BatchCheckLayerAvailability",
                            "ecr:GetDownloadUrlForLayer",
                            "ecr:GetRepositoryPolicy",
                            "ecr:DescribeRepositories",
                            "ecr:ListImages",
                            "ecr:DescribeImages",
                            "ecr:BatchGetImage",
                            "ecr:GetLifecyclePolicy",
                            "ecr:GetLifecyclePolicyPreview",
                            "ecr:ListTagsForResource",
                            "ecr:DescribeImageScanFindings",
                            "ecr:InitiateLayerUpload",
                            "ecr:UploadLayerPart",
                            "ecr:CompleteLayerUpload",
                            "ecr:PutImage"
                        ],
                        "Resource": [
                            "arn:aws:ecr:::{}/*".format(ecr_linux_aarch_repo_name),
                            "arn:aws:ecr:::{}/*".format(ecr_linux_x86_repo_name)
                        ]
                    }
                ]
            }
        )
        inline_policies = {"ecr_power_user_policy": ecr_power_user_policy}
        role = iam.Role(scope=self,
                        id="{}-role".format(id),
                        assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
                        inline_policies=inline_policies)

        # Define CodeBuild project.
        project = codebuild.Project(
            scope=self,
            id=id,
            project_name=ecr_repo,
            source=git_hub_source,
            environment=codebuild.BuildEnvironment(
                compute_type=codebuild.ComputeType.LARGE,
                privileged=True,
                build_image=codebuild.LinuxBuildImage.STANDARD_2_0),
            environment_variables={
                "AWS_ACCOUNT_ID": codebuild.BuildEnvironmentVariable(value=kwargs['env']['account']),
                "AWS_ECR_REPO": codebuild.BuildEnvironmentVariable(value=ecr_repo)
            },
            role=role,
            build_spec=codebuild.BuildSpec.from_source_filename(
                build_spec_file))
