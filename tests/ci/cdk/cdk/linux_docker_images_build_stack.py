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
        github_repo_owner = EnvUtil.get("GITHUB_REPO_OWNER", "awslabs")
        github_repo = EnvUtil.get("GITHUB_REPO", "aws-lc")

        # Define CodeBuild resource.
        git_hub_source = codebuild.Source.git_hub(
            owner=github_repo_owner,
            repo=github_repo,
            webhook=True,
            clone_depth=1)

        # Define a role.
        role = iam.Role(scope=self,
                        id="{}-role".format(id),
                        assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
                        managed_policies=[
                            iam.ManagedPolicy.from_aws_managed_policy_name("AmazonEC2ContainerRegistryPowerUser")
                        ])

        # Define CodeBuild project.
        codebuild.Project(
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
