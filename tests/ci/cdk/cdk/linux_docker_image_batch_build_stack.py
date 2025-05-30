# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

from aws_cdk import (
    Duration,
    Stack,
    aws_codebuild as codebuild,
    aws_iam as iam,
    aws_ec2 as ec2,
    Environment,
)
from constructs import Construct

from util.metadata import (
    GITHUB_REPO_OWNER,
    GITHUB_REPO_NAME,
    GITHUB_SOURCE_VERSION,
    LINUX_AARCH_ECR_REPO,
    LINUX_X86_ECR_REPO,
)
from util.iam_policies import (
    code_build_batch_policy_in_json,
    ecr_power_user_policy_in_json,
)
from util.yml_loader import YmlLoader


class LinuxDockerImageBatchBuildStack(Stack):
    """Define a temporary stack used to batch build Linux Docker images."""

    def __init__(
        self,
        scope: Construct,
        id: str,
        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs
    ) -> None:
        super().__init__(scope, id, env=env, **kwargs)

        github_repo_owner = GITHUB_REPO_OWNER
        github_repo_name = GITHUB_REPO_NAME

        # Define CodeBuild resource.
        git_hub_source = codebuild.Source.git_hub(
            owner=github_repo_owner,
            repo=github_repo_name,
            webhook=False,
            branch_or_ref=GITHUB_SOURCE_VERSION,
            clone_depth=1,
        )

        # Define a role.
        code_build_batch_policy = iam.PolicyDocument.from_json(
            code_build_batch_policy_in_json([id], env)
        )
        ecr_repo_names = [LINUX_AARCH_ECR_REPO, LINUX_X86_ECR_REPO]
        ecr_power_user_policy = iam.PolicyDocument.from_json(
            ecr_power_user_policy_in_json(ecr_repo_names, env)
        )
        inline_policies = {
            "code_build_batch_policy": code_build_batch_policy,
            "ecr_power_user_policy": ecr_power_user_policy,
        }
        role = iam.Role(
            scope=self,
            id="{}-role".format(id),
            assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
            inline_policies=inline_policies,
        )

        # Create build spec.
        build_spec_content = YmlLoader.load(
            "./cdk/codebuild/linux_img_build_omnibus.yaml"
        )

        # Define environment variables.
        environment_variables = {
            "AWS_ACCOUNT_ID": codebuild.BuildEnvironmentVariable(value=env.account),
            "AWS_ECR_REPO_X86": codebuild.BuildEnvironmentVariable(
                value=LINUX_X86_ECR_REPO
            ),
            "AWS_ECR_REPO_AARCH": codebuild.BuildEnvironmentVariable(
                value=LINUX_AARCH_ECR_REPO
            ),
            "GITHUB_REPO_OWNER": codebuild.BuildEnvironmentVariable(
                value=GITHUB_REPO_OWNER
            ),
        }

        # Define VPC
        vpc = ec2.Vpc(
            self,
            id="{}-ec2-vpc".format(id),
            nat_gateways=1 # minimize the number of idle NAT gateways and thus elastic IPs
        )

        # Define CodeBuild project.
        project = codebuild.Project(
            scope=self,
            id=id,
            vpc=vpc,
            project_name=id,
            source=git_hub_source,
            environment=codebuild.BuildEnvironment(
                compute_type=codebuild.ComputeType.SMALL,
                privileged=False,
                build_image=codebuild.LinuxBuildImage.STANDARD_4_0,
            ),
            environment_variables=environment_variables,
            role=role,
            timeout=Duration.minutes(180),
            build_spec=codebuild.BuildSpec.from_object(build_spec_content),
        )
        project.enable_batch_builds()
