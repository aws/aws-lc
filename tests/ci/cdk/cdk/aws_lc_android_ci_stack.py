# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

from aws_cdk import (
    Duration,
    Stack,
    aws_codebuild as codebuild,
    aws_iam as iam,
    Environment,
)
from constructs import Construct

from cdk.aws_lc_base_ci_stack import AwsLcBaseCiStack
from cdk.components import PruneStaleGitHubBuilds
from util.iam_policies import (
    code_build_batch_policy_in_json,
    device_farm_access_policy_in_json,
)
from util.metadata import (
    GITHUB_REPO_OWNER,
    GITHUB_REPO_NAME,
    GITHUB_PUSH_CI_BRANCH_TARGETS,
    PRE_PROD_ACCOUNT,
    STAGING_GITHUB_REPO_OWNER,
    STAGING_GITHUB_REPO_NAME,
)
from util.build_spec_loader import BuildSpecLoader


class AwsLcAndroidCIStack(AwsLcBaseCiStack):
    """Define a stack used to batch execute AWS-LC tests in GitHub."""

    # The Device Farm resource used to in this CI spec, must be manually created.
    # TODO: Automate Device Farm creation with cdk script.

    def __init__(
        self,
        scope: Construct,
        id: str,
        spec_file_path: str,
        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs
    ) -> None:
        super().__init__(scope, id, env=env, timeout=180, **kwargs)

        # Define a IAM role for this stack.
        code_build_batch_policy = iam.PolicyDocument.from_json(
            code_build_batch_policy_in_json([id], env)
        )
        device_farm_policy = iam.PolicyDocument.from_json(
            device_farm_access_policy_in_json(env)
        )
        inline_policies = {
            "code_build_batch_policy": code_build_batch_policy,
            "device_farm_policy": device_farm_policy,
        }
        role = iam.Role(
            scope=self,
            id="{}-role".format(id),
            assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
            inline_policies=inline_policies,
        )

        # Define CodeBuild.
        project = codebuild.Project(
            scope=self,
            id=id,
            project_name=id,
            source=self.git_hub_source,
            role=role,
            timeout=Duration.minutes(self.timeout),
            environment=codebuild.BuildEnvironment(
                compute_type=codebuild.ComputeType.SMALL,
                privileged=False,
                build_image=codebuild.LinuxBuildImage.STANDARD_4_0,
            ),
            build_spec=BuildSpecLoader.load(spec_file_path, env),
        )
        project.enable_batch_builds()

        PruneStaleGitHubBuilds(
            scope=self,
            id="PruneStaleGitHubBuilds",
            project=project,
            ec2_permissions=False,
            env=env,
        )
