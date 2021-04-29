# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core, aws_codebuild as codebuild, aws_iam as iam

from util.metadata import AWS_ACCOUNT, GITHUB_REPO_OWNER, GITHUB_REPO_NAME, GITHUB_SOURCE_VERSION, LINUX_AARCH_ECR_REPO, \
    LINUX_X86_ECR_REPO, EXTERNAL_CREDENTIAL_SECRET_ARN
from util.iam_policies import code_build_batch_policy_in_json, ecr_power_user_policy_in_json, \
    aws_secrets_manager_get_secret_policy_in_json
from util.yml_loader import YmlLoader


class LinuxDockerImageBatchBuildStack(core.Stack):
    """Define a temporary stack used to batch build Linux Docker images. After build, this stack will be destroyed."""

    def __init__(self, scope: core.Construct, id: str, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Define CodeBuild resource.
        git_hub_source = codebuild.Source.git_hub(
            owner=GITHUB_REPO_OWNER,
            repo=GITHUB_REPO_NAME,
            branch_or_ref=GITHUB_SOURCE_VERSION,
            clone_depth=1)

        # Define a role.
        code_build_batch_policy = iam.PolicyDocument.from_json(code_build_batch_policy_in_json([id]))
        ecr_repo_names = [LINUX_AARCH_ECR_REPO, LINUX_X86_ECR_REPO]
        ecr_power_user_policy = iam.PolicyDocument.from_json(ecr_power_user_policy_in_json(ecr_repo_names))
        inline_policies = {"code_build_batch_policy": code_build_batch_policy,
                           "ecr_power_user_policy": ecr_power_user_policy}
        # GitHub access token is only needed during CI setup.
        # The token is used to pull Docker images hosted in 'docker.pkg.github.com'.
        if EXTERNAL_CREDENTIAL_SECRET_ARN:
            secrets_manager_get_secret_policy = iam.PolicyDocument.from_json(
                aws_secrets_manager_get_secret_policy_in_json(EXTERNAL_CREDENTIAL_SECRET_ARN))
            inline_policies["secrets_manager_get_secret_policy"] = secrets_manager_get_secret_policy
        role = iam.Role(scope=self,
                        id="{}-role".format(id),
                        assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
                        inline_policies=inline_policies)

        # Create build spec.
        build_spec_content = YmlLoader.load("./cdk/codebuild/linux_img_build_omnibus.yaml")

        # Define environment variables.
        environment_variables = {
            "AWS_ACCOUNT_ID": codebuild.BuildEnvironmentVariable(value=AWS_ACCOUNT),
            "AWS_ECR_REPO_X86": codebuild.BuildEnvironmentVariable(value=LINUX_X86_ECR_REPO),
            "AWS_ECR_REPO_AARCH": codebuild.BuildEnvironmentVariable(value=LINUX_AARCH_ECR_REPO),
            "GITHUB_REPO_OWNER": codebuild.BuildEnvironmentVariable(value=GITHUB_REPO_OWNER),
        }
        if EXTERNAL_CREDENTIAL_SECRET_ARN:
            # See secrets-manager https://docs.aws.amazon.com/codebuild/latest/userguide/build-spec-ref.html
            github_access_token = "{}:GITHUB_PERSONAL_ACCESS_TOKEN".format(EXTERNAL_CREDENTIAL_SECRET_ARN)
            environment_variables["GITHUB_READ_PKG_ACCESS_TOKEN"] = codebuild.BuildEnvironmentVariable(
                value=github_access_token,
                type=codebuild.BuildEnvironmentVariableType.SECRETS_MANAGER)

        # Define CodeBuild project.
        project = codebuild.Project(
            scope=self,
            id=id,
            project_name=id,
            source=git_hub_source,
            environment=codebuild.BuildEnvironment(
                compute_type=codebuild.ComputeType.SMALL,
                privileged=False,
                build_image=codebuild.LinuxBuildImage.STANDARD_4_0),
            environment_variables=environment_variables,
            role=role,
            timeout=core.Duration.minutes(120),
            build_spec=codebuild.BuildSpec.from_object(build_spec_content))

        # Add 'BuildBatchConfig' property, which is not supported in CDK.
        # CDK raw overrides: https://docs.aws.amazon.com/cdk/latest/guide/cfn_layer.html#cfn_layer_raw
        # https://docs.aws.amazon.com/AWSCloudFormation/latest/UserGuide/aws-resource-codebuild-project.html#aws-resource-codebuild-project-properties
        cfn_build = project.node.default_child
        cfn_build.add_override("Properties.BuildBatchConfig", {
            "ServiceRole": role.role_arn,
            "TimeoutInMins": 120
        })
