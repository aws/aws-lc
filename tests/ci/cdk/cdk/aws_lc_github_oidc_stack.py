# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import itertools
import typing

from aws_cdk import (
    aws_ecr as ecr,
    aws_iam as iam,
    Stack,
    Environment,
)
from constructs import Construct

from util.metadata import (
    ECR_REPOS, GITHUB_REPO_OWNER, GITHUB_REPO_NAME, AWS_LC_METRIC_NS)
from util.iam_policies import (
    device_farm_access_policy_in_json
)

class AwsLcGitHubOidcStack(Stack):
    """Define a stack used to execute AWS-LC self-hosted GitHub Actions Runners."""

    def __init__(
        self,
        scope: Construct,
        id: str,
        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs
    ) -> None:
        super().__init__(scope, id, env=env, **kwargs)

        # Configures GitHub OIDC provider in IAM
        # https://docs.github.com/en/actions/how-tos/secure-your-work/security-harden-deployments/oidc-in-aws
        self.oidc_provider = iam.CfnOIDCProvider(self, "AwsLcGitHubOidcProvider",
                                                 client_id_list=[
                                                     "sts.amazonaws.com"],
                                                 url="https://token.actions.githubusercontent.com")

        oidc_role_name = "AwsLcGitHubActionsOidcRole" 
        # This role should only be granted necessary permissions to assume other roles
        self.minimal_oidc_role = iam.Role(self, id=oidc_role_name, role_name=oidc_role_name,
                                          assumed_by=iam.WebIdentityPrincipal(self.oidc_provider.attr_arn, {
                                              "StringEquals": {
                                                  "token.actions.githubusercontent.com:aud": "sts.amazonaws.com",
                                              },
                                              "StringLike": {
                                                  # Check the subject claim is from our repository VERY IMPORTANT!
                                                  # See https://docs.github.com/en/actions/reference/security/oidc#example-subject-claims
                                                  "token.actions.githubusercontent.com:sub": "repo:{}/{}:*".format(
                                                      GITHUB_REPO_OWNER, GITHUB_REPO_NAME
                                                  )
                                              },
                                          }))
        
        ecr_repos = [ecr.Repository.from_repository_name(self, x.replace('/', '-'), repository_name=x)
                     for x in ECR_REPOS]

        self.standard_github_actions_role = create_standard_github_actions_role(
            self, "AwsLcGitHubActionStandardRole", env, self.minimal_oidc_role, ecr_repos)
        self.standard_github_actions_role.grant_assume_role(
            self.minimal_oidc_role)

        self.device_farm_role = create_device_farm_role(
            self, "AwsLcGitHubActionDeviceFarmRole", env, self.minimal_oidc_role)
        self.device_farm_role.grant_assume_role(self.minimal_oidc_role)

        self.docker_image_build_role = create_docker_image_build_role(
            self, "AwsLcGitHubActionDockerImageBuildRole", env, self.minimal_oidc_role, ecr_repos)
        self.docker_image_build_role.grant_assume_role(
            self.minimal_oidc_role)


def create_device_farm_role(scope: Construct, id: str,
                            env: typing.Union[Environment, typing.Dict[str, typing.Any]],
                            principal: iam.IPrincipal) -> iam.Role:
    device_farm_policy = iam.PolicyDocument.from_json(
        device_farm_access_policy_in_json(env)
    )

    device_farm_role = iam.Role(scope, id, role_name=id,
                                assumed_by=iam.SessionTagsPrincipal(principal),
                                inline_policies={
                                    "device_farm_policy": device_farm_policy,
                                })

    return device_farm_role


def create_docker_image_build_role(scope: Construct, id: str,
                                   env: typing.Union[Environment, typing.Dict[str, typing.Any]],
                                   principal: iam.IPrincipal,
                                   repos: typing.List[ecr.IRepository]) -> iam.Role:

    pull_through_caches = [ecr.Repository.from_repository_name(
        scope, "quay-io", "quay.io/*")]

    role = iam.Role(scope, id, role_name=id,
                    assumed_by=iam.SessionTagsPrincipal(principal),
                    inline_policies={
                        "metrics_policy": iam.PolicyDocument(
                            statements=[
                                iam.PolicyStatement(
                                    effect=iam.Effect.ALLOW,
                                    actions=[
                                        "cloudwatch:PutMetricData"
                                    ],
                                    resources=["*"],
                                    conditions={
                                        "StringEquals": {
                                            "aws:RequestedRegion": [env.region],
                                            "cloudwatch:namespace": [AWS_LC_METRIC_NS],
                                        }
                                    }
                                ),
                            ]
                        ),
                        "ecr": iam.PolicyDocument(
                            statements=[
                                iam.PolicyStatement(
                                    effect=iam.Effect.ALLOW,
                                    actions=[
                                        "ecr:GetAuthorizationToken",
                                    ],
                                    resources=["*"],
                                ),
                                iam.PolicyStatement(
                                    effect=iam.Effect.ALLOW,
                                    actions=[
                                        "ecr:BatchGetImage",
                                        "ecr:BatchCheckLayerAvailability",
                                        "ecr:GetDownloadUrlForLayer",
                                    ],
                                    resources=[x for x in itertools.chain([
                                        x.repository_arn for x in repos
                                    ], [x.repository_arn for x in pull_through_caches])],
                                ),
                                iam.PolicyStatement(
                                    effect=iam.Effect.ALLOW,
                                    actions=[
                                        "ecr:CompleteLayerUpload",
                                        "ecr:InitiateLayerUpload",
                                        "ecr:PutImage",
                                        "ecr:UploadLayerPart",
                                    ],
                                    resources=[
                                        x.repository_arn for x in repos],
                                ),
                                iam.PolicyStatement(
                                    effect=iam.Effect.ALLOW,
                                    actions=[
                                        "ecr:BatchImportUpstreamImage",
                                    ],
                                    resources=[
                                        x.repository_arn for x in pull_through_caches]
                                ),
                            ],
                        ),
                    })

    return role


def create_standard_github_actions_role(scope: Construct, id: str,
                                        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
                                        principal: iam.IPrincipal,
                                        repos: typing.List[ecr.IRepository]) -> iam.Role:
    role = iam.Role(scope, id, role_name=id,
                    assumed_by=iam.SessionTagsPrincipal(principal),
                    inline_policies={
                        "metrics_policy": iam.PolicyDocument(
                            statements=[
                                iam.PolicyStatement(
                                    effect=iam.Effect.ALLOW,
                                    actions=[
                                        "cloudwatch:PutMetricData"
                                    ],
                                    resources=["*"],
                                    conditions={
                                        "StringEquals": {
                                            "aws:RequestedRegion": [env.region],
                                            "cloudwatch:namespace": [AWS_LC_METRIC_NS],
                                        }
                                    }
                                ),
                            ]
                        ),
                        "ecr": iam.PolicyDocument(
                            statements=[
                                iam.PolicyStatement(
                                    effect=iam.Effect.ALLOW,
                                    actions=[
                                        "ecr:GetAuthorizationToken",
                                    ],
                                    resources=["*"],
                                ),
                                iam.PolicyStatement(
                                    effect=iam.Effect.ALLOW,
                                    actions=[
                                        "ecr:BatchGetImage",
                                        "ecr:BatchCheckLayerAvailability",
                                        "ecr:GetDownloadUrlForLayer",
                                    ],
                                    resources=[x.repository_arn for x in repos],
                                ),
                            ],
                        ),
                    })

    return role
