# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

import dataclasses
import typing
from aws_cdk import Environment, RemovalPolicy, Stack, Duration, aws_ecr as ecr, aws_iam as iam
from constructs import Construct
from util.metadata import AMAZONLINUX_ECR_REPO, CENTOS_ECR_REPO, FEDORA_ECR_REPO, UBUNTU_ECR_REPO


class EcrStack(Stack):
    """Define a stack of ECR to store pre-built Docker Images."""

    def __init__(self, scope: Construct, id: str, repo_name: str, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        repo = ecr.Repository(scope=self, id=id, repository_name=repo_name)
        repo.grant_pull_push(iam.ServicePrincipal("codebuild.amazonaws.com"))
        repo.grant_pull(iam.ArnPrincipal("arn:aws:iam::222961743098:role/scrutini-ecr"))
        repo.add_lifecycle_rule(
            description="Retain latest images",
            tag_pattern_list=["*_latest"],
            max_image_age=Duration.days(7300),
        )

        repo.add_lifecycle_rule(
            description="Expire images older than 1 month",
            max_image_age=Duration.days(30),
        )

        repo.add_lifecycle_rule(
            description="Remove untagged images after 1 day",
            tag_status=ecr.TagStatus.UNTAGGED,
            max_image_age=Duration.days(1),
        )


@dataclasses.dataclass
class EcrRepoDataClass:
    cdk_id: str
    ecr_name: str


class PrivateEcrStackV2(Stack):
    def __init__(self,
                 scope: Construct,
                 id: str,
                 env: typing.Union[Environment, typing.Dict[str, typing.Any]],
                 **kwargs) -> None:
        super().__init__(scope, id, env=env, **kwargs)

        ecr.CfnRepositoryCreationTemplate(self, "pull-through-cache-template",
                                          applied_for=["PULL_THROUGH_CACHE"],
                                          description="Used to create pull through cache repositories",
                                          prefix="ROOT",
                                          image_tag_mutability="MUTABLE",
                                          encryption_configuration={
                                                "encryptionType": "AES256"
                                          },
                                          lifecycle_policy="""
{
    "rules": [
        {
            "rulePriority": 1,
            "description": "Expire images older than 30 days",
            "selection": {
                "tagStatus": "untagged",
                "countType": "sinceImagePushed",
                "countUnit": "days",
                "countNumber": 30
            },
            "action": {
                "type": "expire"
            }
        }
    ]
}
""")
        
        quay_io_prefixes = ["centos"]
        for repo in quay_io_prefixes:
            ecr.CfnPullThroughCacheRule(self, f"quay-io-{repo}",
                                        ecr_repository_prefix=f"quay.io/{repo}",
                                        upstream_registry_url="quay.io",
                                        upstream_repository_prefix=repo)

        for x in [
            EcrRepoDataClass("aws-lc-ecr-ubuntu", UBUNTU_ECR_REPO),
            EcrRepoDataClass("aws-lc-ecr-amazonlinux", AMAZONLINUX_ECR_REPO),
            EcrRepoDataClass("aws-lc-ecr-fedora", FEDORA_ECR_REPO),
            EcrRepoDataClass("aws-lc-ecr-centos", CENTOS_ECR_REPO),
        ]:
            EcrPrivateRepo(self, x.cdk_id, repo_name=x.ecr_name)


class EcrPrivateRepo(Construct):
    """Define private ECR repository to store container images."""

    def __init__(self, scope: Construct, id: str, repo_name: str, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        self.repo = ecr.Repository(
            scope=self, id=id, repository_name=repo_name, removal_policy=RemovalPolicy.RETAIN)
        self.repo.add_lifecycle_rule(
            description="Remove untagged images after 1 day",
            tag_status=ecr.TagStatus.UNTAGGED,
            max_image_age=Duration.days(90),
        )
