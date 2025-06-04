# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

from aws_cdk import Stack, Duration, aws_ecr as ecr, aws_iam as iam
from constructs import Construct


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
