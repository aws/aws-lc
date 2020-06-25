# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core, aws_ecr as ecr, aws_iam as iam


class EcrStack(core.Stack):
    """Define a stack of ECR to store pre-built Docker Images."""

    def __init__(self, scope: core.Construct, id: str, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        ecr.Repository(scope=self, id=id, repository_name=id).grant_pull_push(
            iam.ServicePrincipal("codebuild.amazonaws.com"))
