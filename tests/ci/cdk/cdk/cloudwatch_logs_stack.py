# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core, aws_logs as logs, aws_iam as iam


class LogsStack(core.Stack):
    """Define a stack of ECR to store pre-built Docker Images."""

    def __init__(self, scope: core.Construct, id: str, group_name: str, **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        logs.LogGroup(scope=self, id=id, log_group_name=group_name)
