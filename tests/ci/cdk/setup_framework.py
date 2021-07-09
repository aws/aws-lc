#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core
from util.metadata import AWS_ACCOUNT, AWS_REGION
from cdk.cloudwatch_logs_stack import LogsStack

# Initialize app.
app = core.App()

# Initialize env.
env = core.Environment(account=AWS_ACCOUNT, region=AWS_REGION)

# Create log group for CloudWatch Logs
bm_log_group = LogsStack(app, "bm-framework-logs", "bm-framework-logs")

app.synth()