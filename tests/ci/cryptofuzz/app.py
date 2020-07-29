#!/usr/bin/env python3

from aws_cdk import core
from util.util import EnvUtil

from cryptofuzz.webhook_stack import WebhookStack
from cryptofuzz.fuzzing_stack import FuzzingStack
from cryptofuzz.report_stack import ReportStack

# Initialize app
app = core.App()

# Fetch environment variables.
aws_account = EnvUtil.get("CDK_DEPLOY_ACCOUNT", "923900853817")
aws_region = EnvUtil.get("CDK_DEPLOY_REGION", "us-east-2")

# Create stacks
webhook_stack = WebhookStack(app, "WebhookStack")
FuzzingStack(app, "FuzzingStack",
             webhook_stack.vpc)
ReportStack(app, "ReportStack",
            webhook_stack.commit_secret)


app.synth()
