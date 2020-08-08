#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

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
github_code_bucket = EnvUtil.get("GITHUB_CODE_BUCKET", "github-code-bucket")
corpus_bucket = EnvUtil.get("CORPUS_BUCKET", "cryptofuzz-corpus-bucket")
fargate_cluster_name = EnvUtil.get("FARGATE_CLUSTER_NAME", "fargate-cryptofuzz-cluster")
ubuntu_x86 = EnvUtil.get("UBUNTU_X86", "aws-lc-cryptofuzz-ubuntu-19-10--x86--clang-9x-sanitizer")
fedora_x86 = EnvUtil.get("FEDORA_X86", "aws-lc-cryptofuzz-fedora-31--x86--clang-9x")
ubuntu_aarch = EnvUtil.get("UBUNTU_AARCH", "aws-lc-cryptofuzz-ubuntu-19-10--aarch--clang-9x-sanitizer")
interesting_input_bucket = EnvUtil.get("INTERESTING_INPUT_BUCKET", "cryptofuzz-interesting-input-bucket")
commit_secret_name = EnvUtil.get("COMMIT_SECRET_NAME", "CommitID")
repo_owner = EnvUtil.get("GITHUB_REPO_OWNER", "13agupta")
repo = EnvUtil.get("GITHUB_REPO", "aws-lc")
priv_key_secret_name = EnvUtil.get("PRIVATE_KEY_SECRET_NAME", "PrivateSSHKey")
pub_key_secret_name = EnvUtil.get("PUBLIC_KEY_SECRET_NAME", "PublicSSHKey")
report_bucket = EnvUtil.get("REPORT_BUCKET", "cryptofuzz-report-bucket")
gen_corpus_container_name = EnvUtil.get("GEN_CORPUS_CONTAINER_NAME", "gen_corpus_container")
corpus_volume = EnvUtil.get("CORPUS_VOLUME", "corpus_volume")
security_group_name = EnvUtil.get("SECURITY_GROUP_NAME", "security-group")

# Build environment to be passed into stacks
env = {
    'aws_account': aws_account,
    'aws_region': aws_region,
    'github_code_bucket': github_code_bucket,
    'corpus_bucket': corpus_bucket,
    'fargate_cluster_name': fargate_cluster_name,
    'ubuntu_x86': ubuntu_x86,
    'fedora_x86': fedora_x86,
    'ubuntu_aarch': ubuntu_aarch,
    'interesting_input_bucket': interesting_input_bucket,
    'commit_secret_name': commit_secret_name,
    'repo_owner': repo_owner,
    'repo': repo,
    'priv_key_secret_name': priv_key_secret_name,
    'pub_key_secret_name': pub_key_secret_name,
    'report_bucket': report_bucket,
    'gen_corpus_container_name': gen_corpus_container_name,
    'corpus_volume': corpus_volume,
    'security_group_name': security_group_name
}

# Create stacks
webhook_stack = WebhookStack(app, "WebhookStack",
                             env)
FuzzingStack(app, "FuzzingStack",
             webhook_stack.vpc,
             env)
ReportStack(app, "ReportStack",
            env)


app.synth()
