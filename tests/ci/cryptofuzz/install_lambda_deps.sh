#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Install dependencies for CreateSSHKey Lambda
pip3 install --upgrade pip
pip3 install --target ./CreateSSHKey/ requests
pip3 install --target ./CreateSSHKey/ boto3
pip3 install --target ./CreateSSHKey/ cfnresponse
pip3 install --target ./CreateSSHKey/ cryptography
sed -ie 's/from botocore.vendored import requests/import requests/g' CreateSSHKey/cfnresponse/__init__.py

# Install dependencies for GitPullS3 Lambda
pip3 install --target ./GitPullS3/ cffi
pip3 install --target ./GitPullS3/ pygit2
pip3 install --target ./GitPullS3/ boto3

# Install dependencies for ReportFunction Lambda
pip3 install --target ./ReportFunction/ boto3
