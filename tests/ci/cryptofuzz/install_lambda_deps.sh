#!/bin/bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -exuo pipefail

# -e: Exit on any failure
# -x: Print the command before running
# -u: Any variable that is not set will cause an error if used
# -o pipefail: Makes sure to exit a pipeline with a non-zero error code if any command in the pipeline exists with a
#              non-zero error code.

# Installing dependencies locally for GitPullS3
pip2 install --upgrade pip setuptools wheel
pip2 install --target ./GitPullS3 pygit2
pip2 install --target ./GitPullS3 botocore==1.17.34
pip2 install --target ./GitPullS3 boto3==1.14.34
pip2 install --target ./GitPullS3 ipaddress

# Installing dependencies locally for CreateSSHKey
pip2 install --target ./CreateSSHKey botocore==1.17.34
pip2 install --target ./CreateSSHKey boto3==1.14.34
pip2 install --target ./CreateSSHKey asn1crypto
pip2 install --target ./CreateSSHKey cryptography

# Installing dependencies locally for ReportFunction
pip3 install --target ./ReportFunction botocore==1.17.34
pip3 install --target ./ReportFunction boto3==1.14.34

