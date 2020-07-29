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
virtualenv GitPullS3/v-env
source GitPullS3/v-env/bin/activate
pip install pygit2
pip install boto3
pip install ipaddress
deactivate

# Installing dependencies locally for CreateSSHKey
virtualenv CreateSSHKey/v-env
source CreateSSHKey/v-env/bin/activate
pip install botocore==1.17.31
pip install boto3
pip install cryptography
deactivate

# Installing dependencies locally for ReportFunction
virtualenv ReportFunction/v-env
source ReportFunction/v-env/bin/activate
pip install botocore==1.17.31
pip install boto3

