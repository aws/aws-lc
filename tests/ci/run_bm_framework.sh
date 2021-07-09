#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Setup
pip3 install --upgrade pip
sudo apt install nodejs npm

cd cdk
pip3 install -r requirements.txt
python3 setup_framework.py

#cdk deploy
# check if cloudwatch logs already exists

# if not create it

# check if s3 buckets already exist
# if not create them

# start ec2 instances
# spinwait until ec2 instances are no longer active (they'll shut themselves down after they finish)
# terminate ec2 instances

# check correct s3 bucket results to see whether to pass/fail