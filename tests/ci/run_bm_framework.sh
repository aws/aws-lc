#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# start ec2 instances
# spinwait until ec2 instances are no longer active (they'll shut themselves down after they finish)
# stop ec2 instances

# check correct s3 bucket results to see whether to pass/fail

# upload success failure messages to cloudwatch logs