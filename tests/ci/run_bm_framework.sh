#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

echo GitHub Commit Version: "${CODEBUILD_SOURCE_VERSION}"

# get information for ec2 instances
vpc_id="$(aws ec2 describe-vpcs --filter Name=tag:Name,Values=aws-lc-bm-framework/aws-lc-bm-framework-ec2-vpc --query Vpcs[*].VpcId --output text)"
sg_id="$(aws ec2 describe-security-groups --filter Name=vpc-id,Values="${vpc_id}" --filter Name=group-name,Values=bm_framework_ec2_sg  --query SecurityGroups[*].GroupId --output text)"
subnet_id="$(aws ec2 describe-subnets --filter Name=vpc-id,Values="${vpc_id}" --filter Name=state,Values=available --filter Name=tag:Name,Values=aws-lc-bm-framework/aws-lc-bm-framework-ec2-vpc/PrivateSubnet1 --query Subnets[*].SubnetId --output text)"

# create ec2 instances
# ubuntu 20.04
x86_ubuntu2004="$(aws ec2 run-instances --image-id ami-01773ce53581acf22 --count 1 \
  --instance-type c5.metal --security-group-ids "${sg_id}" --subnet-id "${subnet_id}" \
  --block-device-mappings 'DeviceName="/dev/sda1",Ebs={DeleteOnTermination=True,VolumeSize=200}' \
  --tag-specifications 'ResourceType="instance",Tags=[{Key="aws-lc",Value="aws-lc-bm-framework-ec2-x86-instance"}]' \
  --query Instances[*].InstanceId --output text)"

#temp
sleep 300

# kill ec2 instances after we're done w/ them
aws ec2 terminate-instances --instance-ids "${x86_ubuntu2004}"
