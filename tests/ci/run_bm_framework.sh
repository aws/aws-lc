#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# define cleanup script to delete created assets in case something fails or breaks
function cleanup {
  # Delete ssm document once you're finished with it
  aws ssm delete-document --name "${ssm_doc_name}"

  # kill ec2 instances after we're done w/ them
  aws ec2 terminate-instances --instance-ids "${x86_ubuntu2004_id}"
}

# on an error, we want to delete the document and kill the ec2 instance
trap cleanup ERR

echo GitHub Commit Version: "${CODEBUILD_SOURCE_VERSION}"

# get information for ec2 instances
vpc_id="$(aws ec2 describe-vpcs --filter Name=tag:Name,Values=aws-lc-bm-framework/aws-lc-bm-framework-ec2-vpc --query Vpcs[*].VpcId --output text)"
sg_id="$(aws ec2 describe-security-groups --filter Name=vpc-id,Values="${vpc_id}" --filter Name=group-name,Values=bm_framework_ec2_sg  --query SecurityGroups[*].GroupId --output text)"
subnet_id="$(aws ec2 describe-subnets --filter Name=vpc-id,Values="${vpc_id}" --filter Name=state,Values=available --filter Name=tag:Name,Values=aws-lc-bm-framework/aws-lc-bm-framework-ec2-vpc/PrivateSubnet1 --query Subnets[*].SubnetId --output text)"

# create ec2 instances
# ubuntu 20.04
x86_ubuntu2004_id="$(aws ec2 run-instances --image-id ami-01773ce53581acf22 --count 1 \
  --instance-type c5.2xlarge --security-group-ids "${sg_id}" --subnet-id "${subnet_id}" \
  --block-device-mappings 'DeviceName="/dev/sda1",Ebs={DeleteOnTermination=True,VolumeSize=200}' \
  --tag-specifications 'ResourceType="instance",Tags=[{Key="aws-lc",Value="aws-lc-bm-framework-ec2-x86-instance"}]' \
  --iam-instance-profile Name=aws-lc-bm-framework-ec2-profile \
  --placement 'AvailabilityZone=us-west-2a' \
  --query Instances[*].InstanceId --output text)"

# Give 5 minutes for the ec2 to be ready
sleep 120

# Create, and run ssm command
# two commands for running locally vs on codebuild
ssm_doc_name=bm_framework_ec2_benchmark_ssm_document_"${CODEBUILD_SOURCE_VERSION}"
#aws ssm create-document --content file://cdk/cdk/ssm/bm_framework_ec2_x86_benchmark_ssm_document.yaml \
aws ssm create-document --content file://tests/ci/cdk/cdk/ssm/bm_framework_ec2_x86_benchmark_ssm_document.yaml \
    --name "${ssm_doc_name}" \
    --document-type Command \
    --document-format YAML > /dev/null

ssm_command_id="$(aws ssm send-command --instance-ids "${x86_ubuntu2004_id}" \
    --document-name "${ssm_doc_name}" \
    --cloud-watch-output-config CloudWatchLogGroupName="aws-lc-bm-framework-cw-logs",CloudWatchOutputEnabled=true \
    --query Command.CommandId --output text)"

# Give some time for the command to run
for i in {1..30}; do
  ssm_command_status="$(aws ssm list-commands --command-id "${ssm_command_id}" --query Commands[*].Status --output text)"
  if [[ ${ssm_command_status} == 'Success' ]]; then
    echo "SSM command ${ssm_command_id} finished successfully."
    break;
  elif [[ ${ssm_command_status} == 'Failed' ]]; then
    echo "SSM command ${ssm_command_id} failed."
    break;
  else
    echo "${i}: Continue to wait 5 min for benchmarks to finish."
    sleep 300
  fi
done

# Delete ssm document once you're finished with it
aws ssm delete-document --name "${ssm_doc_name}"

# kill ec2 instances after we're done w/ them
aws ec2 terminate-instances --instance-ids "${x86_ubuntu2004_id}"
