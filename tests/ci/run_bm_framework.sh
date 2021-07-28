#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Please run from project root folder!
# You'll want to set the codebuild env variables set if running locally

# cleanup code
cleanup() {
  set +e
  # kill ec2 instances after we're done w/ them
  aws ec2 terminate-instances --instance-ids "${x86_id} ${arm_id} ${x86_nosha_id}" &>/dev/null

  # delete the various documents that we created
  for name in ${ssm_document_names};do
    aws ssm delete-document --name "${name}"
  done
}

# we wanna run the cleanup code on exit
trap cleanup EXIT

# print some information for reference
echo GitHub Commit Version: "${CODEBUILD_SOURCE_VERSION}"
AWS_ACCOUNT_ID=$(aws sts get-caller-identity --query Account --output text)
echo AWS Account ID: "${AWS_ACCOUNT_ID}"
echo GitHub Repo Link: "${CODEBUILD_SOURCE_REPO_URL}"

# get information for ec2 instances
vpc_id="$(aws ec2 describe-vpcs --filter Name=tag:Name,Values=aws-lc-bm-framework/aws-lc-bm-framework-ec2-vpc --query Vpcs[*].VpcId --output text)"
sg_id="$(aws ec2 describe-security-groups --filter Name=vpc-id,Values="${vpc_id}" --filter Name=group-name,Values=bm_framework_ec2_sg --query SecurityGroups[*].GroupId --output text)"
subnet_id="$(aws ec2 describe-subnets --filter Name=vpc-id,Values="${vpc_id}" --filter Name=state,Values=available --filter Name=tag:Name,Values=aws-lc-bm-framework/aws-lc-bm-framework-ec2-vpc/PrivateSubnet1 --query Subnets[*].SubnetId --output text)"

# use sed to replace some placeholder values inside the x86 and arm document
sed -e "s,{AWS_ACCOUNT_ID},${AWS_ACCOUNT_ID},g" \
  -e "s,{COMMIT_ID},${CODEBUILD_SOURCE_VERSION},g" \
  -e "s,{GITHUB_REPO},${CODEBUILD_SOURCE_REPO_URL},g" \
  -e "s,{OPENSSL_ia32cap},,g" \
  -e "s,{NOHW_TYPE},,g" \
  tests/ci/cdk/cdk/ssm/bm_framework_ssm_document.yaml \
  >tests/ci/cdk/cdk/ssm/bm_framework_hw_ssm_document.yaml

# use sed to replace some placeholder values inside the x86 nosha and noavx documents
sed -e "s,{AWS_ACCOUNT_ID},${AWS_ACCOUNT_ID},g" \
  -e "s,{COMMIT_ID},${CODEBUILD_SOURCE_VERSION},g" \
  -e "s,{GITHUB_REPO},${CODEBUILD_SOURCE_REPO_URL},g" \
  -e "s,{OPENSSL_ia32cap},:~0x10000000,g" \
  -e "s,{NOHW_TYPE},nosha,g" \
  tests/ci/cdk/cdk/ssm/bm_framework_ssm_document.yaml \
  >tests/ci/cdk/cdk/ssm/bm_framework_nosha_ssm_document.yaml

# create ec2 instances for x86 and arm
x86_id="$(aws ec2 run-instances --image-id ami-01773ce53581acf22 --count 1 \
  --instance-type c5.2xlarge --security-group-ids "${sg_id}" --subnet-id "${subnet_id}" \
  --block-device-mappings 'DeviceName="/dev/sda1",Ebs={DeleteOnTermination=True,VolumeSize=200}' \
  --tag-specifications 'ResourceType="instance",Tags=[{Key="aws-lc",Value="aws-lc-bm-framework-ec2-x86-instance"}]' \
  --iam-instance-profile Name=aws-lc-bm-framework-ec2-profile \
  --placement 'AvailabilityZone=us-west-2a' \
  --query Instances[*].InstanceId --output text)"

arm_id="$(aws ec2 run-instances --image-id ami-018e246d8c0f39ae5 --count 1 \
  --instance-type c6g.2xlarge --security-group-ids "${sg_id}" --subnet-id "${subnet_id}" \
  --block-device-mappings 'DeviceName="/dev/sda1",Ebs={DeleteOnTermination=True,VolumeSize=200}' \
  --tag-specifications 'ResourceType="instance",Tags=[{Key="aws-lc",Value="aws-lc-bm-framework-ec2-arm-instance"}]' \
  --iam-instance-profile Name=aws-lc-bm-framework-ec2-profile \
  --placement 'AvailabilityZone=us-west-2a' \
  --query Instances[*].InstanceId --output text)"

# create ec2 instances for x86 nosha & x86 noavx
x86_nosha_id="$(aws ec2 run-instances --image-id ami-01773ce53581acf22 --count 1 \
  --instance-type c5.2xlarge --security-group-ids "${sg_id}" --subnet-id "${subnet_id}" \
  --block-device-mappings 'DeviceName="/dev/sda1",Ebs={DeleteOnTermination=True,VolumeSize=200}' \
  --tag-specifications 'ResourceType="instance",Tags=[{Key="aws-lc",Value="aws-lc-bm-framework-ec2-x86-instance"}]' \
  --iam-instance-profile Name=aws-lc-bm-framework-ec2-profile \
  --placement 'AvailabilityZone=us-west-2a' \
  --query Instances[*].InstanceId --output text)"

# Give a few minutes for the ec2 instances to be ready
sleep 120

# Create, and run ssm command for arm & x86
ssm_doc_name=bm_framework_hw_ssm_document_"${CODEBUILD_SOURCE_VERSION}"
aws ssm create-document --content file://tests/ci/cdk/cdk/ssm/bm_framework_hw_ssm_document.yaml \
  --name "${ssm_doc_name}" \
  --document-type Command \
  --document-format YAML >/dev/null

ssm_command_id="$(aws ssm send-command --instance-ids "${x86_id}" "${arm_id}" \
  --document-name "${ssm_doc_name}" \
  --cloud-watch-output-config CloudWatchLogGroupName="aws-lc-bm-framework-cw-logs",CloudWatchOutputEnabled=true \
  --query Command.CommandId --output text)"

# Create and run ssm commands for x86 nosha & x86 noavx
nosha_ssm_doc_name=bm_framework_nosha_ssm_document_"${CODEBUILD_SOURCE_VERSION}"
aws ssm create-document --content file://tests/ci/cdk/cdk/ssm/bm_framework_nosha_ssm_document.yaml \
  --name "${nosha_ssm_doc_name}" \
  --document-type Command \
  --document-format YAML >/dev/null

nosha_ssm_command_id="$(aws ssm send-command --instance-ids "${x86_nosha_id}" \
  --document-name "${nosha_ssm_doc_name}" \
  --cloud-watch-output-config CloudWatchLogGroupName="aws-lc-bm-framework-cw-logs",CloudWatchOutputEnabled=true \
  --query Command.CommandId --output text)"

ssm_command_ids="${ssm_command_id} ${nosha_ssm_command_id}"
ssm_document_names="${ssm_doc_name} ${nosha_ssm_doc_name}"

# Give some time for the commands to run
for i in {1..30}; do
  echo "${i}: Continue to wait 3 min for SSM command ${id} to finish."
  sleep 180
  done=true
  success=true
  # for each command, check its status
  for id in ${ssm_command_ids}; do
    ssm_command_status="$(aws ssm list-commands --command-id "${id}" --query Commands[*].Status --output text)"
    ssm_target_count="$(aws ssm list-commands --command-id "${id}" --query Commands[*].TargetCount --output text)"
    ssm_completed_count="$(aws ssm list-commands --command-id "${id}" --query Commands[*].CompletedCount --output text)"
    if [[ ${ssm_command_status} == 'Success' && ${ssm_completed_count} == "${ssm_target_count}" ]]; then
      echo "SSM command ${id} finished successfully."
    elif [[ ${ssm_command_status} == 'Failed' && ${ssm_completed_count} == "${ssm_target_count}" ]]; then
      echo "SSM command ${id} failed."
      success=false
    else
      done=false
    fi
  done

  # if after the loop finish and done is still true, then we're done
  if [ "${done}" = true ]; then
    echo "All SSM commands have finished."

    # if success is still true here, then none of the commands failed
    if [ "${success}" != true ]; then
      echo "An SSM command failed!"
      exit 1
    fi
    break
  fi
done
