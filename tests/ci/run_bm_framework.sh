#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

# Please run from project root folder!
# You'll want to set the codebuild env variables set if running locally
source tests/ci/common_ssm_setup.sh

# cleanup code
cleanup() {
  set +e
  # kill ec2 instances after we're done w/ them
  for id in ${instance_ids};do
    aws ec2 terminate-instances --instance-ids "${id}"
  done

  # delete the various documents that we created
  for name in ${ssm_document_names};do
    aws ssm delete-document --name "${name}"
  done
}

# we wanna run the cleanup code on exit
trap cleanup EXIT

# print some information for reference
echo GitHub PR Number: "${CODEBUILD_WEBHOOK_TRIGGER}"
echo GitHub Commit Version: "${CODEBUILD_SOURCE_VERSION}"
AWS_ACCOUNT_ID=$(aws sts get-caller-identity --query Account --output text)
echo AWS Account ID: "${AWS_ACCOUNT_ID}"
echo GitHub Repo Link: "${CODEBUILD_SOURCE_REPO_URL}"

# get information for ec2 instances
vpc_id="$(aws ec2 describe-vpcs --filter Name=tag:Name,Values=aws-lc-ci-bm-framework/aws-lc-ci-bm-framework-ec2-vpc --query Vpcs[*].VpcId --output text)"
sg_id="$(aws ec2 describe-security-groups --filter Name=vpc-id,Values="${vpc_id}" --filter Name=group-name,Values=bm_framework_ec2_sg --query SecurityGroups[*].GroupId --output text)"
subnet_id="$(aws ec2 describe-subnets --filter Name=vpc-id,Values="${vpc_id}" --filter Name=state,Values=available --filter Name=tag:Name,Values=aws-lc-ci-bm-framework/aws-lc-ci-bm-framework-ec2-vpc/PrivateSubnet1 --query Subnets[*].SubnetId --output text)"

#$1 is nohw type, $2 is OPENSSL_ia32cap value
generate_ssm_document_file() {
  # use sed to replace placeholder values inside preexisting document
  sed -e "s,{AWS_ACCOUNT_ID},${AWS_ACCOUNT_ID},g" \
    -e "s,{PR_NUM},${CODEBUILD_WEBHOOK_TRIGGER},g" \
    -e "s,{COMMIT_ID},${CODEBUILD_SOURCE_VERSION},g" \
    -e "s,{GITHUB_REPO},${CODEBUILD_SOURCE_REPO_URL},g" \
    -e "s,{OPENSSL_ia32cap},$2,g" \
    -e "s,{NOHW_TYPE},$1,g" \
    tests/ci/cdk/cdk/ssm/bm_framework_ssm_document.yaml \
    >tests/ci/cdk/cdk/ssm/bm_framework_"$1"_ssm_document.yaml
}

# create the ssm documents that will be used for the various ssm commands
generate_ssm_document_file "" ""
generate_ssm_document_file "nosha" "~0x100000000"
generate_ssm_document_file "noavx" "~0x1000000000000000:0xC0010020"

#$1 for ami, $2 for instance-type, echos the instance id so we can capture the output
create_ec2_instances() {
  local instance_id
  instance_id="$(aws ec2 run-instances --image-id "$1" --count 1 \
    --instance-type "$2" --security-group-ids "${sg_id}" --subnet-id "${subnet_id}" \
    --block-device-mappings 'DeviceName="/dev/sda1",Ebs={DeleteOnTermination=True,VolumeSize=200}' \
    --tag-specifications 'ResourceType="instance",Tags=[{Key="aws-lc",Value="aws-lc-ci-bm-framework-ec2-x86-instance"}]' \
    --iam-instance-profile Name=aws-lc-ci-bm-framework-ec2-profile \
    --placement 'AvailabilityZone=us-west-2a' \
    --query Instances[*].InstanceId --output text)"
  echo "${instance_id}"
}

# create ec2 instances for x86 and arm
x86_id=$(create_ec2_instances "ami-01773ce53581acf22" "c5.metal")
arm_id=$(create_ec2_instances "ami-018e246d8c0f39ae5" "c6g.metal")
x86_nosha_id=$(create_ec2_instances "ami-01773ce53581acf22" "m5.metal")
x86_noavx_id=$(create_ec2_instances "ami-01773ce53581acf22" "c5.metal")
instance_ids="${x86_id} ${arm_id} ${x86_nosha_id} ${x86_noavx_id}"

# if any of the ids are blank, ec2 creation failed
if [[ -z "${x86_id}" ]] || [[ -z "${arm_id}" ]] || [[ -z "${x86_nosha_id}" ]] || [[ -z "${x86_noavx_id}" ]];  then
  exit 1
fi

# Give a few minutes for the ec2 instances to be ready
sleep 60

for i in {1..30}; do
  ready=true
  for id in ${instance_ids}; do
    status=$(aws ssm describe-instance-information --filter Key="InstanceIds",Values="${id}" \
    --query InstanceInformationList[*].PingStatus --output text)
    if [ "${status}" != Online ]; then
      ready=false
    fi
  done
  if [ "${ready}" = true ]; then
    break
  fi
  echo "Wait for instances to be able to run the SSM commands"

  # if we've hit the 30 minute mark and still aren't ready, then something has gone wrong
  if [ "${i}" = 30 ]; then exit 1; fi
  sleep 60
done

# Create, and run ssm command for arm & x86
ssm_doc_name=$(create_ssm_document "bm_framework_")
nosha_ssm_doc_name=$(create_ssm_document "bm_framework_nosha")
noavx_ssm_doc_name=$(create_ssm_document "bm_framework_noavx")
ssm_document_names="${ssm_doc_name} ${nosha_ssm_doc_name} ${noavx_ssm_doc_name}"

# delete contents of 'latest' folders before uploading anything new to them
aws s3 rm s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-pr-bucket/latest-${CODEBUILD_WEBHOOK_TRIGGER}" --recursive
aws s3 rm s3://"${AWS_ACCOUNT_ID}-aws-lc-ci-bm-framework-prod-bucket/latest" --recursive

cloudwatch_group_name="aws-lc-ci-bm-framework-cw-logs"
x86_ssm_command_id=$(run_ssm_command "${ssm_doc_name}" "${x86_id}" "${cloudwatch_group_name}")
arm_ssm_command_id=$(run_ssm_command "${ssm_doc_name}" "${arm_id}" "${cloudwatch_group_name}")
nosha_ssm_command_id=$(run_ssm_command "${nosha_ssm_doc_name}" "${x86_nosha_id}" "${cloudwatch_group_name}")
noavx_ssm_command_id=$(run_ssm_command "${noavx_ssm_doc_name}" "${x86_noavx_id}" "${cloudwatch_group_name}")
ssm_command_ids="${x86_ssm_command_id} ${arm_ssm_command_id} ${nosha_ssm_command_id} ${noavx_ssm_command_id}"

# Give some time for the commands to run
for i in {1..30}; do
  echo "${i}: Continue to wait 3 min for SSM commands to finish."
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
