#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Please run from project root folder!
# You'll want to set the codebuild env variables set if running locally

# cleanup code
cleanup() {
  set +e
  # delete the various documents that we created
  for name in ${ssm_document_names};do
    aws ssm delete-document --name "${name}"
  done
}

# we wanna run the cleanup code on exit
trap cleanup EXIT

# print some information for reference
echo GitHub PR Number: "${CODEBUILD_WEBHOOK_TRIGGER}"
echo GitHub Branch Name: "${CODEBUILD_WEBHOOK_HEAD_REF}"
AWS_ACCOUNT_ID=$(aws sts get-caller-identity --query Account --output text)
echo AWS Account ID: "${AWS_ACCOUNT_ID}"
echo GitHub Repo Link: "${CODEBUILD_SOURCE_REPO_URL}"
export CLOUDWATCH_LOG_GROUP="aws-lc-ci-macos-arm-cw-logs"

# get information for ec2 instances
vpc_id="$(aws ec2 describe-vpcs --filter Name=tag:Name,Values=aws-lc-ci-bm-framework/aws-lc-ci-bm-framework-ec2-vpc --query Vpcs[*].VpcId --output text)"
sg_id="$(aws ec2 describe-security-groups --filter Name=vpc-id,Values="${vpc_id}" --filter Name=group-name,Values=bm_framework_ec2_sg --query SecurityGroups[*].GroupId --output text)"
subnet_id="$(aws ec2 describe-subnets --filter Name=vpc-id,Values="${vpc_id}" --filter Name=state,Values=available --filter Name=tag:Name,Values=aws-lc-ci-bm-framework/aws-lc-ci-bm-framework-ec2-vpc/PrivateSubnet1 --query Subnets[*].SubnetId --output text)"
ec2_instance="$(aws ec2 describe-instances --filter Name=tag:Name,Values=aws-lc-ci-macos-arm-ec2-instance --query Reservations[*].Instances[*].InstanceId --output text)"

generate_ssm_document_file() {
  # use sed to replace placeholder values inside preexisting document
  sed -e "s,{AWS_ACCOUNT_ID},${AWS_ACCOUNT_ID},g" \
    -e "s,{PR_NUM},${CODEBUILD_WEBHOOK_TRIGGER//pr\/},g" \
    -e "s,{GITHUB_REPO},${CODEBUILD_SOURCE_REPO_URL},g" \
    tests/ci/cdk/cdk/ssm/m1_tests_ssm_document.yaml \
    >tests/ci/cdk/cdk/ssm/m1_test_framework_ssm_document_tmp.yaml
}

create_ssm_document() {
  local doc_name
  doc_name=m1_test_framework_ssm_document_"${CODEBUILD_SOURCE_VERSION}"
  aws ssm create-document --content file://tests/ci/cdk/cdk/ssm/m1_test_framework_ssm_document_tmp.yaml \
    --name "${doc_name}" \
    --document-type Command \
    --document-format YAML >/dev/null
  echo "${doc_name}"
}

#$1 is the document name, $2 is the instance ids
run_ssm_command() {
  local command_id
  command_id="$(aws ssm send-command --instance-ids "${2}" \
    --document-name "${1}" \
    --cloud-watch-output-config CloudWatchLogGroupName="${CLOUDWATCH_LOG_GROUP}",CloudWatchOutputEnabled=true \
    --query Command.CommandId --output text)"
  echo "${command_id}"
}

# create the ssm documents that will be used for the various ssm commands
generate_ssm_document_file

# Create, and run ssm command.
ssm_doc_name=$(create_ssm_document)
ssm_document_names="${ssm_doc_name}"

m1_ssm_command_id=$(run_ssm_command "${ssm_doc_name}" "${ec2_instance}")
ssm_command_ids="${m1_ssm_command_id}"

run_url="https://${AWS_REGION}.console.aws.amazon.com/cloudwatch/home?region=${AWS_REGION}\
#logsV2:log-groups/log-group/${CLOUDWATCH_LOG_GROUP}/log-events/\
${m1_ssm_command_id}\$252F${ec2_instance}\$252FrunShellScript\$252Fstdout"

echo "Actual Run in EC2 can be observered at CloudWatch URL: ${run_url}"

# Give some time for the commands to run
for i in {1..45}; do
  echo "${i}: Continue to wait 2 min for SSM commands to finish."
  sleep 120
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