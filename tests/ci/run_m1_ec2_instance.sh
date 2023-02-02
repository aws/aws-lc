#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Please run from project root folder!
# You'll want to set the codebuild env variables set if running locally
source tests/ci/common_ssm_setup.sh

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
export cloudwatch_group_name="aws-lc-ci-macos-arm-cw-logs"

# get information for ec2 instances
ec2_instance="$(aws ec2 describe-instances --filter "Name=tag:Name,Values=aws-lc-ci-macos-arm-ec2-instance" "Name=instance-state-name,Values=running" --query Reservations[*].Instances[*].InstanceId --output text)"

generate_ssm_document_file() {
  # use sed to replace placeholder values inside preexisting document
  sed -e "s,{AWS_ACCOUNT_ID},${AWS_ACCOUNT_ID},g" \
    -e "s,{PR_NUM},${CODEBUILD_WEBHOOK_TRIGGER//pr\/},g" \
    -e "s,{GITHUB_REPO},${CODEBUILD_SOURCE_REPO_URL},g" \
    tests/ci/cdk/cdk/ssm/m1_tests_ssm_document.yaml \
    >tests/ci/cdk/cdk/ssm/macos_arm_ssm_document.yaml
}

# create the ssm documents that will be used for the various ssm commands
generate_ssm_document_file

# Create, and run ssm command.
ssm_doc_name=$(create_ssm_document "macos_arm")
ssm_document_names="${ssm_doc_name}"

m1_ssm_command_id=$(run_ssm_command "${ssm_doc_name}" "${ec2_instance}" ${cloudwatch_group_name})

run_url="https://${AWS_REGION}.console.aws.amazon.com/cloudwatch/home?region=${AWS_REGION}\
#logsV2:log-groups/log-group/${cloudwatch_group_name}/log-events/\
${m1_ssm_command_id}\$252F${ec2_instance}\$252FrunShellScript\$252Fstdout"

echo "Actual Run in EC2 can be observered at CloudWatch URL: ${run_url}"

# Give some time for the commands to run
done=false
success=false
for i in {1..45}; do
  echo "${i}: Continue to wait 2 min for SSM commands to finish."
  sleep 120

  ssm_command_status="$(aws ssm list-commands --command-id "${m1_ssm_command_id}" --query Commands[*].Status --output text)"
  ssm_target_count="$(aws ssm list-commands --command-id "${m1_ssm_command_id}" --query Commands[*].TargetCount --output text)"
  ssm_completed_count="$(aws ssm list-commands --command-id "${m1_ssm_command_id}" --query Commands[*].CompletedCount --output text)"
  if [[ ${ssm_command_status} == 'Success' && ${ssm_completed_count} == "${ssm_target_count}" ]]; then
    echo "SSM command ${m1_ssm_command_id} finished successfully."
    success=true
    done=true
  elif [[ ${ssm_command_status} == 'Failed' && ${ssm_completed_count} == "${ssm_target_count}" ]]; then
    echo "SSM command ${m1_ssm_command_id} failed."
    done=true
  else
    # Still running.
    done=false
  fi

  # if after the loop finish and done is still true, then we're done
  if [ "${done}" = true ]; then
    echo "M1 SSM command has finished."

    # if success is still true here, then none of the commands failed
    if [ "${success}" == true ]; then
      echo "M1 SSM command succeeded!"
      exit 0
    else
      echo "M1 SSM command failed!"
      exit 1
    fi
    break
  fi
done
exit 1