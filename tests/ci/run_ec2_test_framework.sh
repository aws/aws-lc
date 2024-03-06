#!/usr/bin/env bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Please run from project root folder!
# You'll want to set the codebuild env variables set if running locally
source tests/ci/common_ssm_setup.sh

AWS_ACCOUNT_ID=$(aws sts get-caller-identity --query Account --output text)

# Cleanup AWS resources.
cleanup() {
  set +e
  aws ec2 terminate-instances --instance-ids "${instance_id}"
  aws ssm delete-document --name "${ssm_doc_name}"
}

generate_ssm_document_file() {
  # use sed to replace placeholder values inside preexisting document
  sed -e "s,{AWS_ACCOUNT_ID},${AWS_ACCOUNT_ID},g" \
    -e "s,{PR_NUM},${CODEBUILD_WEBHOOK_TRIGGER},g" \
    -e "s,{COMMIT_ID},${CODEBUILD_SOURCE_VERSION},g" \
    -e "s,{GITHUB_REPO},${CODEBUILD_SOURCE_REPO_URL},g" \
    -e "s,{ECR_DOCKER_TAG},${ecr_docker_tag},g" \
    tests/ci/cdk/cdk/ssm/general_test_run_ssm_document.yaml \
    > "tests/ci/cdk/cdk/ssm/${ec2_ami_id}_ssm_document.yaml"
}

#$1 for ami, $2 for instance-type, echos the instance id so we can capture the output
create_ec2_instances() {
  local instance_id
  instance_id="$(aws ec2 run-instances --image-id "$1" --count 1 \
    --instance-type "$2" --security-group-ids "${EC2_SECURITY_GROUP_ID}" --subnet-id "${EC2_SUBNET_ID}" \
    --block-device-mappings 'DeviceName="/dev/sda1",Ebs={DeleteOnTermination=True,VolumeSize=200}' \
    --tag-specifications 'ResourceType="instance",Tags=[{Key="Name",Value="ec2-test-'"$CODEBUILD_WEBHOOK_TRIGGER"'"}]' \
    --iam-instance-profile Name=aws-lc-ci-ec2-test-framework-ec2-profile \
    --placement 'AvailabilityZone=us-west-2a' \
    --instance-initiated-shutdown-behavior terminate \
    --query Instances[*].InstanceId --output text)"
  echo "${instance_id}"
}

trap cleanup EXIT

# print some information for reference
echo GitHub PR Number: "${CODEBUILD_WEBHOOK_TRIGGER}"
echo GitHub Commit Version: "${CODEBUILD_SOURCE_VERSION}"
echo AWS Account ID: "${AWS_ACCOUNT_ID}"
echo GitHub Repo Link: "${CODEBUILD_SOURCE_REPO_URL}"
export ec2_ami_id="$1"
export ec2_instance_type="$2"
export ecr_docker_tag="$3"
export s3_bucket_name="aws-lc-codebuild"

# create the ssm documents that will be used for the various ssm commands
generate_ssm_document_file

# create ec2 instances
instance_id=$(create_ec2_instances "${ec2_ami_id}" "${ec2_instance_type}")
if [[ -z "${instance_id}" ]];  then
  exit 1
fi

# Give a few minutes for the ec2 instance to be ready
sleep 60
for i in {1..30}; do
  status=$(aws ssm describe-instance-information --filter Key="InstanceIds",Values="${instance_id}" \
    --query InstanceInformationList[*].PingStatus --output text)
  if [ "${status}" == Online ]; then
    break
  fi
  echo "Wait for instances to be able to run the SSM commands"

  # if we've hit the 30 minute mark and still aren't ready, then something has gone wrong
  if [ "${i}" = 30 ]; then exit 1; fi
  sleep 60
done


# Create, and run ssm command.
ssm_doc_name=$(create_ssm_document "${ec2_ami_id}")

cloudwatch_group_name="aws-lc-ci-ec2-test-framework-cw-logs"
ec2_test_ssm_command_id=$(run_ssm_command "${ssm_doc_name}" "${instance_id}" ${cloudwatch_group_name})

run_url="https://${AWS_REGION}.console.aws.amazon.com/cloudwatch/home?region=${AWS_REGION}\
#logsV2:log-groups/log-group/${cloudwatch_group_name}/log-events/\
${ec2_test_ssm_command_id}\$252F${instance_id}\$252FrunShellScript\$252Fstdout"

echo "Actual Run in EC2 can be observered at CloudWatch URL: ${run_url}"

# Give some time for the commands to run
done=false
success=false
for i in {1..45}; do
  echo "${i}: Continue to wait 2 min for SSM commands to finish."
  sleep 120

  ssm_command_status="$(aws ssm list-commands --command-id "${ec2_test_ssm_command_id}" --query Commands[*].Status --output text)"
  ssm_target_count="$(aws ssm list-commands --command-id "${ec2_test_ssm_command_id}" --query Commands[*].TargetCount --output text)"
  ssm_completed_count="$(aws ssm list-commands --command-id "${ec2_test_ssm_command_id}" --query Commands[*].CompletedCount --output text)"
  if [[ ${ssm_command_status} == 'Success' && ${ssm_completed_count} == "${ssm_target_count}" ]]; then
    echo "SSM command ${ec2_test_ssm_command_id} finished successfully."
    success=true
    done=true
  elif [[ ${ssm_command_status} == 'Failed' && ${ssm_completed_count} == "${ssm_target_count}" ]]; then
    echo "SSM command ${ec2_test_ssm_command_id} failed."
    done=true
  else
    # Still running.
    done=false
  fi

  # if after the loop finish and done is still true, then we're done
  if [ "${done}" = true ]; then
    echo "EC2 SSM command has finished."

    # if success is still true here, then none of the commands failed
    if [ "${success}" == true ]; then
      echo "EC2 SSM command succeeded!"
      exit 0
    else
      echo "EC2 SSM command failed!"
      exit 1
    fi
    break
  fi
done
exit 1
