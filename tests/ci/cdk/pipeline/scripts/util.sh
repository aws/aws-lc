#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

if [[ -z "${PIPELINE_EXECUTION_ID:+x}" ]]; then
  TRIGGER_TYPE="manual"
else
  TRIGGER_TYPE="pipeline"
fi

function assume_role() {
  set +x
  local role_arn=${1:-${CROSS_ACCOUNT_BUILD_ROLE_ARN}}

  if [[ -z ${role_arn} ]]; then
    echo "No role arn provided"
    return 1
  fi

  local session_name=${CROSS_ACCOUNT_BUILD_SESSION:-"build-session"}
  CREDENTIALS=$(aws sts assume-role --role-arn "${role_arn}" --role-session-name "${session_name}")
  export AWS_ACCESS_KEY_ID=$(echo $CREDENTIALS | jq -r .Credentials.AccessKeyId)
  export AWS_SECRET_ACCESS_KEY=$(echo $CREDENTIALS | jq -r .Credentials.SecretAccessKey)
  export AWS_SESSION_TOKEN=$(echo $CREDENTIALS | jq -r .Credentials.SessionToken)
  set -x
}

function refresh_session() {
  unset AWS_ACCESS_KEY_ID
  unset AWS_SECRET_ACCESS_KEY
  unset AWS_SESSION_TOKEN

  if [[ -z "${PIPELINE_EXECUTION_ID:+x}" ]]; then
    echo "Security token expired. Please monitor build progress on the console"
    exit 1
  fi

  assume_role
}

function start_codebuild_project() {
  local project=${1}
  local commit_hash=${2:-main}

  if [[ -z ${project} ]]; then
    echo "No project name provided."
    exit 1
  fi

  # https://awscli.amazonaws.com/v2/documentation/api/latest/reference/codebuild/start-build-batch.html
  build_id=$(aws codebuild start-build-batch --project-name ${project} \
    --source-version ${commit_hash} \
    --environment-variables-override "name=TRIGGER_TYPE,value=${TRIGGER_TYPE},type=PLAINTEXT" \
    --query "buildBatch.id" \
    --output text)
  export BUILD_BATCH_ID=${build_id}
}

function retry_batch_build() {
  aws codebuild retry-build-batch --id "${BUILD_BATCH_ID}" \
    --retry-type RETRY_FAILED_BUILDS
}

function codebuild_build_status_check() {
  # Every 5 min, this function checks if the linux docker image batch code build finished successfully.
  # Normally, docker img build can take up to 1 hour. By default, we wait up to 30 * 5 min.
  local timeout=${1:-180}
  local status_check_max=$((timeout / 5))
  for i in $(seq 1 ${status_check_max}); do
    # https://docs.aws.amazon.com/cli/latest/reference/codebuild/batch-get-build-batches.html
    build_batch_status=$(aws codebuild batch-get-build-batches --ids "${BUILD_BATCH_ID}" \
      --query "buildBatches[0].buildBatchStatus" \
      --output text 2>&1)
    if [[ ${build_batch_status} == "SUCCEEDED" ]]; then
      echo "Build ${BUILD_BATCH_ID} finished successfully."
      return 0
    elif [[ ${build_batch_status} == "FAILED" ]]; then
      echo "Build ${BUILD_BATCH_ID} failed."
      return 1
    elif [[ ${build_batch_status} == "IN_PROGRESS" ]]; then
      echo "${i}: Wait 5 min for build job finish."
      sleep 300
    # if the build runs for too long, AWS sessions may expire and need to be refreshed
    elif echo "${build_batch_status}" | grep -q "ExpiredTokenException"; then
      refresh_session
    else
      echo "Build ${BUILD_BATCH_ID} returns: ${build_batch_status}. Exiting..."
      return 1
    fi
  done
  echo "Build ${BUILD_BATCH_ID} takes more time than expected."
  return 1
}

function start_windows_img_build() {
  # EC2 takes several minutes to be ready for running command.
  echo "Wait 3 min for EC2 ready for SSM command execution."
  sleep 180

  # Run commands on windows EC2 instance to build windows docker images.
  for i in {1..60}; do
    instance_id=$(aws ec2 describe-instances \
      --filters "Name=tag:${WIN_EC2_TAG_KEY},Values=${WIN_EC2_TAG_VALUE}" \
      --query 'Reservations[0].Instances[0].InstanceId' \
      --output text 2>&1)
    # if the build runs for too long, AWS sessions may expire and need to be refreshed
    if echo "${instance_id}" | grep -q "RequestExpired"; then
      refresh_session
    elif [[ "${instance_id}" == "null" ]]; then
      sleep 60
      continue
    fi
    instance_ping_status=$(aws ssm describe-instance-information \
      --filters "Key=InstanceIds,Values=${instance_id}" | jq -r '.InstanceInformationList[0].PingStatus')
    if [[ "${instance_ping_status}" == "Online" ]]; then
      # https://awscli.amazonaws.com/v2/documentation/api/latest/reference/ssm/send-command.html
      command_id=$(aws ssm send-command \
        --instance-ids "${instance_id}" \
        --document-name "${WIN_DOCKER_BUILD_SSM_DOCUMENT}" \
        --output-s3-bucket-name "${S3_FOR_WIN_DOCKER_IMG_BUILD}" \
        --output-s3-key-prefix 'runcommand' \
        --parameters "TriggerType=[\"${TRIGGER_TYPE}\"]" |
        jq -r '.Command.CommandId')
      # Export for checking command run status.
      export WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID="${command_id}"
      echo "Windows ec2 is executing SSM command."
      return 0
    else
      echo "${i}: Current instance ping status: ${instance_ping_status}. Wait 1 minute to retry SSM command execution."
      sleep 60
    fi
  done
  echo "After 60 minutes, Windows ec2 is still not ready for SSM commands execution. Exit."
  return 1
}

function win_docker_img_build_status_check() {
  # Every 5 min, this function checks if the windows docker image build is finished successfully.
  # Normally, docker img build can take up to 1 hour.
  local timeout=${1:-150}
  local status_check_max=$((timeout / 5))
  for i in $(seq 1 ${status_check_max}); do
    # https://awscli.amazonaws.com/v2/documentation/api/latest/reference/ssm/list-commands.html
    command_run_status=$(aws ssm list-commands --command-id "${WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID}" \
            --query 'Commands[0].Status' \
            --output text 2>&1)
    if [[ ${command_run_status} == "Success" ]]; then
      echo "SSM command ${WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID} finished successfully."
      return 0
    elif [[ ${command_run_status} == "Failed" ]]; then
      echo "SSM command ${WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID} failed."
      return 1
    elif [[ ${command_run_status} == "InProgress" ]]; then
      echo "${i}: Wait 5 min for build job finish."
      sleep 300
    # if the build runs for too long, AWS sessions may expire and need to be refreshed
    elif echo "${command_run_status}" | grep -q "ExpiredTokenException"; then
      refresh_session
    else
      echo "SSM commands ${WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID} returns: ${command_run_status}. Exiting..."
      return 1
    fi
  done
  echo "SSM command ${WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID} takes more time than expected."
  return 1
}
