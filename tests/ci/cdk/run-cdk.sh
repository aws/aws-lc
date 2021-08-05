#!/bin/bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -exuo pipefail

# -e: Exit on any failure
# -x: Print the command before running
# -u: Any variable that is not set will cause an error if used
# -o pipefail: Makes sure to exit a pipeline with a non-zero error code if any command in the pipeline exists with a
#              non-zero error code.

function delete_s3_buckets() {
  aws s3api list-buckets --query "Buckets[].Name" | jq '.[]' | while read -r i; do
    bucket_name=$(echo "${i}" | tr -d '"')
    # Delete the bucket if its name uses AWS_LC_S3_BUCKET_PREFIX.
    if [[ "${bucket_name}" == *"${AWS_LC_S3_BUCKET_PREFIX}"* ]]; then
      aws s3 rm "s3://${bucket_name}" --recursive
      aws s3api delete-bucket --bucket "${bucket_name}"
    # Delete bm-framework buckets if we're not on the team account
    elif [[ "${CDK_DEPLOY_ACCOUNT}" != "620771051181" ]] && [[ "${bucket_name}" == *"${aws-lc-ci-bm-framework}"* ]]; then
      aws s3 rm "s3://${bucket_name}" --recursive
      aws s3api delete-bucket --bucket "${bucket_name}"
    fi
  done
}

function delete_container_repositories() {
  ecr_repos=$(aws ecr describe-repositories)
  if [[ "${ecr_repos}" == *"${ECR_LINUX_AARCH_REPO_NAME}"* ]]; then
    aws ecr delete-repository --repository-name "${ECR_LINUX_AARCH_REPO_NAME}" --force
  fi
  if [[ "${ecr_repos}" == *"${ECR_LINUX_X86_REPO_NAME}"* ]]; then
    aws ecr delete-repository --repository-name "${ECR_LINUX_X86_REPO_NAME}" --force
  fi
  if [[ "${ecr_repos}" == *"${ECR_WINDOWS_X86_REPO_NAME}"* ]]; then
    aws ecr delete-repository --repository-name "${ECR_WINDOWS_X86_REPO_NAME}" --force
  fi
}

function delete_external_credential() {
  # This deletion may take a few minutes to take effects.
  # https://docs.aws.amazon.com/cli/latest/reference/secretsmanager/delete-secret.html
  # https://aws.amazon.com/premiumsupport/knowledge-center/delete-secrets-manager-secret/
  aws secretsmanager delete-secret --secret-id "${AWS_LC_CI_SECRET_NAME}" --force-delete-without-recovery
}

function store_external_credential() {
  # Always delete the secret to avoid resource name conflicts.
  delete_external_credential
  # When creating secret with the same name repeatedly,
  # below error may occur because the deletion may take a few minutes to take effects.
  # "You can't create this secret because a secret with this name is already scheduled for deletion."
  # To avoid that, sleep 1 min
  sleep 60
  # https://docs.aws.amazon.com/cli/latest/reference/secretsmanager/create-secret.html
  key_value="{\"GITHUB_PERSONAL_ACCESS_TOKEN\":\"${GITHUB_ACCESS_TOKEN}\"}"
  secret_arn=$(aws secretsmanager create-secret --name "${AWS_LC_CI_SECRET_NAME}" --secret-string "${key_value}" | jq -r '.ARN')
  # Export this variable so CDK can create related IAM policy on this ARN.
  export EXTERNAL_CREDENTIAL_SECRET_ARN="${secret_arn}"
}

function destroy_ci() {
  cdk destroy aws-lc-* --force
  # CDK stack destroy does not delete s3 bucket automatically.
  delete_s3_buckets
  # CDK stack destroy does not delete ecr automatically.
  delete_container_repositories
  # Delete the secret from Secrets Manager.
  delete_external_credential
}

function destroy_docker_img_build_stack() {
  # Destroy all temporary resources created for all docker image build.
  cdk destroy aws-lc-docker-image-build-* --force
  # CDK stack destroy does not delete s3 bucket automatically.
  delete_s3_buckets
  # Delete the secret from Secrets Manager.
  delete_external_credential
}

function create_docker_img_build_stack() {
  # Clean up build stacks if exists.
  destroy_docker_img_build_stack
  # Use SecretsManager to store GitHub personal access token.
  store_external_credential
  # Deploy aws-lc ci stacks.
  # When repeatedly deploy, error 'EIP failed Reason: Maximum number of addresses has been reached' can happen.
  # https://forums.aws.amazon.com/thread.jspa?messageID=952368
  # Workaround: go to AWS EIP console, release unused IP.
  cdk deploy aws-lc-docker-image-build-* --require-approval never
}

function create_github_ci_stack() {
  cdk deploy aws-lc-ci-* --require-approval never

  # Need to use aws cli to change webhook build type because CFN is not ready yet.
  aws codebuild update-webhook --project-name aws-lc-ci-linux-x86 --build-type BUILD_BATCH
  aws codebuild update-webhook --project-name aws-lc-ci-linux-arm --build-type BUILD_BATCH
  aws codebuild update-webhook --project-name aws-lc-ci-windows-x86 --build-type BUILD_BATCH
  aws codebuild update-webhook --project-name aws-lc-ci-fuzzing --build-type BUILD_BATCH
  aws codebuild update-webhook --project-name aws-lc-ci-bm-framework --build-type BUILD_BATCH
}

function build_linux_img() {
  # https://awscli.amazonaws.com/v2/documentation/api/latest/reference/codebuild/start-build-batch.html
  build_id=$(aws codebuild start-build-batch --project-name aws-lc-docker-image-build-linux | jq -r '.buildBatch.id')
  export AWS_LC_LINUX_BUILD_BATCH_ID="${build_id}"
}

function build_windows_img() {
  # EC2 takes several minutes to be ready for running command.
  echo "Wait 3 min for EC2 ready for SSM command execution."
  sleep 180

  # Run commands on windows EC2 instance to build windows docker images.
  for i in {1..60}; do
    instance_id=$(aws ec2 describe-instances \
      --filters "Name=tag:${WIN_EC2_TAG_KEY},Values=${WIN_EC2_TAG_VALUE}" | jq -r '.Reservations[0].Instances[0].InstanceId')
    if [[ "${instance_id}" == "null" ]]; then
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
        --output-s3-key-prefix 'runcommand' | jq -r '.Command.CommandId')
      # Export for checking command run status.
      export WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID="${command_id}"
      echo "Windows ec2 is executing SSM command."
      return
    else
      echo "${i}: Current instance ping status: ${instance_ping_status}. Wait 1 minute to retry SSM command execution."
      sleep 60
    fi
  done
  echo "After 30 minutes, Windows ec2 is still not ready for SSM commands execution. Exit."
  exit 1
}

function linux_docker_img_build_status_check() {
  # Every 5 min, this function checks if the linux docker image batch code build finished successfully.
  # Normally, docker img build can take up to 1 hour. Here, we wait up to 30 * 5 min.
  for i in {1..30}; do
    # https://docs.aws.amazon.com/cli/latest/reference/codebuild/batch-get-build-batches.html
    build_batch_status=$(aws codebuild batch-get-build-batches --ids "${AWS_LC_LINUX_BUILD_BATCH_ID}" | jq -r '.buildBatches[0].buildBatchStatus')
    if [[ ${build_batch_status} == 'SUCCEEDED' ]]; then
      echo "Code build ${AWS_LC_LINUX_BUILD_BATCH_ID} finished successfully."
      return
    elif [[ ${build_batch_status} == 'FAILED' ]]; then
      echo "Code build ${AWS_LC_LINUX_BUILD_BATCH_ID} failed."
      exit 1
    else
      echo "${i}: Wait 5 min for docker image build job finish."
      sleep 300
    fi
  done
  echo "Code build ${AWS_LC_LINUX_BUILD_BATCH_ID} takes more time than expected."
  exit 1
}

function win_docker_img_build_status_check() {
  # Every 5 min, this function checks if the windows docker image build is finished successfully.
  # Normally, docker img build can take up to 1 hour. Here, we wait up to 30 * 5 min.
  for i in {1..30}; do
    # https://awscli.amazonaws.com/v2/documentation/api/latest/reference/ssm/list-commands.html
    command_run_status=$(aws ssm list-commands --command-id "${WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID}" | jq -r '.Commands[0].Status')
    if [[ ${command_run_status} == 'Success' ]]; then
      echo "SSM command ${WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID} finished successfully."
      return
    elif [[ ${command_run_status} == 'Failed' ]]; then
      echo "SSM command ${WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID} failed."
      exit 1
    else
      echo "${i}: Wait 5 min for windows docker image build job finish."
      sleep 300
    fi
  done
  echo "SSM command ${WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID} takes more time than expected."
  exit 1
}

function validate_github_access_token {
  # GitHub access token is only needed when building Docker images.
  if [[ -z "${GITHUB_ACCESS_TOKEN+x}" || -z "${GITHUB_ACCESS_TOKEN}" ]]; then
    echo '--github-access-token is required for aws-lc ci setup.'
    exit 1
  fi
}

function build_docker_images() {
  # Always destroy docker build stacks (which include EC2 instance) on EXIT.
  trap destroy_docker_img_build_stack EXIT

  # Check prerequisite.
  # One prerequisite is to provide GitHub access token so AWS CodeBuild can pull Docker images from GitHub.
  validate_github_access_token

  # Create/update aws-ecr repo.
  cdk deploy aws-lc-ecr-* --require-approval never

  # Create docker image build stack.
  create_docker_img_build_stack

  echo "Activating AWS CodeBuild to build Linux aarch & x86 docker images."
  build_linux_img

  echo "Executing AWS SSM commands to build Windows docker images."
  build_windows_img

  echo "Waiting for docker images creation. Building the docker images need to take 1 hour."
  # TODO(CryptoAlg-624): These image build may fail due to the Docker Hub pull limits made on 2020-11-01.
  linux_docker_img_build_status_check
  win_docker_img_build_status_check
}

function setup_ci() {
  build_docker_images

  create_github_ci_stack
}

###########################
# Main and related helper #
###########################

function script_helper() {
  cat <<EOF
This script uses CDK to deploy/destroy AWS resources defined in the aws-lc cdk app.

For aws-lc continuous integration setup, this script uses aws cli to build some non-AWS resources(e.g. Docker image).

Options:
    --help                       Displays this help
    --aws-account                AWS account for CDK deploy/destroy. Default to '620771051181'.
    --aws-region                 AWS region for AWS resources creation. Default to 'us-west-2'.
    --github-repo-owner          GitHub repository owner. Default to 'awslabs'.
    --github-source-version      GitHub source version. Default to 'main'.
    --github-access-token        GitHub personal access token. Currently, only 'read:package' permission is needed.
                                 Only required for ci setup.
    --action                     Required. The value can be
                                   'deploy-ci': deploys aws-lc ci. This includes AWS and Docker image resources creation.
                                   'update-ci': update aws-lc ci. This only update AWS CodeBuild for GitHub CI.
                                   'destroy-ci': destroys AWS and Docker image resources used by aws-lc ci.
                                   'build-img': builds Docker image used by aws-lc ci.
                                                After image build, AWS resources are cleaned up.
                                   'diff': compares the specified stack with the deployed stack.
                                   'synth': synthesizes and prints the CloudFormation template for the stacks.
EOF
}

function export_global_variables() {
  # If these variables are not set or empty, defaults are export.
  if [[ -z "${CDK_DEPLOY_ACCOUNT+x}" || -z "${CDK_DEPLOY_ACCOUNT}" ]]; then
    export CDK_DEPLOY_ACCOUNT='620771051181'
  fi
  if [[ -z "${CDK_DEPLOY_REGION+x}" || -z "${CDK_DEPLOY_REGION}" ]]; then
    export CDK_DEPLOY_REGION='us-west-2'
  fi
  if [[ -z "${GITHUB_REPO_OWNER+x}" || -z "${GITHUB_REPO_OWNER}" ]]; then
    export GITHUB_REPO_OWNER='awslabs'
  fi
  if [[ -z "${GITHUB_SOURCE_VERSION+x}" || -z "${GITHUB_SOURCE_VERSION}" ]]; then
    export GITHUB_SOURCE_VERSION='main'
  fi
  # Other variables for managing resources.
  DATE_NOW="$(date +%Y-%m-%d-%H-%M)"
  export GITHUB_REPO='aws-lc'
  export ECR_LINUX_AARCH_REPO_NAME='aws-lc-docker-images-linux-aarch'
  export ECR_LINUX_X86_REPO_NAME='aws-lc-docker-images-linux-x86'
  export ECR_WINDOWS_X86_REPO_NAME='aws-lc-docker-images-windows-x86'
  export AWS_LC_S3_BUCKET_PREFIX='aws-lc-windows-docker-image-build-s3'
  export S3_FOR_WIN_DOCKER_IMG_BUILD="${AWS_LC_S3_BUCKET_PREFIX}-${DATE_NOW}"
  export WIN_EC2_TAG_KEY='aws-lc'
  export WIN_EC2_TAG_VALUE="aws-lc-windows-docker-image-build-${DATE_NOW}"
  export WIN_DOCKER_BUILD_SSM_DOCUMENT="windows-ssm-document-${DATE_NOW}"
  # During CI setup, used to create secret in AWS Secrets Manager for storing external credentials.
  # After CI setup, used to delete secret from AWS Secrets Manager.
  export AWS_LC_CI_SECRET_NAME='aws-lc-ci-external-credential'
}

function main() {
  # parse arguments.
  while [[ $# -gt 0 ]]; do
    case ${1} in
    --help)
      script_helper
      exit 0
      ;;
    --aws-account)
      export CDK_DEPLOY_ACCOUNT="${2}"
      shift
      ;;
    --aws-region)
      export CDK_DEPLOY_REGION="${2}"
      shift
      ;;
    --github-repo-owner)
      export GITHUB_REPO_OWNER="${2}"
      shift
      ;;
    --github-source-version)
      export GITHUB_SOURCE_VERSION="${2}"
      shift
      ;;
    --github-access-token)
      export GITHUB_ACCESS_TOKEN="${2}"
      shift
      ;;
    --action)
      export ACTION="${2}"
      shift
      ;;
    *)
      echo "${1} is not supported."
      exit 1
      ;;
    esac
    # Check next option -- key/value.
    shift
  done

  # Make sure action is set.
  if [[ -z "${ACTION+x}" || -z "${ACTION}" ]]; then
    echo "${ACTION} is required input."
    exit 1
  fi

  # Export global variables, which provides the contexts needed by ci setup/destroy.
  export_global_variables

  # Execute the action.
  case ${ACTION} in
  deploy-ci)
    setup_ci
    ;;
  update-ci)
    create_github_ci_stack
    ;;
  destroy-ci)
    destroy_ci
    ;;
  build-img)
    build_docker_images
    ;;
  synth)
    cdk synth aws-lc-ci-*
    ;;
  diff)
    cdk diff aws-lc-ci-*
    ;;
  *)
    echo "--action is required. Use '--help' to see allowed actions."
    exit 1
    ;;
  esac
}

# Invoke main
main "$@"
