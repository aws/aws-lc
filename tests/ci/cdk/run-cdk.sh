#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exuo pipefail

source pipeline/scripts/util.sh

# -e: Exit on any failure
# -x: Print the command before running
# -u: Any variable that is not set will cause an error if used
# -o pipefail: Makes sure to exit a pipeline with a non-zero error code if any command in the pipeline exists with a
#              non-zero error code.

function delete_s3_buckets() {
  aws s3api list-buckets --query "Buckets[].Name" | jq '.[]' | while read -r i; do
    bucket_name=$(echo "${i}" | tr -d '"')
    # Delete the bucket if its name uses AWS_LC_S3_BUCKET_PREFIX.
    if [[ "${bucket_name}" == *"${S3_FOR_WIN_DOCKER_IMG_BUILD}"* ]]; then
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

function destroy_ci() {
  if [[ "${DEPLOY_ACCOUNT}" == "620771051181" || "${DEPLOY_ACCOUNT}" == "351119683581" ]]; then
    echo "destroy_ci should not be executed on team account."
    exit 1
  fi
  cdk destroy 'aws-lc-*' --force
  # CDK stack destroy does not delete s3 bucket automatically.
  delete_s3_buckets
  # CDK stack destroy does not delete ecr automatically.
  delete_container_repositories
}

function destroy_docker_img_build_stack() {
  if [[ "${IMG_BUILD_STATUS}" == "Failed" ]]; then
    echo "Docker images build failed. AWS resources of building Docker images is kept for debug."
    exit 1
  fi
  # Destroy all temporary resources created for all docker image build.
  cdk destroy 'aws-lc-docker-image-build-*' --force
  # CDK stack destroy does not delete s3 bucket automatically.
  delete_s3_buckets
}

function create_linux_docker_img_build_stack() {
  # Deploy aws-lc ci stacks.
  # When repeatedly deploy, error 'EIP failed Reason: Maximum number of addresses has been reached' can happen.
  #
  # Workaround: The default quota amount is 5 EIP addresses. Go to
  # https://us-west-2.console.aws.amazon.com/servicequotas/home/services/ec2/quotas and request a quota
  # increase for "EC2-VPC Elastic IPs".
  cdk deploy aws-lc-docker-image-build-linux --require-approval never
}

function create_win_docker_img_build_stack() {
  # Deploy aws-lc ci stacks.
  # When repeatedly deploy, error 'EIP failed Reason: Maximum number of addresses has been reached' can happen.
  #
  # Workaround: The default quota amount is 5 EIP addresses. Go to
  # https://us-west-2.console.aws.amazon.com/servicequotas/home/services/ec2/quotas and request a quota
  # increase for "EC2-VPC Elastic IPs".
  cdk deploy aws-lc-docker-image-build-windows --require-approval never
}

function create_github_ci_stack() {
  cdk deploy 'aws-lc-ci-*' --require-approval never
}

function run_linux_img_build() {
  # https://awscli.amazonaws.com/v2/documentation/api/latest/reference/codebuild/start-build-batch.html
  build_id=$(aws codebuild start-build-batch --project-name aws-lc-docker-image-build-linux | jq -r '.buildBatch.id')
  export AWS_LC_LINUX_BUILD_BATCH_ID="${build_id}"
}

function run_windows_img_build() {
  # EC2 takes several minutes to be ready for running command.
#  echo "Wait 3 min for EC2 ready for SSM command execution."
#  sleep 180

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
        --output-s3-key-prefix 'runcommand' \
        --parameters "TriggerType=[\"manual\"]" | \
        jq -r '.Command.CommandId')
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
  export IMG_BUILD_STATUS='Failed'
  # Every 5 min, this function checks if the linux docker image batch code build finished successfully.
  # Normally, docker img build can take up to 1 hour. Here, we wait up to 30 * 5 min.
  for i in {1..30}; do
    # https://docs.aws.amazon.com/cli/latest/reference/codebuild/batch-get-build-batches.html
    build_batch_status=$(aws codebuild batch-get-build-batches --ids "${AWS_LC_LINUX_BUILD_BATCH_ID}" | jq -r '.buildBatches[0].buildBatchStatus')
    if [[ ${build_batch_status} == 'SUCCEEDED' ]]; then
      export IMG_BUILD_STATUS='Success'
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
  export IMG_BUILD_STATUS='Failed'
  # Every 5 min, this function checks if the windows docker image build is finished successfully.
  # Normally, docker img build can take up to 1 hour. Here, we wait up to 30 * 5 min.
  for i in {1..30}; do
    # https://awscli.amazonaws.com/v2/documentation/api/latest/reference/ssm/list-commands.html
    command_run_status=$(aws ssm list-commands --command-id "${WINDOWS_DOCKER_IMG_BUILD_COMMAND_ID}" | jq -r '.Commands[0].Status')
    if [[ ${command_run_status} == 'Success' ]]; then
      export IMG_BUILD_STATUS='Success'
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

function build_linux_docker_images() {
  # Create/update aws-ecr repo.
  cdk deploy 'aws-lc-ecr-linux-*' --require-approval never

  # Create docker image build stack.
  create_linux_docker_img_build_stack

  echo "Activating AWS CodeBuild to build Linux aarch & x86 docker images."
  run_linux_img_build

  echo "Waiting for docker images creation. Building the docker images need to take 1 hour."
  # TODO(CryptoAlg-624): These image build may fail due to the Docker Hub pull limits made on 2020-11-01.
  linux_docker_img_build_status_check
}

function build_win_docker_images() {
 # Create/update aws-ecr repo.
 cdk deploy 'aws-lc-ecr-windows-*' --require-approval never

 # Create aws windows build stack
 create_win_docker_img_build_stack

 S3_FOR_WIN_DOCKER_IMG_BUILD=$(aws cloudformation describe-stack-resources \
                                        --stack-name aws-lc-docker-image-build-windows  \
                                        --query "StackResources[?ResourceType=='AWS::S3::Bucket'].PhysicalResourceId" \
                                        --output text)

 echo "Executing AWS SSM commands to build Windows docker images."
 run_windows_img_build

 echo "Waiting for docker images creation. Building the docker images need to take 1 hour."
 # TODO(CryptoAlg-624): These image build may fail due to the Docker Hub pull limits made on 2020-11-01.
 win_docker_img_build_status_check
}

function setup_ci() {
  build_linux_docker_images
  build_win_docker_images

  create_github_ci_stack
  create_android_resources
}

function deploy_production_pipeline() {
  cdk deploy AwsLcCiPipeline --require-approval never
}

function deploy_dev_pipeline() {
  if [[ -z "${DEPLOY_ACCOUNT:+x}" ]]; then
    echo "The pipeline needs a deployment acount to know where to deploy the CI to."
    exit 1
  fi

  if [[ ${DEPLOY_ACCOUNT} == '620771051181' ]]; then
    echo "Dev pipeline cannot deploy to production account."
    exit 1
  fi

  if [[ -z "${PIPELINE_ACCOUNT:+x}" ]]; then
    export PIPELINE_ACCOUNT=${DEPLOY_ACCOUNT}
  fi

  if [[ ${PIPELINE_ACCOUNT} == '774305600158' ]]; then
    echo "Cannot deploy. The production pipeline is hosted with the same name in this pipeline account."
    exit 1
  fi

  cdk deploy AwsLcCiPipeline --require-approval never
}

function create_android_resources() {
  # Use aws cli to create Device Farm project and get project arn to create device pools.
  # TODO: Move resource creation to aws cdk when cdk has support for device form resource constructs.
  # Issue: https://github.com/aws/aws-cdk/issues/17893
  DEVICEFARM_PROJECT=`aws devicefarm create-project --name aws-lc-android-ci | \
                             python3 -c 'import json,sys;obj=json.load(sys.stdin);print(obj["project"]["arn"])'`

  DEVICEFARM_DEVICE_POOL=`aws devicefarm create-device-pool --project-arn ${DEVICEFARM_PROJECT} \
    --name "aws-lc-device-pool" \
    --description "AWS-LC Device Pool" \
    --rules file://../android/devicepool_rules.json --max-devices 2 | \
    python3 -c 'import json,sys;obj=json.load(sys.stdin);print(obj["devicePool"]["arn"])'`

  DEVICEFARM_DEVICE_POOL_FIPS=`aws devicefarm create-device-pool --project-arn ${DEVICEFARM_PROJECT} \
    --name "aws-lc-device-pool-fips" \
    --description "AWS-LC FIPS Device Pool" \
    --rules file://../android/devicepool_rules_fips.json --max-devices 2 | \
    python3 -c 'import json,sys;obj=json.load(sys.stdin);print(obj["devicePool"]["arn"])'`

  cat <<EOF

DEVICEFARM_PROJECT arn value: ${DEVICEFARM_PROJECT}

DEVICEFARM_DEVICE_POOL arn value: ${DEVICEFARM_DEVICE_POOL}

DEVICEFARM_DEVICE_POOL_FIPS arn value: ${DEVICEFARM_DEVICE_POOL_FIPS}

Take the corresponding Device Farm arn values and update the arn values at tests/ci/kickoff_devicefarm_job.sh

EOF
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
    --deploy-account                AWS account for CDK deploy/destroy. Default to '620771051181'.
    --deploy-region                 AWS region for AWS resources creation. Default to 'us-west-2'.
    --github-repo-owner          GitHub repository owner. Default to 'aws'.
    --github-source-version      GitHub source version. Default to 'main'.
    --action                     Required. The value can be
                                   'deploy-ci': deploys aws-lc ci. This includes AWS and Docker image resources creation.
                                   'update-ci': update aws-lc ci. This only update AWS CodeBuild for GitHub CI.
                                   'destroy-ci': destroys AWS and Docker image resources used by aws-lc ci.
                                   'destroy-img-stack': destroys AWS resources created during built of Docker images.
                                   'build-linux-img': builds Linux Docker image used by aws-lc ci.
                                                After image build, AWS resources are cleaned up.
                                   'build-win-img': builds Windows Docker image used by aws-lc ci.
                                                After image build, AWS resources are cleaned up.
                                   'diff': compares the specified stack with the deployed stack.
                                   'synth': synthesizes and prints the CloudFormation template for the stacks.
                                   'bootstrap': Bootstraps the CDK stack. This is needed before deployment or updating the CI.
                                   'invoke': invoke a custom command. Provide the custom command through '--command <YOUR_CUSTOM_COMMAND>'
    --command                    Custom command to invoke. Required for '--action invoke'.
EOF
}

function export_global_variables() {
  # If these variables are not set or empty, defaults are export.
  if [[ -z "${DEPLOY_ACCOUNT:+x}" ]]; then
    export DEPLOY_ACCOUNT='620771051181'
  fi
  if [[ -z "${DEPLOY_REGION:+x}" ]]; then
    export DEPLOY_REGION='us-west-2'
    export AWS_DEFAULT_REGION="${DEPLOY_REGION}"
  fi
  if [[ -z "${GITHUB_REPO_OWNER:+x}" ]]; then
    export GITHUB_REPO_OWNER='aws'
  fi
  if [[ -z "${GITHUB_SOURCE_VERSION:+x}" ]]; then
    export GITHUB_SOURCE_VERSION='main'
  fi
  # Other variables for managing resources.
#  DATE_NOW="$(date +%Y-%m-%d-%H-%M)"
  export GITHUB_REPO_NAME='aws-lc'
  export ECR_LINUX_AARCH_REPO_NAME='aws-lc-docker-images-linux-aarch'
  export ECR_LINUX_X86_REPO_NAME='aws-lc-docker-images-linux-x86'
  export ECR_WINDOWS_X86_REPO_NAME='aws-lc-docker-images-windows-x86'
  export AWS_LC_S3_BUCKET_PREFIX='aws-lc-windows-docker-image-build-s3'
  export WIN_EC2_TAG_KEY='aws-lc'
  export WIN_EC2_TAG_VALUE='aws-lc-windows-docker-image-build'
  export WIN_DOCKER_BUILD_SSM_DOCUMENT='AWSLC-BuildWindowsDockerImages'
  export S3_FOR_WIN_DOCKER_IMG_BUILD='aws-lc-windows-docker-image-build-s3'
  export MAX_TEST_RETRY=2
  export IMG_BUILD_STATUS='unknown'
  # 620771051181 and 351119683581 is AWS-LC team AWS account.
  if [[ "${DEPLOY_ACCOUNT}" != "620771051181" && "${DEPLOY_ACCOUNT}" != '351119683581' ]] && [[ "${GITHUB_REPO_OWNER}" == 'aws' ]]; then
    echo "Only team account is allowed to create CI stacks on aws repo."
    exit 1
  fi
}

function main() {
  # parse arguments.
  while [[ $# -gt 0 ]]; do
    case ${1} in
    --help)
      script_helper
      exit 0
      ;;
    --deploy-account)
      export DEPLOY_ACCOUNT="${2}"
      shift
      ;;
    --deploy-region)
      export DEPLOY_REGION="${2}"
      export AWS_DEFAULT_REGION="${DEPLOY_REGION}"
      shift
      ;;
    --pipeline-account)
      export PIPELINE_ACCOUNT="${2}"
      shift
      ;;
    --pipeline-region)
      export PIPELINE_REGION="${2}"
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
    --action)
      export ACTION="${2}"
      shift
      ;;
    --command)
      COMMAND="${2}"
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
  if [[ -z "${ACTION:+x}" ]]; then
    echo "${ACTION} is required input."
    exit 1
  fi

  # Export global variables, which provides the contexts needed by ci setup/destroy.
  export_global_variables

  # Execute the action.
  case ${ACTION} in
  deploy-production-pipeline)
    export IS_DEV="False"
    deploy_production_pipeline
    ;;
  deploy-dev-pipeline)
    export IS_DEV="True"
    deploy_dev_pipeline
    ;;
  deploy-ci)
    setup_ci
    ;;
  update-ci)
    create_github_ci_stack
    ;;
  destroy-ci)
    destroy_ci
    ;;
  update-android-resources)
    create_android_resources
    ;;
  destroy-img-stack)
    destroy_docker_img_build_stack
    ;;
  build-linux-img)
    build_linux_docker_images
    ;;
  build-win-img)
    build_win_docker_images
    ;;
  synth)
    cdk synth '*'
    ;;
  diff)
    cdk diff aws-lc-ci-*
    ;;
  bootstrap)
    cdk bootstrap
    ;;
  invoke)
    if [[ -z "${COMMAND:+x}" ]]; then
      echo "--action invoke requires a command."
      exit 1
    fi
    ${COMMAND:?}
    ;;
  *)
    echo "--action is required. Use '--help' to see allowed actions."
    exit 1
    ;;
  esac
}

# Invoke main
main "$@"
