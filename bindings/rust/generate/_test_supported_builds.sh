#!/usr/bin/env bash
set -e -x

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.

### If you need the images used by this script, you can retrieve them from ECR:
### 1) Retrieve creds from Isengard. Paste into shell.
### 2) Setup the environment:
###    $ AWS_ACCOUNT_ID=???
###    $ DOCKER_IMAGE_REPO_NAME=aws-lc-docker-images-linux-
###    $ DI_ARCH=x86
###    $ DI_TAG=ubuntu-22.04_gcc-12x_latest
###    $ DOCKER_IMAGE_HOST=${AWS_ACCOUNT_ID}.dkr.ecr.us-west-2.amazonaws.com
### 3) Login:
###    $ aws ecr get-login-password --region us-west-2 | docker login --username AWS --password-stdin ${DOCKER_IMAGE_HOST}
### 4) Pull docker images:
###    $ docker pull ${DOCKER_IMAGE_HOST}/${DOCKER_IMAGE_REPO_NAME}${DI_ARCH}:${DI_TAG}

function usage {
  echo "Usage: $(basename $0) AWS_ACCOUNT_ID "
}

if [[ ! "${1}" -gt 0  ]]; then
  usage
  exit 1
fi

AWS_ACCOUNT_ID="${1}"
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
CRATE_DIR="${TMP_DIR}"/aws-lc-sys

###
###
### Test crate on Mac
###
###
if [[ ! "${OSTYPE}" == "darwin"* ]]; then
  echo This scipt must be run on a Mac
  exit 1
fi
${SCRIPT_DIR}/_crate_test_build.sh

pushd "${AWS_LC_DIR}"

###
###
DOCKER_IMAGE_HOST=${AWS_ACCOUNT_ID}.dkr.ecr.us-west-2.amazonaws.com
DOCKER_IMAGE_REPO_NAME=aws-lc-docker-images-linux-
DI_ARCH=x86
DI_TAG=ubuntu-22.04_gcc-12x_latest
###
###
docker run -v `pwd`:`pwd` -w `pwd` --rm ${DOCKER_IMAGE_HOST}/${DOCKER_IMAGE_REPO_NAME}${DI_ARCH}:${DI_TAG} /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh

###
###
DI_ARCH=x86
DI_TAG=amazonlinux-2_clang-7x_latest
###
###
docker run -v `pwd`:`pwd` -w `pwd` --rm ${DOCKER_IMAGE_HOST}/${DOCKER_IMAGE_REPO_NAME}${DI_ARCH}:${DI_TAG} /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh

###
###
DI_ARCH=aarch
DI_TAG=ubuntu-20.04_clang-10x_latest
###
###
# TODO: The ARM64 images fail the Rust build with a strange message. I suspect it's due to Docker emulation on my Mac.
#docker run -v `pwd`:`pwd` -w `pwd` --rm ${DOCKER_IMAGE_HOST}/${DOCKER_IMAGE_REPO_NAME}${DI_ARCH}:${DI_TAG} /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh

###
###
DI_ARCH=aarch
DI_TAG=amazonlinux-2_gcc-7x_latest
###
###
# TODO: The ARM64 images fail the Rust build with a strange message. I suspect it's due to Docker emulation on my Mac.
#docker run -v `pwd`:`pwd` -w `pwd` --rm ${DOCKER_IMAGE_HOST}/${DOCKER_IMAGE_REPO_NAME}${DI_ARCH}:${DI_TAG} /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh

popd
