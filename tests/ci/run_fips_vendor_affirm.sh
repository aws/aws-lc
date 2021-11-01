#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

# FIPS_OE_IMAGE is the Docker image used to test AWS-LC FIPS builds.
if [[ -z "${FIPS_OE_IMAGE+x}" || -z "${FIPS_OE_IMAGE}" ]]; then
  echo "FIPS_OE_IMAGE is not defined or empty. Use default value."
  FIPS_OE_IMAGE='620771051181.dkr.ecr.us-west-2.amazonaws.com/aws-lc-docker-images-linux-x86:amazonlinux-2_gcc-7x_latest'
fi

# OLD_LINUX_IMAGE is the old Linux platforms that AWS-LC FIPS vendor affirm is developed to support.
if [[ -z "${OLD_LINUX_IMAGE+x}" || -z "${OLD_LINUX_IMAGE}" ]]; then
  echo "OLD_LINUX_IMAGE is not defined or empty. Use default value."
  OLD_LINUX_IMAGE='620771051181.dkr.ecr.us-west-2.amazonaws.com/aws-lc-docker-images-linux-x86:centos-7_gcc-4x_latest'
fi

# Pull the two Docker images.
docker pull ${FIPS_OE_IMAGE}
docker pull ${OLD_LINUX_IMAGE}

# Generate bcm.o by running FIPS build on |FIPS_OE_IMAGE|.
echo "Testing AWS-LC in FIPS Release and DISABLE_GETAUXVAL mode."
docker run --privileged -v `pwd`:`pwd` \
  -w `pwd` ${FIPS_OE_IMAGE} ./tests/ci/run_fips_module_generation.sh

# The bcm.o is generated under |BCM_O_UNDER_BUILD_ROOT|.
BCM_O_UNDER_BUILD_ROOT="${BUILD_ROOT}/crypto/fipsmodule/bcm.o"
ensure_file ${BCM_O_UNDER_BUILD_ROOT}

# Copy the bcm.o to |SRC_ROOT| because |BUILD_ROOT| is deleted before each build.
cp "${BCM_O_UNDER_BUILD_ROOT}" "${SRC_ROOT}"
BCM_O_UNDER_SRC_ROOT="${SRC_ROOT}/bcm.o"
ensure_file ${BCM_O_UNDER_SRC_ROOT}

# Run FIPS build with the built bcm.o on |OLD_LINUX_IMAGE|.
docker run --privileged -v `pwd`:`pwd` \
  -e BCM_O_UNDER_SRC_ROOT="${BCM_O_UNDER_SRC_ROOT}" \
  -w `pwd` ${OLD_LINUX_IMAGE} ./tests/ci/run_build_with_fips_module.sh
