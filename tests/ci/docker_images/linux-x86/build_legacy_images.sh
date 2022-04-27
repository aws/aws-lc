#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

if [ -n "$1" ]; then
  docker_name="$1"
else
  docker_name='ubuntu-7.10_gcc-4.1x'
fi

# `ubuntu-7.10-gutsy_gcc-4.1x` was rebuilt from an iso image
# from: https://old-releases.ubuntu.com/releases/gutsy/
# The docker tar file is checked into our team account.
# Must be logged into team account to access docker tar file.
mkdir -p ${docker_name}/dependencies
cd ${docker_name}/dependencies
aws s3 cp s3://ubuntu-7.10-gutsy-gcc-4.1x/ubuntu-7.10-gutsy_gcc-4.1x.tar ${docker_name}.tar
docker load --input ${docker_name}.tar
# The wget version that comes with this docker image is too old to
# download the cmake version from source, so we predownload the 
# dependencies outside of the image and pull it in the container.
wget -O cmake-2.8.12.tar.gz https://cmake.org/files/v2.8/cmake-2.8.12.tar.gz
cd ..
docker build -t ubuntu-7.10:gcc-4.1x .
rm -rf dependencies
cd ..
