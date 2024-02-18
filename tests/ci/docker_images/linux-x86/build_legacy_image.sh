#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

if [ -n "$1" ]; then
  docker_name="$1"
else
  docker_name='ubuntu-10.04_gcc-4.1x'
fi

mkdir -p ${docker_name}/dependencies
cd ${docker_name}/dependencies

# The wget version that comes with this docker image is too old to
# download the cmake version from source, so we predownload the 
# dependencies outside of the image and pull it in the container.
wget -O cmake-3.9.6.tar.gz https://cmake.org/files/v3.9/cmake-3.9.6.tar.gz
cd ..
sudo docker build -t ubuntu-10.04_gcc-4.1x .

sudo rm -rf dependencies
cd ..
