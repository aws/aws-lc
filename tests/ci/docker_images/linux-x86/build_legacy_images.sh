#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# `ubuntu-7.10-root.tar.xz` was taken from an unofficial 
# repo: https://github.com/iComputer7/ancient-ubuntu-docker.
# The file is predownloaded and checked in along with our CI 
# docker images to prevent us from not being able to download
# the file if the repo is deleted.

# The wget version that comes with this docker image is too old to
# download the cmake version from source, so we predownload the 
# dependencies outside of the image and pull it in the container.
# docker load --input ubuntu-7.04-gcc-4.1.2.tar
wget -O ubuntu-7.10_gcc-4.1x/cmake-2.8.12.tar.gz https://cmake.org/files/v2.8/cmake-2.8.12.tar.gz
docker build -t ubuntu-7.10:gcc-4.1x ubuntu-7.10_gcc-4.1x
