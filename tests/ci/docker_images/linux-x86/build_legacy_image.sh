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
mkdir -p ${docker_name}/dependencies
cd ${docker_name}/dependencies
# Download ubuntu-7.10 iso image from the official website and 
# create docker image from it using squashfs-tools.
sudo apt-get update && sudo apt-get -y --no-install-recommends install squashfs-tools
wget -O ubuntu-7.10-desktop-amd64.iso http://old-releases.ubuntu.com/releases/gutsy/ubuntu-7.10-desktop-amd64.iso
mkdir -p rootfs unquashfs
sudo mount -o loop ubuntu-7.10-desktop-amd64.iso rootfs
find . -type f | grep filesystem.squashfs
sudo unsquashfs -f -d unsquashfs/ rootfs/casper/filesystem.squashfs
sudo tar -C unsquashfs -c . | docker import - ${docker_name}

# The wget version that comes with this docker image is too old to
# download the cmake version from source, so we predownload the 
# dependencies outside of the image and pull it in the container.
wget -O cmake-2.8.12.tar.gz https://cmake.org/files/v2.8/cmake-2.8.12.tar.gz
cd ..
sudo docker build -t ubuntu-7.10:gcc-4.1x .

# Remove installed dependencies to build the image.
sudo umount -f dependencies/rootfs
sudo apt-get --purge remove -y squashfs-tools
sudo rm -rf dependencies
cd ..
