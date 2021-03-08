#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Note: this file is reserved for pulling Docker images from 'docker.pkg.github.com', which needs external credential.
# Pull Docker images used by https://github.com/awslabs/aws-c-cal
# These Docker images are hosted in 'docker.pkg.github.com', which needs GitHub personal access token.
cur_dir="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=./common.sh
source "${cur_dir}/common.sh"
# shellcheck source=./aws-crt/aws-crt-common.sh
source "${cur_dir}/aws-crt/aws-crt-common.sh"
login_github_docker_pkg
pull_aws_crt_docker_img
