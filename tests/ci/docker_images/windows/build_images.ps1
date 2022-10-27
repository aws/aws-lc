# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

docker build -t aws-lc/windows_base:2019 .\windows_base
docker build -t vs2015 .\vs2015
docker build -t vs2017 .\vs2017
