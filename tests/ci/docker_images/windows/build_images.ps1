# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

. .\common.ps1

Invoke-Command { docker build -t aws-lc/windows_base:2022 .\windows_base }
Invoke-Command { docker build -t vs2015 .\vs2015 }
Invoke-Command { docker build -t vs2017 .\vs2017 }