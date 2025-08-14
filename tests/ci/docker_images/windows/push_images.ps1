# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

. .\common.ps1

$ECS_REPO=$args[0]

if ($args[0] -eq $null) {
    # This is a ECS repository in our CI account
    $ECS_REPO="620771051181.dkr.ecr.us-west-2.amazonaws.com/aws-lc-docker-images-windows-x86"
}

Write-Host "$ECS_REPO"

Tag-And-Push-Image "windows-2022:vs2015" "${ECS_REPO}:windows-2022_vs2015"
Tag-And-Push-Image "windows-2022:vs2017" "${ECS_REPO}:windows-2022_vs2017"
Tag-And-Push-Image "windows-2022:vs2019" "${ECS_REPO}:windows-2022_vs2019"
Tag-And-Push-Image "windows-2022:vs2022" "${ECS_REPO}:windows-2022_vs2022"
