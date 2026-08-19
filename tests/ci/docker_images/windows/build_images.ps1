# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

. .\common.ps1

# Load the pinned versions/URLs/checksums of externally-hosted dependencies
# (Intel SDE) and pass them to the images that need them as build args.
$Deps = @{}
Get-Content (Join-Path $PSScriptRoot "..\..\..\..\.github\docker_images\dependencies.env") | ForEach-Object {
    if ($_ -match '^([A-Za-z_][A-Za-z0-9_]*)=(.*)$') { $Deps[$Matches[1]] = $Matches[2] }
}
$SdeBuildArgs = @(
    "--build-arg", "SDE_VERSION_TAG=$($Deps['SDE_VERSION_TAG_WIN'])",
    "--build-arg", "SDE_MIRROR_URL=$($Deps['SDE_MIRROR_URL_WIN'])",
    "--build-arg", "SDE_SHA256=$($Deps['SDE_SHA256_WIN'])"
)

Invoke-Command { docker build -t aws-lc/windows-2022:base .\windows-2022_base }
Invoke-Command { docker build -t windows-2022:vs2015 .\windows-2022_vs2015 }
Invoke-Command { docker build -t windows-2022:vs2017 @SdeBuildArgs .\windows-2022_vs2017 }
Invoke-Command { docker build -t windows-2022:vs2019 .\windows-2022_vs2019 }
Invoke-Command { docker build -t windows-2022:vs2022 @SdeBuildArgs .\windows-2022_vs2022 }
