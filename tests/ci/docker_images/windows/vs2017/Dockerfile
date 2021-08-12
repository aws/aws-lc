# escape=`

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Keep parity with the upstream tags at https://hub.docker.com/_/microsoft-windows-servercore
FROM aws-lc/windows_base:2019

# Install Visual C++ Build Tools, as per: https://chocolatey.org/packages/visualcpp-build-tools
RUN powershell -NoProfile -InputFormat None -Command `
    choco install visualcpp-build-tools -version 15.0.26228.20170424 -y; `
    Write-Host 'Waiting for Visual C++ Build Tools to finish'; `
    Wait-Process -Name vs_installer

RUN setx /M PATH "%PATH%;C:\Program Files (x86)\Microsoft Visual Studio\2017\BuildTools\MSBuild\15.0\Bin"

CMD [ "cmd.exe" ]
