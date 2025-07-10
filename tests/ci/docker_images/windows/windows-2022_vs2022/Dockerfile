# escape=`

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Keep parity with the upstream tags at https://hub.docker.com/_/microsoft-windows-servercore
FROM aws-lc/windows-2022:base

ENV SDE_VERSION_TAG=sde-external-9.44.0-2024-08-22-win
ENV SDE_MIRROR_URL="https://downloadmirror.intel.com/831748/sde-external-9.44.0-2024-08-22-win.tar.xz"

SHELL ["cmd", "/S", "/C"]
RUN `
    # Download the Build Tools bootstrapper.
    curl -SL --output vs_buildtools.exe https://aka.ms/vs/17/release/vs_buildtools.exe `
    `
    # Install MSVC2022 Build Tools with Windows SDK
    && (start /w vs_buildtools.exe --quiet --wait --norestart --nocache `
        --add Microsoft.VisualStudio.Workload.VCTools `
        --add Microsoft.VisualStudio.Component.VC.CLI.Support `
        --add Microsoft.VisualStudio.Component.VC.CMake.Project `
        --add Microsoft.VisualStudio.Component.Windows10SDK.19041 `
        --add Microsoft.VisualStudio.Component.VC.Tools.x86.x64 `
        || IF "%ERRORLEVEL%"=="3010" EXIT 0) `
    `
    # Cleanup
    && del /q vs_buildtools.exe

RUN `
    # Install Windows Intel SDE.
    curl -SL --output temp.tar.xz %SDE_MIRROR_URL% `
    `
    && 7z x temp.tar.xz `
    && 7z x temp.tar `
    && ren %SDE_VERSION_TAG% windows-sde `
    && del temp.tar.xz `
    && del temp.tar

# Add MSBuild and Windows SDK tools to PATH
RUN setx /M PATH "%PATH%;C:\Program Files (x86)\Microsoft Visual Studio\2022\BuildTools\MSBuild\17.0\Bin"

RUN setx /M SDEROOT C:/windows-sde

CMD [ "cmd.exe" ]
