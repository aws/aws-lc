# escape=`

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Keep parity with the upstream tags at https://hub.docker.com/_/microsoft-windows-servercore
FROM aws-lc/windows_base:2019

ENV SDE_VERSION_TAG=sde-external-9.44.0-2024-08-22-win
ENV SDE_MIRROR_URL="https://downloadmirror.intel.com/831748/sde-external-9.44.0-2024-08-22-win.tar.xz"

SHELL ["cmd", "/S", "/C"]
RUN `
    # Download the Build Tools bootstrapper.
    curl -SL --output vs_buildtools.exe https://aka.ms/vs/15/release/vs_buildtools.exe `
    `
    # Install MSVC2017 Build Tools.
    # Reference: https://docs.microsoft.com/en-us/previous-versions/visualstudio/visual-studio-2017/install/workload-component-id-vs-build-tools?view=vs-2017
    && (start /w vs_buildtools.exe --quiet --wait --norestart --nocache `
        --add Microsoft.VisualStudio.Workload.VCTools `
        --add Microsoft.VisualStudio.Component.VC.CLI.Support `
        --add Microsoft.VisualStudio.Component.VC.CMake.Project `
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

RUN setx /M PATH "%PATH%;C:\Program Files (x86)\Microsoft Visual Studio\2017\BuildTools\MSBuild\15.0\Bin"

RUN setx /M SDEROOT C:/windows-sde

CMD [ "cmd.exe" ]
