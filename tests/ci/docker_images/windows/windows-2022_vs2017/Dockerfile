# escape=`

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Keep parity with the upstream tags at https://hub.docker.com/_/microsoft-windows-servercore
FROM aws-lc/windows-2022:base

# SDE pins come from .github/docker_images/dependencies.env, passed through as
# --build-arg by build_images.ps1. No defaults: a build that does not provide
# them fails below rather than drifting from the pinned versions.
ARG SDE_VERSION_TAG
ARG SDE_MIRROR_URL
ARG SDE_SHA256

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
    # Fail fast if the SDE pins were not passed as build args.
    (if "%SDE_VERSION_TAG%"=="" exit 1) `
    && (if "%SDE_SHA256%"=="" exit 1) `
    `
    # Install Windows Intel SDE.
    && curl -SL --output temp.tar.xz %SDE_MIRROR_URL% `
    `
    # Verify the pinned checksum before extracting.
    && (certutil -hashfile temp.tar.xz SHA256 | findstr /i /c:"%SDE_SHA256%") `
    && 7z x temp.tar.xz `
    && 7z x temp.tar `
    && ren %SDE_VERSION_TAG% windows-sde `
    && del temp.tar.xz `
    && del temp.tar

RUN setx /M PATH "%PATH%;C:\Program Files (x86)\Microsoft Visual Studio\2017\BuildTools\MSBuild\15.0\Bin"

RUN setx /M SDEROOT C:/windows-sde

CMD [ "cmd.exe" ]
