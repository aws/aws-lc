# escape=`

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Keep parity with the upstream tags at https://hub.docker.com/_/microsoft-windows-servercore
FROM aws-lc/windows-2022:base

SHELL ["cmd", "/S", "/C"]
RUN `
    # Download the Build Tools bootstrapper.
    curl -SL --output vs_buildtools.exe https://aka.ms/vs/15/release/vs_buildtools.exe `
    `
    # Install Build Tools. Build Tools for MSVC2015 are not directly downloadable without a Visual Studio
    # subscription, so we'll need to download MSVC2017 and add the MSVC2015 (VC.140) component available to
    # download with it.
    # Reference: https://docs.microsoft.com/en-us/previous-versions/visualstudio/visual-studio-2017/install/workload-component-id-vs-build-tools?view=vs-2017
    && (start /w vs_buildtools.exe --quiet --wait --norestart --nocache `
        --add Microsoft.VisualStudio.Component.VC.CLI.Support `
        --add Microsoft.VisualStudio.Component.VC.140 `
        --add Microsoft.VisualStudio.Component.VC.CMake.Project `
        || IF "%ERRORLEVEL%"=="3010" EXIT 0) `
    `
    # Cleanup
    && del /q vs_buildtools.exe

# Add msbuild and cl to PATH
RUN setx /M PATH "%PATH%;C:\Program Files (x86)\MSBuild\14.0\bin;C:\Program Files (x86)\Microsoft Visual Studio 14.0\VC\bin"

# Dynamically get the installed SDK version
RUN for /f "tokens=*" %a in ('dir /b /ad "C:\Program Files (x86)\Windows Kits\10\Include\10.0*"') do setx /M SDKVERSION %a

# Replace Windows SDK with the correct binary path. vcvarsall.bat for MSVC2015 does not account for the nested directory
RUN rmdir /s /Q "C:\Program Files (x86)\Windows Kits\10\bin\x64" && `
    rmdir /s /Q "C:\Program Files (x86)\Windows Kits\10\bin\x86" && `
    move "C:\Program Files (x86)\Windows Kits\10\bin\%SDKVERSION%\x64" "C:\Program Files (x86)\Windows Kits\10\bin" && `
    move "C:\Program Files (x86)\Windows Kits\10\bin\%SDKVERSION%\x86" "C:\Program Files (x86)\Windows Kits\10\bin"

CMD [ "cmd.exe" ]
