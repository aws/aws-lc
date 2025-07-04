# escape=`

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM mcr.microsoft.com/windows/servercore:ltsc2022

ADD https://download.microsoft.com/download/6/A/A/6AA4EDFF-645B-48C5-81CC-ED5963AEAD48/vc_redist.x64.exe /vc_redist.x64.exe
RUN start /wait C:\vc_redist.x64.exe /quiet /norestart

# Install chocolatey
# https://stackoverflow.com/questions/76470752/chocolatey-installation-in-docker-started-to-fail-restart-due-to-net-framework
ENV chocolateyVersion=1.4.0
# https://chocolatey.org/docs/troubleshooting#the-request-was-aborted-could-not-create-ssltls-secure-channel
RUN @powershell Set-ExecutionPolicy Bypass -Scope Process -Force; [Net.ServicePointManager]::SecurityProtocol = [Net.ServicePointManager]::SecurityProtocol -bor [Net.SecurityProtocolType]::Tls12; $env:chocolateyUseWindowsCompression = 'true'; [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; iex ((New-Object System.Net.WebClient).DownloadString('https://chocolatey.org/install.ps1'))

RUN choco install git --version 2.23.0 -y && `
choco install 7zip.install -y && `
choco install ninja --version 1.9.0.20190208 -y && `
choco install strawberryperl --version 5.32.0.1 -y && `
choco install nasm --version 2.14.02 -y && `
choco install golang --version 1.20.1 -y && `
choco install cmake --version 3.15.4 --installargs 'ADD_CMAKE_TO_PATH=""System""' -y

# Remove Strawberryperl's GCC from path because it override's MSVC's C.
RUN setx /M PATH "%PATH:C:\Strawberry\c\bin;=%"

CMD [ "cmd.exe" ]
