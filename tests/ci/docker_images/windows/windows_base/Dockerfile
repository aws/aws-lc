# escape=`

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM mcr.microsoft.com/windows/servercore:ltsc2019

ADD https://download.microsoft.com/download/6/A/A/6AA4EDFF-645B-48C5-81CC-ED5963AEAD48/vc_redist.x64.exe /vc_redist.x64.exe
RUN start /wait C:\vc_redist.x64.exe /quiet /norestart

# Install chocolatey
# https://chocolatey.org/docs/troubleshooting#the-request-was-aborted-could-not-create-ssltls-secure-channel
RUN @powershell Set-ExecutionPolicy Bypass -Scope Process -Force; [Net.ServicePointManager]::SecurityProtocol = [Net.ServicePointManager]::SecurityProtocol -bor [Net.SecurityProtocolType]::Tls12; $env:chocolateyUseWindowsCompression = 'true'; [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; iex ((New-Object System.Net.WebClient).DownloadString('https://chocolatey.org/install.ps1'))

RUN choco install git --version 2.23.0 -y && `
choco install ninja --version 1.9.0.20190208 -y && `
choco install activeperl --version 5.24.3.2404 -y && `
choco install nasm --version 2.14.02 -y && `
choco install golang --version 1.13.1 -y && `
choco install cmake --version 3.15.4 --installargs 'ADD_CMAKE_TO_PATH=""System""' -y

CMD [ "cmd.exe" ]
