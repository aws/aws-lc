# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Keep parity with the upstream tags at https://hub.docker.com/_/microsoft-windows-servercore
FROM aws-lc/windows_base:2019

# Install Visual C++ Build Tools, as per: https://chocolatey.org/packages/visualcpp-build-tools
RUN choco install visualcpp-build-tools -version 14.0.25420.1 -y

# Add msbuild and cl to PATH
RUN setx /M PATH "%PATH%;C:\Program Files (x86)\MSBuild\14.0\bin;C:\Program Files (x86)\Microsoft Visual Studio 14.0\VC\bin"

CMD [ "cmd.exe" ]
