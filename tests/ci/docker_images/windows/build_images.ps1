# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

. .\common.ps1

#Invoke-Command { docker build -t aws-lc/windows-2019:base .\windows-2019_base }
Invoke-Command { docker build -t aws-lc/windows-2022:base .\windows-2022_base }
#Invoke-Command { docker build -t windows-2019:vs2015 .\windows-2019_vs2015 }
#Invoke-Command { docker build -t windows-2019:vs2017-sde .\windows-2019_vs2017-sde }
Invoke-Command { docker build -t windows-2022:vs2022-sde .\windows-2022_vs2022-sde }
Invoke-Command { docker build -t windows-2022:vs2017-sde .\windows-2022_vs2017-sde }
Invoke-Command { docker build -t windows-2022:vs2015 .\windows-2022_vs2015 }