# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

$ECS_REPO=$args[0]

if ($args[0] -eq $null) {
    # This is a ECS repository in our CI account
    $ECS_REPO="620771051181.dkr.ecr.us-west-2.amazonaws.com/aws-lc-docker-images-windows-x86"
}

Write-Host "$ECS_REPO"

docker tag vs2015 ${ECS_REPO}:vs2015_latest
docker tag vs2015 ${ECS_REPO}:vs2015-$(Get-Date -UFormat %Y-%m-%d-%H)
docker push ${ECS_REPO}:vs2015_latest
docker push ${ECS_REPO}:vs2015-$(Get-Date -UFormat %Y-%m-%d-%H)

docker tag vs2017 ${ECS_REPO}:vs2017_latest
docker tag vs2017 ${ECS_REPO}:vs2017-$(Get-Date -UFormat %Y-%m-%d-%H)
docker push ${ECS_REPO}:vs2017_latest
docker push ${ECS_REPO}:vs2017-$(Get-Date -UFormat %Y-%m-%d-%H)
