# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

$TAG_SUFFIX = if (-not [string]::IsNullOrEmpty($TRIGGER_TYPE) -and $TRIGGER_TYPE -eq "pipeline") {
  "pending"
} else {
  "latest"
}

Function Invoke-Command {
  [cmdletbinding()]
  Param (
    $Command
  )
  Process {
    echo $Command
    & $Command
    $ExitCode = $LASTEXITCODE
    if ($ExitCode -gt 0){
      throw "Command '$Command' exited with code $ExitCode"
    }
  }
}

Function Tag-And-Push-Image {
  [cmdletbinding()]
  Param (
    $Source,
    $Target
  )
  Process {
    $DockerImageWithTag = "${Target}_${TAG_SUFFIX}"
    $DockerImageWithDate = "${Target}-$(Get-Date -UFormat %Y-%m-%d-%H)"

    Invoke-Command { docker tag ${Source} ${DockerImageWithTag} }
    Invoke-Command { docker tag ${Source} ${DockerImageWithDate} }
    Invoke-Command { docker push ${DockerImageWithTag} }
    Invoke-Command { docker push ${DockerImageWithDate} }
  }
}