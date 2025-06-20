# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC


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