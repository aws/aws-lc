#!/bin/bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -exuo pipefail

# -e: Exit on any failure
# -x: Print the command before running
# -u: Any variable that is not set will cause an error if used
# -o pipefail: Makes sure to exit a pipeline with a non-zero error code if any command in the pipeline exists with a
#              non-zero error code.

export ACTION=$1
shift

# Functions
function deploy() {
    cdk deploy WebhookStack FuzzingStack ReportStack --require-approval never
}

function destroy() {
    cdk destroy WebhookStack FuzzingStack ReportStack --force
}

# Main logics

case ${ACTION} in
DEPLOY)
  deploy
  ;;
DIFF)
  cdk diff
  ;;
SYNTH)
  cdk synth
  ;;
DESTROY)
  destroy
  ;;
*)
  echo "Action: ${ACTION} is not supported."
  ;;
esac

exit 0
