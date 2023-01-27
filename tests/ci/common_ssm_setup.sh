# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

#$1 is the prefix for the ssm document, echos the doc name so we can capture the output
create_ssm_document() {
  local doc_name
  doc_name="$1"_ssm_document_"${CODEBUILD_SOURCE_VERSION}"
  aws ssm create-document --content file://tests/ci/cdk/cdk/ssm/"$1"_ssm_document.yaml \
    --name "${doc_name}" \
    --document-type Command \
    --document-format YAML >/dev/null
  echo "${doc_name}"
}

#$1 is the document name, $2 is the instance ids, $3 is the cloudwatch log group name.
function run_ssm_command() {
  local command_id
  command_id="$(aws ssm send-command --instance-ids "${2}" \
    --document-name "${1}" \
    --cloud-watch-output-config CloudWatchLogGroupName="${3}",CloudWatchOutputEnabled=true \
    --query Command.CommandId --output text)"
  echo "${command_id}"
}
