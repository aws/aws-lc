#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

export PATH="$HOME/.local/bin:$PATH"

# Install Claude
curl -fsSL https://claude.ai/install.sh | bash
mkdir -p ~/.local/bin
mkdir -p /home/codebuild-user/.local/bin

export CLAUDE_CODE_USE_BEDROCK=1
export AWS_REGION=us-west-2

export ANTHROPIC_DEFAULT_OPUS_MODEL='us.anthropic.claude-opus-4-6-v1'
export ANTHROPIC_DEFAULT_SONNET_MODEL='us.anthropic.claude-sonnet-4-6'
export ANTHROPIC_DEFAULT_HAIKU_MODEL='us.anthropic.claude-haiku-4-5-20251001-v1:0'

if [ ! -d "$CODEBUILD_SRC_DIR" ]; then
  echo "Error: CODEBUILD_SRC_DIR ('$CODEBUILD_SRC_DIR') does not exist"
  exit 1
fi

# Extract PR number from CODEBUILD_WEBHOOK_TRIGGER (e.g., "pr/1373")
PR_NUMBER="${CODEBUILD_WEBHOOK_TRIGGER#pr/}"
if [ -z "$PR_NUMBER" ]; then
  echo "Error: Could not determine PR number from CODEBUILD_WEBHOOK_TRIGGER"
  exit 1
fi

# Test Claude installation and Bedrock connectivity
claude --version
claude -p "Say hello!"

# Fetch PR data
REPO="${GITHUB_REPO_OWNER}/${GITHUB_REPO_NAME}"
PR_DATA_DIR="${CODEBUILD_SRC_DIR}/.pr-data"
mkdir -p "${PR_DATA_DIR}"

echo "Fetching PR #${PR_NUMBER} data from ${REPO}..."
curl -sfL "https://api.github.com/repos/${REPO}/pulls/${PR_NUMBER}" -o "${PR_DATA_DIR}/pr-metadata.json"
curl -sfL "https://github.com/${REPO}/pull/${PR_NUMBER}.diff" -o "${PR_DATA_DIR}/pr.diff"
curl -sfL "https://api.github.com/repos/${REPO}/pulls/${PR_NUMBER}/files" -o "${PR_DATA_DIR}/pr-files.json"

# Run code review
echo "Running code review for PR #${PR_NUMBER} in ${REPO}..."
timeout 1200 claude -p "Read review-pr.md and then proceed to review PR #${PR_NUMBER}. The repository is cloned in ${CODEBUILD_SRC_DIR}. PR data has been pre-fetched to ${PR_DATA_DIR}/" \
  --allowedTools "WebFetch,Read,Glob,Grep,Agent,Bash(git *)" && rc=0 || rc=$?
if [ $rc -eq 124 ]; then
  echo "Error: Claude code review timed out after 1200 seconds for PR #${PR_NUMBER}"
  exit 1
elif [ $rc -ne 0 ]; then
  exit $rc
fi
