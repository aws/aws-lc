#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

export PATH="$HOME/.local/bin:$PATH"

export CLAUDE_CODE_USE_BEDROCK=1
export AWS_REGION=us-west-2

export ANTHROPIC_DEFAULT_OPUS_MODEL='us.anthropic.claude-opus-4-6-v1'
export ANTHROPIC_DEFAULT_SONNET_MODEL='us.anthropic.claude-sonnet-4-6'
export ANTHROPIC_DEFAULT_HAIKU_MODEL='us.anthropic.claude-haiku-4-5-20251001-v1:0'
export CLAUDE_MAX_TOKENS=8192
export CLAUDE_TIMEOUT=300

# Extract PR number from CODEBUILD_WEBHOOK_TRIGGER (e.g., "pr/1373")
PR_NUMBER="${CODEBUILD_WEBHOOK_TRIGGER#pr/}"
if [ -z "$PR_NUMBER" ]; then
  echo "Error: Could not determine PR number from CODEBUILD_WEBHOOK_TRIGGER"
  exit 1
fi

# Test Claude installation and Bedrock connectivity
claude --version
claude -p "Say hello!"

REPO="${GITHUB_REPO_OWNER}/${GITHUB_REPO_NAME}"
echo "Running code review for PR #${PR_NUMBER} in ${REPO}..."
REVIEW_PROMPT="$(sed -e "s/\$ARGUMENTS/${PR_NUMBER}/g" -e "s|\$REPO|${REPO}|g" review-pr.md)"
claude -p "$REVIEW_PROMPT" \
  --allowedTools "WebFetch,Read,Glob,Grep,Agent,Bash(git *)" \
  --dangerously-skip-permissions