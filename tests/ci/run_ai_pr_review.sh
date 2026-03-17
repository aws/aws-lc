#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

export PATH="$HOME/.local/bin:$PATH"
export GH_CONFIG_DIR="$HOME/.config/gh"
mkdir -p "$GH_CONFIG_DIR"

export CLAUDE_CODE_USE_BEDROCK=1
export AWS_REGION=us-west-2

export ANTHROPIC_DEFAULT_OPUS_MODEL='us.anthropic.claude-opus-4-6-v1'
export ANTHROPIC_DEFAULT_SONNET_MODEL='us.anthropic.claude-sonnet-4-6'
export ANTHROPIC_DEFAULT_HAIKU_MODEL='us.anthropic.claude-haiku-4-5-20251001-v1:0'
export CLAUDE_MAX_TOKENS=8192
export CLAUDE_TIMEOUT=300

if [ -n "$GITHUB_PAT" ]; then
  echo $GITHUB_PAT | gh auth login --with-token
else
  echo "Error: GITHUB_PAT not found"
  exit 1
fi

# Test Claude installation and Bedrock connectivity
claude --version
claude -p "Say hello!"
echo "Installing Code Review plugin..."
claude plugin marketplace add anthropics/claude-code
claude plugin install code-review@claude-code-plugins

REPO_CONTEXT=""
if [ -n "$REPO" ]; then
  REPO_CONTEXT=" The PR is in the GitHub repository $GITHUB_REPO_OWNER/$GITHUB_REPO_NAME."
fi

echo "Running code review tool..."
claude -p "/code-review:code-review${REPO_CONTEXT}. At the end print the complete list of every issue found with full descriptions." \
  --dangerously-skip-permissions