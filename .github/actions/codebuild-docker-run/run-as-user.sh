#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Usage: run-as-user.sh USER COMMAND
# Run COMMAND in bash as USER, with HOME=/home/USER and the caller's PATH.

set -ex

user=$1
mkdir -p "/home/${user}"
chown -R "${user}:${user}" "/home/${user}"

export RUN_AS_HOME="/home/${user}" RUN_AS_PATH="${PATH}" RUN_AS_COMMAND=$2
exec su -p -s /bin/bash "${user}" -c 'set -ex
export HOME="${RUN_AS_HOME}" PATH="${RUN_AS_PATH}"
unset RUN_AS_HOME RUN_AS_PATH
eval "${RUN_AS_COMMAND}"'
