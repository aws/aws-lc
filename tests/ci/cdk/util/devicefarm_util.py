#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

from util.env_util import EnvUtil

# Used for AWS Device Farm python kick off script.
ANDROID_APK = EnvUtil.get("ANDROID_APK", None)
ANDROID_TEST_APK = EnvUtil.get("ANDROID_TEST_APK", None)
DEVICEFARM_PROJECT = EnvUtil.get("DEVICEFARM_PROJECT", None)
DEVICEFARM_DEVICE_POOL = EnvUtil.get("DEVICEFARM_DEVICE_POOL", None)
ANDROID_TEST_NAME = EnvUtil.get("ANDROID_TEST_NAME", "AWS-LC Android Test")
AWS_REGION = EnvUtil.get("AWS_REGION", None)
