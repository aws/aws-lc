# Copyright (C) 2009 The Android Open Source Project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
LOCAL_PATH := $(call my-dir)

include $(CLEAR_VARS)

LOCAL_MODULE    := jitterentropy
LOCAL_CFLAGS    := -O0 -DCRYPTO_CPU_JITTERENTROPY_STAT
LOCAL_SRC_FILES := jitterentropy-base.c jitterentropy-stat.c jitterentropy-foldtime.c

# compile into a shared library that can be pulled into an APK
LOCAL_STATIC_LIBRARIES := android_native_app_glue
include $(BUILD_SHARED_LIBRARY)
$(call import-module,android/native_app_glue)

# compilation of a standalone-binary that must be manually moved to
# Android /data partition for execution.
#include $(BUILD_EXECUTABLE)

# compilation of the CPU Jitter RNG app
#LOCAL_SRC_FILES := jitterentropy-base.c jitterentropy-main-user.c

