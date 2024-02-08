#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

# This test reports on common style mistakes.

# Test 1: Check for headers without #pragma once
# - Ignore third party libraries
# - Ignore the file md32_common.h which is included several times in different
#   contexts (TODO:Fix this)
# - If the last grep did not match any file (success) it returns an error code
#   that terminates the script. We avoid this by adding the final '|| true'
HEADERS_WITHOUT_PRAGMA=`find . -type f -name "*.h" | grep -v third_party | 
	                grep -v md32_common.h | xargs grep -L "pragma once" ||
                        true`
if [ ! -z "$HEADERS_WITHOUT_PRAGMA" ] ; then
  echo "The following headers do not contain the 'pragma once' guard:
        $HEADERS_WITHOUT_PRAGMA"
  # TODO: re-enable "#pragma once" when CI is active.
  # exit -1
fi

