#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
#
#  http://aws.amazon.com/apache2.0
#
# or in the "LICENSE" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
#############################################################################

# Set ARCH to "x86" or "arm" as appropriate; this is literally the
# directory name in which the libs2nbignum.a file should be found.
# If this block fails to do it automatically, replace with manual
# setting: ARCH=x86 or ARCH=arm as appropriate

.PHONY: clean ctCheck

ARCH=unknown_architecture

UNAME_RESULT=$(shell uname -m)

ifeq ($(UNAME_RESULT),x86_64)
ARCH=x86
endif

ifeq ($(UNAME_RESULT),aarch64)
ARCH=arm
endif

ifeq ($(UNAME_RESULT),arm64)
ARCH=arm
endif

# Build the test program "test". This can then be invoked, optionally
# with a parameter with the number of tests per function, e.g.
#
#   ./test 10
#
# The "go" target runs it with 100 tests per function and filters
# most of the "good result" output to leave the summary and errors

default: test ctCheck;

go: test; ./test 100 | grep -v OK

test: test.c ../include/s2n-bignum.h ../$(ARCH)/libs2nbignum.a; gcc -Wall -std=gnu99 -o test test.c -L../$(ARCH) -ls2nbignum

clean: ;
	rm -f test
	rm -f ctCheck

ctCheck:
	rm -f ctCheck
	for f in `find ../$(ARCH)/p* -name '*.o'`; do trimmed=`echo $$f | tr -d .`; objdump -d $$f | cut -f3 -s | awk "{print \"$$trimmed: \" \$$1}" | grep -v -f ../non_ct_functions.txt |  grep -v -f ../$(ARCH)/allowed_asm >> ctCheck && echo FAIL >> ctCheck; done || true
	! grep FAIL ctCheck
