#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

.PHONY: clean ctCheck

# Set ARCH to "x86" or "arm" as appropriate; this is literally the
# directory name in which the libs2nbignum.a file should be found.
# If this block fails to do it automatically, replace with manual
# setting: ARCH=x86 or ARCH=arm as appropriate

ARCH=unknown_architecture
VALGRIND=valgrind --

UNAME_RESULT=$(shell uname -m)

ifeq ($(UNAME_RESULT),x86_64)
ARCH=x86
# Enabling valgrind makes test unable to detect BMI/ADX
VALGRIND=
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
#
# "complete" runs all tests regardless of architecture including
# the known value tests, doing no filtering of output and giving a
# return code.

default: test ctCheck;

go: test; ./test +100 | grep -v OK

complete: test ctCheck; $(VALGRIND) ./test +500

test: test.c known_value_tests_p384.h tweetnacl_excerpt.c ../include/s2n-bignum.h ../$(ARCH)/libs2nbignum.a; gcc -Wall -std=gnu99 -o test test.c -L../$(ARCH) -ls2nbignum

clean: ;
	rm -f test
	rm -f ctCheck

ctCheck:
	rm -f ctCheck
	for f in `find ../$(ARCH)/p* ../$(ARCH)/secp* -name '*.o' | grep -v bignum_inv_p | grep -v bignum_montinv_p | grep -v _scalarmul | grep -v _montjscalarmul | grep -v _jscalarmul`; do trimmed=`echo $$f | tr -d .`; objdump -d --no-show-raw-insn $$f | grep '^[ \t]' | cut -f2 -d: -s | awk "{print \"$$trimmed: \" \$$1}" | grep -v -f ../non_ct_functions.txt |  grep -v -f ../$(ARCH)/allowed_asm >> ctCheck && echo FAIL >> ctCheck; done || true
	! grep FAIL ctCheck
