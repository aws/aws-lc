#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

s2n-bignum-c89.h : s2n-bignum.h c89.txt ; \
        (cat c89.txt; (cat s2n-bignum.h | sed -E -f c89.sed)) >s2n-bignum-c89.h

clobber:; rm -f s2n-bignum-c89.h
