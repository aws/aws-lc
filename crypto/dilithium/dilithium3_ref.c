// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


#define DILITHIUM_MODE 3

#include "./pqcrystals-dilithium_dilithium_common/aes256ctr.h"
#include "./pqcrystals-dilithium_dilithium_common/config.h"
#include "./pqcrystals-dilithium_dilithium_common/fips202.h"
#include "./pqcrystals-dilithium_dilithium_common/ntt.h"
#include "./pqcrystals-dilithium_dilithium_common/packing.h"
#include "./pqcrystals-dilithium_dilithium_common/poly.h"
#include "./pqcrystals-dilithium_dilithium_common/polyvec.h"
#include "./pqcrystals-dilithium_dilithium_common/reduce.h"
#include "./pqcrystals-dilithium_dilithium_common/rounding.h"
#include "./pqcrystals-dilithium_dilithium_common/sign.h"
#include "./pqcrystals-dilithium_dilithium_common/symmetric.h"

#include "./pqcrystals-dilithium_dilithium_common/aes256ctr.c"
#include "./pqcrystals-dilithium_dilithium_common/fips202.c"
#include "./pqcrystals-dilithium_dilithium_common/ntt.c"
#include "./pqcrystals-dilithium_dilithium_common/packing.c"
#include "./pqcrystals-dilithium_dilithium_common/poly.c"
#include "./pqcrystals-dilithium_dilithium_common/polyvec.c"
#include "./pqcrystals-dilithium_dilithium_common/reduce.c"
#include "./pqcrystals-dilithium_dilithium_common/rounding.c"
#include "./pqcrystals-dilithium_dilithium_common/sign.c"
#include "./pqcrystals-dilithium_dilithium_common/symmetric-shake.c"
