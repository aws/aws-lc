// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


#define DILITHIUM_MODE 3

#include "./pqcrystals_dilithium_ref_common/config.h"
#include "./pqcrystals_dilithium_ref_common/fips202.h"
#include "./pqcrystals_dilithium_ref_common/ntt.h"
#include "./pqcrystals_dilithium_ref_common/packing.h"
#include "./pqcrystals_dilithium_ref_common/poly.h"
#include "./pqcrystals_dilithium_ref_common/polyvec.h"
#include "./pqcrystals_dilithium_ref_common/reduce.h"
#include "./pqcrystals_dilithium_ref_common/rounding.h"
#include "./pqcrystals_dilithium_ref_common/sign.h"
#include "./pqcrystals_dilithium_ref_common/symmetric.h"

#include "./pqcrystals_dilithium_ref_common/fips202.c"
#include "./pqcrystals_dilithium_ref_common/ntt.c"
#include "./pqcrystals_dilithium_ref_common/packing.c"
#include "./pqcrystals_dilithium_ref_common/poly.c"
#include "./pqcrystals_dilithium_ref_common/polyvec.c"
#include "./pqcrystals_dilithium_ref_common/reduce.c"
#include "./pqcrystals_dilithium_ref_common/rounding.c"
#include "./pqcrystals_dilithium_ref_common/sign.c"
#include "./pqcrystals_dilithium_ref_common/symmetric-shake.c"
