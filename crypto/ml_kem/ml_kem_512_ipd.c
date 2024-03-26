// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// The following two lines have to be in that order, first the definition of
// KYBER_K, and then the inclusion of params.h so that the correct version
// of Kyber would be selected. KYBER_K equal to 2 corresponds to ML-KEM-512.
// Both lines also have to come before all the source files.
#define KYBER_K 2
#include "./ml_kem_ipd_ref_common/params.h"

#include "./ml_kem_ipd_ref_common/cbd.c"
#include "./ml_kem_ipd_ref_common/indcpa.c"
#include "./ml_kem_ipd_ref_common/kem.c"
#include "./ml_kem_ipd_ref_common/ntt.c"
#include "./ml_kem_ipd_ref_common/poly.c"
#include "./ml_kem_ipd_ref_common/polyvec.c"
#include "./ml_kem_ipd_ref_common/reduce.c"
#include "./ml_kem_ipd_ref_common/symmetric-shake.c"
#include "./ml_kem_ipd_ref_common/verify.c"
