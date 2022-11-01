/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

#define SELECT_FN   1
#define BEEU        1

#ifdef SELECT_FN
void select_w5(uint64_t* restrict val, uint64_t* restrict in_t, uint32_t index);

void select_w7(uint64_t* restrict val, uint64_t* restrict in_t, uint32_t index);
#endif

#ifdef BEEU
int beeu_mod_inverse_vartime(uint64_t out[4], const uint64_t a[4], const uint64_t n[4]);
#endif
