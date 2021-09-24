// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// All the PQ KEMs define the size of the following parameters:
//   - private key
//   - public key
//   - shared secret
//   - ciphertext.
// Since the KEM implementations use the same macro name for these,
// we define macros wih KEM specific names in this file. The values
// are copied from the corresponding KEM implementation.
// -----------------------------------------------------------------------------
#ifndef AWSLC_PQ_KEM_PARAMS_SIZE_H
#define AWSLC_PQ_KEM_PARAMS_SIZE_H

// SIKE P434 Round-3 parameters size, copied from file sike_r3/P434/P434_api.h
#define SIKE_P434_R3_PRIVATE_KEY_BYTES    (374)
#define SIKE_P434_R3_PUBLIC_KEY_BYTES     (330)
#define SIKE_P434_R3_SHARED_SECRET_BYTES  (16)
#define SIKE_P434_R3_CIPHERTEXT_BYTES     (346)

#endif  // AWSLC_PQ_KEM_PARAMS_SIZE_H
