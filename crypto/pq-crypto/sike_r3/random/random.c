// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// This file has been changed from the original implementation of SIKE to
// replace SIKE's randomness generation with a call to AWS-LC |RAND_bytes|.
// -----------------------------------------------------------------------------

#include "random.h"
#include "openssl/rand.h"

int randombytes(unsigned char* random_array, unsigned long long nbytes)
{
  return RAND_bytes(random_array, nbytes);
}
