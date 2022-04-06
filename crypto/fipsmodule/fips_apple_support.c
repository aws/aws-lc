/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------------------
*/

// The FIPS build on macOS/iOS is different than the build on Linux.
// Apple's linker doesn't support linker scripts so we have to build the module
// in a different way. This file is compiled twice:
//    - with AWSLC_FIPS_APPLE_START flag to generate fips_apple_start.o
//    - with AWSLC_FIPS_APPLE_END flag to generate fips_apple_end.o
// The two generated files are used to link with the module bcm.o such that
// the final module object has start and end markers for  __text and __const
// sections that are used for the integrity check.

#include <stdio.h>
#include <stdint.h>

#if defined(AWSLC_FIPS_APPLE_START)

// Dummy but not empty function and array to avoid the compiler completely
// optimizing out the symbols.
const uint8_t *BORINGSSL_bcm_text_start(void) {
  return NULL;
}
const uint8_t BORINGSSL_bcm_rodata_start[16] =
              {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}; 

#elif defined(AWSLC_FIPS_APPLE_END)

// Dummy but not empty function and array to avoid the compiler completely
// optimizing out the symbols.
const uint8_t *BORINGSSL_bcm_text_end(void){
  return NULL;
}
const uint8_t BORINGSSL_bcm_rodata_end[16] =
              {16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31}; 

#else

#error "This file should be compiled only as part of the macOS/iOS FIPS build."

#endif

