/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------------------
*/

// The FIPS build on macOS is different than the build on Linux.
// Apple's linker doesn't support linker scripts so we have to build the module
// in a different way. This file is compiled twice:
//    - with AWSLC_FIPS_MACOS_START flag to generate fips_macos_start.o
//    - with AWSLC_FIPS_MACOS_END flag to generate fips_macos_end.o
// The two generated files are used to link with the module bcm.o such that
// the final module object has start and end markers for  __text and __const
// sections that are used for the integrity check.

#include <stdio.h>
#include <stdint.h>

#if defined(AWSLC_FIPS_MACOS_START)

const uint8_t *BORINGSSL_bcm_text_start(void) {
  return NULL;
}
const uint8_t BORINGSSL_bcm_rodata_start[16] =
              {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}; 

#elif defined(AWSLC_FIPS_MACOS_END)

const uint8_t *BORINGSSL_bcm_text_end(void){
  return NULL;
}
const uint8_t BORINGSSL_bcm_rodata_end[16] =
              {16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31}; 

#else

#error "This file should be compiled only as part of the FIPS build on macOS."

#endif

