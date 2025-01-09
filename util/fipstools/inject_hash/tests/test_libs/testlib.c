// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <stdio.h>
#include <stdint.h>

#ifndef BAD_MARKER
const uint8_t *BORINGSSL_bcm_text_start(void) {
  return NULL;
}
#endif
const uint8_t *BORINGSSL_bcm_text_end(void){
  return NULL;
}


const uint8_t BORINGSSL_bcm_text_hash[32] = {
    0xae, 0x2c, 0xea, 0x2a, 0xbd, 0xa6, 0xf3, 0xec, 0x97, 0x7f, 0x9b,
    0xf6, 0x94, 0x9a, 0xfc, 0x83, 0x68, 0x27, 0xcb, 0xa0, 0xa0, 0x9f,
    0x6b, 0x6f, 0xde, 0x52, 0xcd, 0xe2, 0xcd, 0xff, 0x31, 
#ifndef BAD_HASH
    0x80,
#else
    0X81,
#endif
};

const uint8_t BORINGSSL_bcm_rodata_start[16] =
              {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}; 
const uint8_t BORINGSSL_bcm_rodata_end[16] =
              {16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31};
