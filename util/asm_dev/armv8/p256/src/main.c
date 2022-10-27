/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

#include <stdio.h>
#include <stdlib.h>
#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif
#include <inttypes.h>
#include "p256.h"

#ifdef SELECT_FN
#define ENTRY_LONG_SIZE  12  //12 64-bit (long) words, 3 coordinates
#define NUM_ENTRIES      16
#define TABLE_LONG_SIZE (NUM_ENTRIES * ENTRY_LONG_SIZE)

#define ENTRY_LONG_SIZE_W7  8   // 2 coordinates
#define NUM_ENTRIES_W7     64
#define TABLE_LONG_SIZE_W7 (NUM_ENTRIES_W7 * ENTRY_LONG_SIZE_W7)
#endif

#ifdef BEEU
#define K_MAX   2000
// P-256 group order in words (little-endian) obtained from debugging
// ./third_party/boringssl/crypto/crypto_test --gtest_filter=P256_X86_64Test.*
static const uint64_t order_words[4] =
{
    0xf3b9cac2fc632551, 0xbce6faada7179e84, 0xffffffffffffffff, 0xffffffff00000000
};
// In bytes from ec.c
//{
//    0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF,
//    0xFF, 0xFF, 0xFF, 0xFF, 0xBC, 0xE6, 0xFA, 0xAD, 0xA7, 0x17, 0x9E, 0x84,
//    0xF3, 0xB9, 0xCA, 0xC2, 0xFC, 0x63, 0x25, 0x51,
//};

// expected inverse of a = 2, obtained from debugging as above
static const uint64_t out_exp_2[4] =
{
    0x79dce5617e3192a9, 0xde737d56d38bcf42, 0x7fffffffffffffff, 0x7fffffff80000000
};

static void beeu_print(const int res, const uint64_t out_exp[4], const uint64_t out[4])
{
    uint32_t k;
    if(res == 1)
    {
        for (k = 0; k < 4; k++)
        {
            if (out_exp[k] != out[k])
            {
                break;
            }
            printf("k:%d, out_exp: %lX, out: %lX\n", k, out_exp[k], out[k]);
        }
        printf("out_exp_p: %lX, out_p: %lX\n", (uintptr_t)out_exp, (uintptr_t)out);

        if (4 == k)
        {
            printf("beeu Test passed\n");
        }
    }
}
#endif

int main()
{
#ifdef SELECT_FN
    uint32_t index;
    uint32_t idx_64;
    uint32_t j;

    uint64_t table[TABLE_LONG_SIZE];
    uint64_t val[ENTRY_LONG_SIZE];

    uint64_t table_w7[TABLE_LONG_SIZE_W7];
    uint64_t val_w7[ENTRY_LONG_SIZE_W7];

    uint32_t passed;
#endif

#ifdef BEEU
    uint64_t out[4];
    uint64_t a[4];
    uint64_t out_exp[4];
    uint64_t a_out[4];
    uint64_t k;
    int beeu_res;
#endif

#ifdef SELECT_FN
    /*
     * Test select_w5
     */
    passed = 1;
    for(j = 1; j <= TABLE_LONG_SIZE; j++)
    {
      table[j-1] = (uint64_t)j << 2;
    }

    for(index = 1; index <= NUM_ENTRIES; index ++)
    {
      select_w5(val, table, index);

      // Check the correct entry was selected
      for(j = 0; j < ENTRY_LONG_SIZE; j++)
      {
        // Calculating the index to the 64-bit part of the table entry
        idx_64 = ((index-1) * ENTRY_LONG_SIZE) + (uint32_t) j;
        if(val[j] != table[idx_64])
        {
          printf("Error: difference at index: %d, j: %d, idx_64: %d, val[j]:%lX, table[idx_64]: %lX\n",
                 index, j, idx_64, val[j], table[idx_64]);
          passed = 0;
        }
      }
    }
    if (1 == passed)
    {
        printf("select_w5 Test passed\n");
    }

    /*
     * Test select_w7
     */
    passed = 1;
    for(j = 1; j <= TABLE_LONG_SIZE_W7; j++)
    {
      table_w7[j-1] = (uint64_t)j << 2;
    }

    for(index = 1; index <= NUM_ENTRIES_W7; index ++)
    {
      select_w7(val_w7, table_w7, index);

      // Check the correct entry was selected
      for(j = 0; j < ENTRY_LONG_SIZE_W7; j++)
      {
        // Calculating the index to the 64-bit part of the table entry
        idx_64 = ((index-1) * ENTRY_LONG_SIZE_W7) + (uint32_t) j;
        if(val_w7[j] != table_w7[idx_64])
        {
          printf("Error (w7): difference at index: %d, j: %d, idx_64: %d, val[j]:%lX, table[idx_64]: %lX\n",
                 index, j, idx_64, val_w7[j], table_w7[idx_64]);
          passed = 0;
        }
      }
    }
    if (1 == passed)
    {
        printf("select_w7 Test passed\n");
    }
#endif

#ifdef BEEU
    /*
     * Test beeu
     */

    printf("a = 2\n");
    a[0] = 2;
    a[1] = a[2] = a[3] = 0;

    beeu_res = beeu_mod_inverse_vartime(out, a, order_words);
    beeu_print(beeu_res, out_exp_2, out);

    printf("a = 1\n");
    a[0] = 1;
    out_exp[0] = 1;
    out_exp[1] = out_exp[2] = out_exp[3] = 0;

    beeu_res = beeu_mod_inverse_vartime(out, a, order_words);
    beeu_print(beeu_res, out_exp, out);

    for (k = 1; k < K_MAX; k++)
    {
        a[0] = k;
        if (k >= (K_MAX >>1))
        {
            a[1] = k << 8;
            a[2] = k << 32;
            a[3] = k << 48;
        } else {
            a[1] = a[2] = a[3] = 0;
        }
        // out = a^{-1} mod n
        beeu_res = beeu_mod_inverse_vartime(out, a, order_words);
        if (beeu_res == 1)
        {
            // a_out = out^{-1} mod n
            beeu_res = beeu_mod_inverse_vartime(a_out, out, order_words);
            if (beeu_res != 1    ||
                a_out[0] != a[0] ||
                a_out[1] != a[1] ||
                a_out[2] != a[2] ||
                a_out[3] != a[3]
                )
            {
                printf("beeu Test FAILED at k = %ld; a_out != a\n", k);
                break;
            }
        }
    }
    if (k == K_MAX)
    {
        printf("SUCCESS: %ld beeu tests passed\n", k);
    }

#endif

    return 0;
}
