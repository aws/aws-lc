// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <assert.h>

#include "../common.h"
#include "macho_tests.h"

#define TEST_FILE "test_macho"

// static void print_hex(const void *ptr, size_t size) {
//     for (size_t i = 0; i < size; i++) {
//         printf("%02X", *((unsigned char *) ptr + i));
//         if ((i+1)%4 == 0) {
//             printf(" ");
//         }

//         if((i+1)%32 == 0) {
//             printf("\n");
//         }
//     }
//     printf("\n");
// }

machofile *MachoTestFixture::expected_macho;
symbol_info *MachoTestFixture::expected_symtab;
uint32_t MachoTestFixture::num_syms;
char MachoTestFixture::expected_strtab[31];
int MachoTestFixture::text_data[1];
char MachoTestFixture::const_data[2];

TEST_F(MachoTestFixture, TestReadMachOFile) {
    machofile test_macho_file;
    if(!read_macho_file(TEST_FILE, &test_macho_file)) {
        LOG_ERROR("Failed to read macho_file");
    }

    EXPECT_TRUE(memcmp(&test_macho_file.macho_header, &expected_macho->macho_header, sizeof(macho_header)) == 0);
    
    EXPECT_EQ(test_macho_file.num_sections, expected_macho->num_sections);

    EXPECT_TRUE(memcmp(test_macho_file.sections, expected_macho->sections, test_macho_file.num_sections * sizeof(section_info)) == 0);
}
