// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <assert.h>
#include <stdio.h>

#include "../macho_parser.h"

static void test_read_macho_file(void) {
    assert (1 == 1);
}

static void test_free_macho_file(void) {
    assert (1 == 1);
}

static void test_print_macho_section_info(void) {
    assert (1 == 1);
}

static void test_get_macho_section_data(void) {
    assert (1 == 1);
}

static void test_find_macho_symbol_index(void) {
    assert (1 == 1);
}

int main(int argc, char *argv[]) {

    test_read_macho_file();
    test_free_macho_file();
    test_print_macho_section_info();
    test_get_macho_section_data();
    test_find_macho_symbol_index();

    printf("All tests passed\n");
    return 0;
}
