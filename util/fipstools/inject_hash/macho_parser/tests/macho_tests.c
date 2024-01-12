// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <assert.h>

#include "../common.h"
#include "../macho_parser.h"

#define TEST_FILE "test_macho"

static void create_test_macho_file(void) {
    FILE *file = fopen(TEST_FILE, "wb");
    if (!file) {
        LOG_ERROR("Error with fopen() on %s file", TEST_FILE);
        exit(EXIT_FAILURE);
    }

    MachOHeader test_header = {
        .magic = MH_MAGIC_64,
        .ncmds = 2,
        .sizeofcmds = sizeof(SegmentLoadCommand) + 2 * sizeof(SectionHeader) + sizeof(SymtabLoadCommand),
    };

    SegmentLoadCommand test_text_segment = {
        .cmd = LC_SEGMENT_64,
        .cmdsize = sizeof(SegmentLoadCommand) + 2 * sizeof(SectionHeader),
        .segname = "__TEXT",
        .nsects = 2,
    };

    SectionHeader test_text_section = {
        .sectname = "__text",
        .size = 1, // {0xC3}
        .offset = sizeof(MachOHeader) + sizeof(SegmentLoadCommand) + 2 * sizeof(SectionHeader) + sizeof(SymtabLoadCommand),
    };

    SectionHeader test_const_section = {
        .sectname = "__const",
        .size = 2, // "hi" (including string literal)
        .offset = test_text_section.offset + test_text_section.size,
    };

    SymtabLoadCommand test_symtab_command = {
        .cmd = LC_SYMTAB,
        .cmdsize = sizeof(SymtabLoadCommand),
        .symoff = test_const_section.offset + test_const_section.size,
        .nsyms = 2,
        .stroff = test_const_section.offset + test_const_section.size + 2 * sizeof(nList),
        .strsize = 2,
    };

    fwrite(&test_header, sizeof(MachOHeader), 1, file);
    fwrite(&test_text_segment, sizeof(SegmentLoadCommand), 1, file);
    fwrite(&test_text_section, sizeof(SectionHeader), 1, file);
    fwrite(&test_const_section, sizeof(SectionHeader), 1, file);
    fwrite(&test_symtab_command, sizeof(SymtabLoadCommand), 1, file);

    char test_text_data[] = {0xC3};
    char test_const_data[] = "hi";

    fseek(file, test_text_section.offset, SEEK_SET);
    fwrite(test_text_data, sizeof(test_text_data), 1, file);

    fseek(file, test_const_section.offset, SEEK_SET);
    fwrite(test_const_data, sizeof(test_const_data), 1, file);

    // Leave out symbol and string tables for now

    // nList symbol1 = {
    //     .n_un = {.n_strx = 1},  // Index into the string table
    //     .n_type = N_TEXT,
    //     .n_sect = 1,
    //     .n_desc = 0,
    //     .n_value = 0x100000000,  // Address of the symbol
    // };

    // nList symbol2 = {
    //     .n_un = {.n_strx = 15},  // Index into the string table
    //     .n_type = N_DATA,
    //     .n_sect = 2,
    //     .n_desc = 0,
    //     .n_value = 0x100000000 + sizeof(test_text_data),  // Address of the symbol
    // };

    // fwrite(&symbol1, sizeof(struct nlist_64), 1, file);
    // fwrite(&symbol2, sizeof(struct nlist_64), 1, file);

    // // Write the string table
    // char string_table[] = "\0__text\0__const\0symbol1\0symbol2";
    // fseek(file, symtab_cmd.stroff, SEEK_SET);
    // fwrite(string_table, sizeof(string_table), 1, file);

    if (fclose(file) != 0) {
        LOG_ERROR("bad\n");
    }
}

static void cleanup(void) {
    if (remove(TEST_FILE) != 0) {
        LOG_ERROR("Error deleting %s", TEST_FILE);
        exit(EXIT_FAILURE);
    }
}

static void test_read_macho_file(void) {
    MachOFile test_macho_file;
    if(!read_macho_file(TEST_FILE, &test_macho_file)) {
        LOG_ERROR("Something in read_macho_file broke");
        exit(EXIT_FAILURE);
    }

    if (test_macho_file.machHeader.magic != MH_MAGIC_64) {
        LOG_ERROR("Incorrect header magic value");
    }
    if (test_macho_file.machHeader.ncmds != 2) {
        LOG_ERROR("Incorrect header ncmds value");
    }
    if (test_macho_file.machHeader.sizeofcmds != sizeof(SegmentLoadCommand) + 2 * sizeof(SectionHeader) + sizeof(SymtabLoadCommand)) {
        LOG_ERROR("Incorrect header sizeofcmds value");
    }

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

    create_test_macho_file();
    test_read_macho_file();
    test_free_macho_file();
    test_print_macho_section_info();
    test_get_macho_section_data();
    test_find_macho_symbol_index();

    cleanup();

    printf("All tests passed\n");
    return 0;
}
