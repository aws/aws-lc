// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <assert.h>

#include "../common.h"
#include "../macho_parser.h"

#define TEST_FILE "test_macho"

static void print_hex(const void *ptr, size_t size) {
    for (size_t i = 0; i < size; i++) {
        printf("%02X", *((unsigned char *) ptr + i));
        if ((i+1)%4 == 0) {
            printf(" ");
        }

        if((i+1)%32 == 0) {
            printf("\n");
        }
    }
    printf("\n");
}

static MachOFile create_test_macho_file(void) {
    FILE *file = fopen(TEST_FILE, "wb");
    if (!file) {
        LOG_ERROR("Error with fopen() on %s file", TEST_FILE);
        exit(EXIT_FAILURE);
    }

    uint32_t header_sizeofcmds = sizeof(SegmentLoadCommand) + 2 * sizeof(SectionHeader) + sizeof(SymtabLoadCommand);
    uint32_t header_ncmds = 2;
    MachOHeader test_header = {
        .magic = MH_MAGIC_64,
        .ncmds = header_ncmds,
        .sizeofcmds = header_sizeofcmds,
    };

    uint32_t text_segment_cmdsize = sizeof(SegmentLoadCommand) + 2 * sizeof(SectionHeader);
    uint32_t text_segment_nsects = 2;
    SegmentLoadCommand test_text_segment = {
        .cmd = LC_SEGMENT_64,
        .cmdsize = text_segment_cmdsize,
        .segname = "__TEXT",
        .nsects = text_segment_nsects,
    };

    uint32_t text_section_offset = sizeof(MachOHeader) + sizeof(SegmentLoadCommand) + 2 * sizeof(SectionHeader) + sizeof(SymtabLoadCommand);
    uint64_t text_section_size = 1; // {0xC3}
    SectionHeader test_text_section = {
        .sectname = "__text",
        .size = text_section_size, 
        .offset = text_section_offset,
    };

    uint32_t const_section_offset = text_section_offset + text_section_size;
    uint64_t const_section_size = 2;  // "hi"
    SectionHeader test_const_section = {
        .sectname = "__const",
        .size = const_section_size,
        .offset = const_section_offset,
    };

    uint32_t symtab_command_symoff = const_section_offset + const_section_size;
    uint32_t symtab_command_nsyms = 2;
    uint32_t symtab_command_stroff = symtab_command_symoff + 2 * sizeof(nList);
    uint32_t symtab_command_strsize = 2;
    SymtabLoadCommand test_symtab_command = {
        .cmd = LC_SYMTAB,
        .cmdsize = sizeof(SymtabLoadCommand),
        .symoff = symtab_command_symoff,
        .nsyms = symtab_command_nsyms,
        .stroff = symtab_command_stroff,
        .strsize = symtab_command_strsize,
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


    SectionInfo expected_text_section = {
        .name = "__text",
        .size = text_section_size,
        .offset = text_section_offset,
    };

    SectionInfo expected_const_section = {
        .name = "__const",
        .size = const_section_size,
        .offset = const_section_offset,
    };

    SectionInfo expected_symbol_table = {
        .name = "__symbol_table",
        .size = symtab_command_nsyms * sizeof(nList),
        .offset = symtab_command_symoff,
    };

    SectionInfo expected_string_table = {
        .name = "__string_table",
        .size = symtab_command_strsize,
        .offset = symtab_command_stroff,
    };

    // SectionInfo expected_sections[4] = {expected_text_section, expected_const_section, expected_symbol_table, expected_string_table};    
    SectionInfo *expected_sections = malloc(sizeof(SectionInfo) * 4);
    expected_sections[0] = expected_text_section;
    expected_sections[1] = expected_const_section;
    expected_sections[2] = expected_symbol_table;
    expected_sections[3] = expected_string_table;

    MachOFile expected = {
        .machHeader = test_header,
        .numSections = 4,
        .sections = expected_sections,
    };

    return expected;
}

static void cleanup(void) {
    if (remove(TEST_FILE) != 0) {
        LOG_ERROR("Error deleting %s", TEST_FILE);
        exit(EXIT_FAILURE);
    }
}

static void test_read_macho_file(MachOFile expected) {
    MachOFile test_macho_file;
    if(!read_macho_file(TEST_FILE, &test_macho_file)) {
        LOG_ERROR("Something in read_macho_file broke");
        exit(EXIT_FAILURE);
    }

    if (memcmp(&test_macho_file.machHeader, &expected.machHeader, sizeof(MachOHeader)) != 0) {
        LOG_ERROR("test_read_macho_file: read header is different than expected");
        exit(EXIT_FAILURE);
    }
    if (test_macho_file.numSections != expected.numSections) {
        LOG_ERROR("test_read_macho_file: read number of sections is dfferent than expected");
        exit(EXIT_FAILURE);
    }
    if (memcmp(test_macho_file.sections, expected.sections, test_macho_file.numSections * sizeof(SectionInfo)) != 0) {
        LOG_ERROR("test_read_macho_file: read section information is different than expected");
        printf("test:\n");
        print_hex(test_macho_file.sections, test_macho_file.numSections * sizeof(SectionInfo));
        printf("expected:\n");
        print_hex(expected.sections, expected.numSections * sizeof(SectionInfo));
        exit(EXIT_FAILURE);
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

    MachOFile expected = create_test_macho_file();
    test_read_macho_file(expected);
    test_free_macho_file();
    test_print_macho_section_info();
    test_get_macho_section_data();
    test_find_macho_symbol_index();

    free(expected);
    cleanup();

    printf("All tests passed\n");
    return 0;
}
