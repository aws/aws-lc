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

static void create_test_macho_file(int num_syms, int *text_data, char *const_data,machofile *macho, symbol_info *symbol_table, const char* string_table) {
    if (macho == NULL || symbol_table == NULL) {
        LOG_ERROR("macho and symbol_table must be allocated");
        exit(EXIT_FAILURE);
    }

    FILE *file = fopen(TEST_FILE, "wb");
    if (!file) {
        LOG_ERROR("Error with fopen() on %s file", TEST_FILE);
        exit(EXIT_FAILURE);
    }

    uint32_t header_sizeofcmds = sizeof(segment_load_cmd) + 2 * sizeof(section) + sizeof(symtab_load_cmd);
    uint32_t header_ncmds = 2;
    macho_header test_header = {
        .magic = MH_MAGIC_64,
        .ncmds = header_ncmds,
        .sizeofcmds = header_sizeofcmds,
    };

    uint32_t text_segment_cmdsize = sizeof(segment_load_cmd) + 2 * sizeof(section);
    uint32_t text_segment_nsects = 2;
    segment_load_cmd test_text_segment = {
        .cmd = LC_SEGMENT_64,
        .cmdsize = text_segment_cmdsize,
        .segname = "__TEXT",
        .nsects = text_segment_nsects,
    };

    uint32_t text_section_offset = sizeof(macho_header) + sizeof(segment_load_cmd) + 2 * sizeof(section) + sizeof(symtab_load_cmd);
    uint64_t text_section_size = 1; // {0xC3}
    section test_text_section = {
        .sectname = "__text",
        .size = text_section_size, 
        .offset = text_section_offset,
    };

    uint32_t const_section_offset = text_section_offset + text_section_size;
    uint64_t const_section_size = 2;  // "hi"
    section test_const_section = {
        .sectname = "__const",
        .size = const_section_size,
        .offset = const_section_offset,
    };

    uint32_t symtab_command_symoff = const_section_offset + const_section_size;
    uint32_t symtab_command_stroff = symtab_command_symoff + num_syms * sizeof(symbol_info);
    uint32_t symtab_command_strsize = 32;
    symtab_load_cmd test_symtab_command = {
        .cmd = LC_SYMTAB,
        .cmdsize = sizeof(symtab_load_cmd),
        .symoff = symtab_command_symoff,
        .nsyms = num_syms,
        .stroff = symtab_command_stroff,
        .strsize = symtab_command_strsize,
    };

    fwrite(&test_header, sizeof(macho_header), 1, file);
    fwrite(&test_text_segment, sizeof(segment_load_cmd), 1, file);
    fwrite(&test_text_section, sizeof(section), 1, file);
    fwrite(&test_const_section, sizeof(section), 1, file);
    fwrite(&test_symtab_command, sizeof(symtab_load_cmd), 1, file);

    int *test_text_data = text_data;
    char *test_const_data = const_data;

    fseek(file, test_text_section.offset, SEEK_SET);
    fwrite(test_text_data, sizeof(test_text_data), 1, file);

    fseek(file, test_const_section.offset, SEEK_SET);
    fwrite(test_const_data, sizeof(test_const_data), 1, file);

    symbol_info symbol1 = {
        .n_un = {.n_strx = 15},  // Index into the string table
        .n_type = 0,
        .n_sect = 1,
        .n_desc = 0,
        .n_value = 15,  // Address of the symbol
    };

    symbol_info symbol2 = {
        .n_un = {.n_strx = 23},  // Index into the string table
        .n_type = 0,
        .n_sect = 2,
        .n_desc = 0,
        .n_value = 23,  // Address of the symbol
    };

    fseek(file, symtab_command_symoff, SEEK_SET);
    fwrite(&symbol1, sizeof(symbol_info), 1, file);
    fwrite(&symbol2, sizeof(symbol_info), 1, file);

    // Write the string table
    fseek(file, symtab_command_stroff, SEEK_SET);
    fwrite(string_table, symtab_command_strsize, 1, file);

    if (fclose(file) != 0) {
        LOG_ERROR("Error closing file\n");
    }

    section_info expected_text_section = {
        .name = "__text",
        .size = text_section_size,
        .offset = text_section_offset,
    };

    section_info expected_const_section = {
        .name = "__const",
        .size = const_section_size,
        .offset = const_section_offset,
    };

    section_info expected_symbol_table = {
        .name = "__symbol_table",
        .size = num_syms * sizeof(symbol_info),
        .offset = symtab_command_symoff,
    };

    section_info expected_string_table = {
        .name = "__string_table",
        .size = symtab_command_strsize,
        .offset = symtab_command_stroff,
    };

    section_info *expected_sections = malloc(sizeof(section_info) * 4);
    expected_sections[0] = expected_text_section;
    expected_sections[1] = expected_const_section;
    expected_sections[2] = expected_symbol_table;
    expected_sections[3] = expected_string_table;

    macho->macho_header = test_header,
    macho->num_sections = 4,
    macho->sections = expected_sections;

    symbol_table[0] = symbol1;
    symbol_table[1] = symbol2;
}

static void cleanup(void) {
    if (remove(TEST_FILE) != 0) {
        LOG_ERROR("Error deleting %s", TEST_FILE);
        exit(EXIT_FAILURE);
    }
}

static void test_read_macho_file(machofile *expected_macho) {
    machofile test_macho_file;
    if(!read_macho_file(TEST_FILE, &test_macho_file)) {
        LOG_ERROR("Something in read_macho_file broke");
        exit(EXIT_FAILURE);
    }

    if (memcmp(&test_macho_file.macho_header, &expected_macho->macho_header, sizeof(macho_header)) != 0) {
        LOG_ERROR("test_read_macho_file: read header is different than expected");
        exit(EXIT_FAILURE);
    }
    if (test_macho_file.num_sections != expected_macho->num_sections) {
        LOG_ERROR("test_read_macho_file: read number of sections is dfferent than expected");
        exit(EXIT_FAILURE);
    }
    if (memcmp(test_macho_file.sections, expected_macho->sections, test_macho_file.num_sections * sizeof(section_info)) != 0) {
        LOG_ERROR("test_read_macho_file: read section information is different than expected");
        printf("test:\n");
        print_hex(test_macho_file.sections, test_macho_file.num_sections * sizeof(section_info));
        printf("expected:\n");
        print_hex(expected_macho->sections, expected_macho->num_sections * sizeof(section_info));
        exit(EXIT_FAILURE);
    }
}

static void test_get_macho_section_data(int *text_data, char *const_data, machofile *expected_macho, symbol_info* expected_symtab, const char* expected_strtab) {
    uint8_t *text_section = NULL;
    size_t text_section_size;
    int *expected_text_section = text_data;

    uint8_t *const_section = NULL;
    size_t const_section_size;
    char *expected_const_section = const_data;

    uint8_t *symbol_table = NULL;
    size_t symbol_table_size;

    uint8_t *string_table = NULL;
    size_t string_table_size;

    text_section = get_macho_section_data(TEST_FILE, expected_macho, "__text", &text_section_size, NULL);
    if (memcmp(text_section, expected_text_section, text_section_size) != 0) {
        LOG_ERROR("text section is not equal to what was expected");
        exit(EXIT_FAILURE);
    }

    const_section = get_macho_section_data(TEST_FILE, expected_macho, "__const", &const_section_size, NULL);
    if (memcmp(const_section, expected_const_section, const_section_size) != 0) {
        LOG_ERROR("const section is not equal to what was expected");
        exit(EXIT_FAILURE);
    }

    // Something about calling this function on the symbol table causes something to segfault occasionally
    symbol_table = get_macho_section_data(TEST_FILE, expected_macho, "__symbol_table", &symbol_table_size, NULL);
    if (memcmp(symbol_table, expected_symtab, symbol_table_size) != 0) {
        LOG_ERROR("symbol table is not equal to what was expected");
        exit(EXIT_FAILURE);
    }

    string_table = get_macho_section_data(TEST_FILE, expected_macho, "__string_table", &string_table_size, NULL);
    if (memcmp(string_table, expected_strtab, string_table_size) != 0) {
        LOG_ERROR("string table is not equal to what was expected");
        exit(EXIT_FAILURE);
    }

    if (text_section != NULL) {
        free(text_section);
    }
    if (const_section != NULL) {
        free(const_section);
    }
    if (symbol_table != NULL) {
        free(symbol_table);
    }
    if (string_table != NULL) {
        free(string_table);
    }
}

static void test_find_macho_symbol_index(machofile *expected_macho, const char *expected_strtab, uint32_t expected_symbol_int) {
    uint8_t *symbol_table = NULL;
    size_t symbol_table_size;

    uint8_t *string_table = NULL;
    size_t string_table_size;

    symbol_table = get_macho_section_data(TEST_FILE, expected_macho, "__symbol_table", &symbol_table_size, NULL);
    string_table = get_macho_section_data(TEST_FILE, expected_macho, "__string_table", &string_table_size, NULL);

    uint32_t symbol1_index;
    symbol1_index = find_macho_symbol_index(symbol_table, symbol_table_size, string_table, string_table_size, "symbol1", NULL);

    if (symbol_table != NULL) {
        free(symbol_table);
    }
    if (string_table != NULL) {
        free(string_table);
    }

    if (expected_symbol_int != symbol1_index) {
        LOG_ERROR("found index %u is not equal to expected index %u", symbol1_index, expected_symbol_int);
        exit(EXIT_FAILURE);
    }
}

/**
 * TODO:
 * move all "global" variables into main function and pass into tests as arguments
*/

int main(int argc, char *argv[]) {
    int num_syms = 2;
    char expected_strtab[] = "__text\0__const\0symbol1\0symbol2\0";
    int text_data[] = { 0xC3 };
    char const_data[] = "hi";

    machofile *expected_macho = malloc(sizeof(machofile));
    symbol_info *expected_symtab = malloc(num_syms * sizeof(symbol_info));
    uint32_t expected_symbol_ind = 15;

    create_test_macho_file(num_syms, text_data, const_data, expected_macho, expected_symtab, expected_strtab);
    test_read_macho_file(expected_macho);
    test_get_macho_section_data(text_data, const_data, expected_macho, expected_symtab, expected_strtab);
    test_find_macho_symbol_index(expected_macho, expected_strtab, expected_symbol_ind);

    free_macho_file(expected_macho);
    free(expected_symtab);
    cleanup();

    printf("All tests passed\n");
    return 0;
}
