// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include "../macho_parser.h"

#define TEST_FILE "test_macho"
#define EXPECTED_STRTAB_SIZE 32
#define TEXT_DATA_SIZE 1
#define CONST_DATA_SIZE 3
#define NUM_SYMS 2

class MachoTestFixture : public ::testing::Test {
protected:
    static machofile *expected_macho;
    static struct nlist_64 *expected_symtab;
    static constexpr char expected_strtab[] = "__text\0__const\0symbol1\0symbol2\0";
    static constexpr int text_data[] = { 0xC3 };
    static constexpr char const_data[] = "hi";
    static uint32_t expected_symbol1_ind;
    static uint32_t expected_symbol2_ind;

    static uint32_t FindSymbolIndex(const char *strtab, const char *symbol_name) {
        const char *symbol = strtab;
        uint32_t index = 0;

        while (*symbol != '\0') {
            if (strcmp(symbol, symbol_name) == 0) {
                return index;
            }

            index += strlen(symbol) + 1;
            symbol += strlen(symbol) + 1;
        }

        return UINT32_MAX;
    }

    static void SetUpTestSuite() {
        bool fail = true;
        section_info *expected_text_section = NULL;
        section_info *expected_const_section = NULL;
        section_info *expected_symbol_table = NULL;
        section_info *expected_string_table = NULL;
        section_info *expected_sections = NULL;

        struct nlist_64 symbol1;
        struct nlist_64 symbol2;

        static FILE *file = fopen(TEST_FILE, "wb");
        if (file == NULL) {
            LOG_ERROR("Error with fopen() on %s file", TEST_FILE);
        }

        uint32_t header_sizeofcmds = sizeof(struct segment_command_64) + 2 * sizeof(struct section_64) + sizeof(struct symtab_command);
        uint32_t header_ncmds = 2;
        struct mach_header_64 test_header = {
            .magic = MH_MAGIC_64,
            .ncmds = header_ncmds,
            .sizeofcmds = header_sizeofcmds,
        };

        uint32_t text_segment_cmdsize = sizeof(struct segment_command_64) + 2 * sizeof(struct section_64);
        uint32_t text_segment_nsects = 2;
        struct segment_command_64 test_text_segment = {
            .cmd = LC_SEGMENT_64,
            .cmdsize = text_segment_cmdsize,
            .segname = "__TEXT",
            .nsects = text_segment_nsects,
        };

        uint32_t text_section_offset = sizeof(struct mach_header_64) + sizeof(struct segment_command_64) + 2 * sizeof(struct section_64) + sizeof(struct symtab_command);
        uint64_t text_section_size = TEXT_DATA_SIZE; // {0xC3}
        struct section_64 test_text_section = {
            .sectname = "__text",
            .size = text_section_size, 
            .offset = text_section_offset,
        };

        uint32_t const_section_offset = text_section_offset + text_section_size;
        uint64_t const_section_size = CONST_DATA_SIZE;  // "hi"
        struct section_64 test_const_section = {
            .sectname = "__const",
            .size = const_section_size,
            .offset = const_section_offset,
        };

        uint32_t symtab_command_symoff = const_section_offset + const_section_size;
        uint32_t symtab_command_stroff = symtab_command_symoff + NUM_SYMS * sizeof(struct nlist_64);
        uint32_t symtab_command_strsize = 32;
        struct symtab_command test_symtab_command = {
            .cmd = LC_SYMTAB,
            .cmdsize = sizeof(struct symtab_command),
            .symoff = symtab_command_symoff,
            .nsyms = NUM_SYMS,
            .stroff = symtab_command_stroff,
            .strsize = symtab_command_strsize,
        };

        if (fwrite(&test_header, sizeof(struct mach_header_64), 1, file) != 1) {
            LOG_ERROR("Error occurred while writing to file %s", TEST_FILE);
            goto end;
        }
        if (fwrite(&test_text_segment, sizeof(struct segment_command_64), 1, file) != 1) {
            LOG_ERROR("Error occurred while writing to file %s", TEST_FILE);
            goto end;
        }
        if (fwrite(&test_text_section, sizeof(struct section_64), 1, file) != 1) {
            LOG_ERROR("Error occurred while writing to file %s", TEST_FILE);
            goto end;
        }
        if (fwrite(&test_const_section, sizeof(struct section_64), 1, file) != 1) {
            LOG_ERROR("Error occurred while writing to file %s", TEST_FILE);
            goto end;
        }
        if (fwrite(&test_symtab_command, sizeof(struct symtab_command), 1, file) != 1) {
            LOG_ERROR("Error occurred while writing to file %s", TEST_FILE);
            goto end;
        }

        if (fseek(file, test_text_section.offset, SEEK_SET) != 0) {
            LOG_ERROR("Failed to seek in file %s", TEST_FILE);
            goto end;
        }
        if (fwrite(text_data, sizeof(text_data), 1, file) != 1) {
            LOG_ERROR("Error occurred while writing to file %s", TEST_FILE);
            goto end;
        }

        if (fseek(file, test_const_section.offset, SEEK_SET) != 0) {
            LOG_ERROR("Failed to seek in file %s", TEST_FILE);
            goto end;
        }
        if (fwrite(const_data, sizeof(const_data), 1, file) != 1) {
            LOG_ERROR("Error occurred while writing to file %s", TEST_FILE);
            goto end;
        }

        expected_symbol1_ind = FindSymbolIndex(expected_strtab, "symbol1");
        if (expected_symbol1_ind == UINT32_MAX) {
            LOG_ERROR("symbol1 not found in expected string table");
            goto end;
        }
        symbol1 = {
            .n_un = {.n_strx = expected_symbol1_ind},
            .n_type = 0,
            .n_sect = 1,
            .n_desc = 0,
            .n_value = expected_symbol1_ind,
        };

        expected_symbol2_ind = FindSymbolIndex(expected_strtab, "symbol2");
        if (expected_symbol2_ind == UINT32_MAX) {
            LOG_ERROR("symbol2 not found in expected string table");
            goto end;
        }
        symbol2 = {
            .n_un = {.n_strx = expected_symbol2_ind},
            .n_type = 0,
            .n_sect = 2,
            .n_desc = 0,
            .n_value = expected_symbol2_ind,
        };

        if (fseek(file, symtab_command_symoff, SEEK_SET) != 0) {
            LOG_ERROR("Failed to seek in file %s", TEST_FILE);
            goto end;
        }
        if (fwrite(&symbol1, sizeof(struct nlist_64), 1, file) != 1) {
            LOG_ERROR("Error occurred while writing to file %s", TEST_FILE);
            goto end;
        }
        if (fwrite(&symbol2, sizeof(struct nlist_64), 1, file) != 1) {
            LOG_ERROR("Error occurred while writing to file %s", TEST_FILE);
            goto end;
        }

        if (fseek(file, symtab_command_stroff, SEEK_SET) != 0) {
            LOG_ERROR("Failed to seek in file %s", TEST_FILE);
            goto end;
        }
        if (fwrite(expected_strtab, symtab_command_strsize, 1, file) != 1) {
            LOG_ERROR("Error occurred while writing to file %s", TEST_FILE);
            goto end;
        }

        if (fclose(file) != 0) {
            LOG_ERROR("Error closing file\n");
            goto end;
        }

        // We use calloc for the below four calls to ensure that the untouched parts are zeroized,
        // as we will later memcmp the data to what we've read from the file.
        expected_text_section = (section_info*) calloc(1, sizeof(section_info));
        if (expected_text_section == NULL) {
            LOG_ERROR(" Error allocating memory for expected text section");
            goto end;
        }
        strcpy(expected_text_section->name, "__text");
        expected_text_section->size = text_section_size;
        expected_text_section->offset = text_section_offset;

        expected_const_section = (section_info*) calloc(1, sizeof(section_info));
        if (expected_const_section == NULL) {
            LOG_ERROR(" Error allocating memory for expected const section");
            goto end;
        }
        strcpy(expected_const_section->name, "__const");
        expected_const_section->size = const_section_size;
        expected_const_section->offset = const_section_offset;

        expected_symbol_table = (section_info*) calloc(1, sizeof(section_info));
        if (expected_symbol_table == NULL) {
            LOG_ERROR(" Error allocating memory for expected symbol table");
            goto end;
        }
        strcpy(expected_symbol_table->name, "__symbol_table");
        expected_symbol_table->size = NUM_SYMS * sizeof(struct nlist_64);
        expected_symbol_table->offset = symtab_command_symoff;

        expected_string_table = (section_info*) calloc(1, sizeof(section_info));
        if (expected_string_table == NULL) {
            LOG_ERROR(" Error allocating memory for expected string table");
            goto end;
        }
        strcpy(expected_string_table->name, "__string_table");
        expected_string_table->size = symtab_command_strsize;
        expected_string_table->offset = symtab_command_stroff;

        expected_sections = (section_info*) malloc(sizeof(section_info) * 4);
        if (expected_sections == NULL) {
            LOG_ERROR("Error allocating memory for expected sections");
            goto end;
        }
        memcpy(&expected_sections[0], expected_text_section, sizeof(section_info));
        memcpy(&expected_sections[1], expected_const_section, sizeof(section_info));
        memcpy(&expected_sections[2], expected_symbol_table, sizeof(section_info));
        memcpy(&expected_sections[3], expected_string_table, sizeof(section_info));

        expected_macho = (machofile*) malloc(sizeof(machofile));
        if (expected_macho == NULL) {
            LOG_ERROR("Error allocating memory for expected macho file struct");
            goto end;
        }
        expected_macho->macho_header = test_header;
        expected_macho->num_sections = 4;
        expected_macho->sections = expected_sections;

        expected_symtab = (struct nlist_64*) malloc(NUM_SYMS * sizeof(struct nlist_64));
        if (expected_symtab == NULL) {
            LOG_ERROR("Error allocating memory for expected symbol table struct");
            goto end;
        }
        expected_symtab[0] = symbol1;
        expected_symtab[1] = symbol2;

        fail = false;
end:
        if (fail) {
            free(expected_sections);
            free(expected_macho);
            free(expected_symtab);
        }
        free(expected_text_section);
        free(expected_const_section);
        free(expected_symbol_table);
        free(expected_string_table);
    }

    static void TearDownTestSuite() {
        free_macho_file(expected_macho);
        free(expected_symtab);
        if (remove(TEST_FILE) != 0) {
            LOG_ERROR("Error deleting %s", TEST_FILE);
        }
    }
};
