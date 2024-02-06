#include <gtest/gtest.h>

#include "../macho_parser.h"

#define TEST_FILE "test_macho"
#define EXPECTED_STRTAB_SIZE 31
#define TEXT_DATA_SIZE 1
#define CONST_DATA_SIZE 2

class MachoTestFixture : public ::testing::Test {
protected:
    static machofile *expected_macho;
    static symbol_info *expected_symtab;
    static uint32_t num_syms;
    static char expected_strtab[EXPECTED_STRTAB_SIZE];
    static int text_data[TEXT_DATA_SIZE];
    static char const_data[CONST_DATA_SIZE];
    static uint32_t expected_symbol1_ind;
    static uint32_t expected_symbol2_ind;

    static void SetUpTestSuite() {
        num_syms = 2;
        memcpy(expected_strtab, "__text\0__const\0symbol1\0symbol2\0", EXPECTED_STRTAB_SIZE);
        text_data[0] = 0xC3;
        memcpy(const_data, "hi", CONST_DATA_SIZE);
        expected_symbol1_ind = 15;
        expected_symbol2_ind = 23;

        FILE *file = fopen(TEST_FILE, "wb");
        if (!file) {
            LOG_ERROR("Error with fopen() on %s file", TEST_FILE);
        }

        uint32_t header_sizeofcmds = sizeof(segment_load_cmd) + 2 * sizeof(section_data) + sizeof(symtab_load_cmd);
        uint32_t header_ncmds = 2;
        macho_header test_header = {
            .magic = MH_MAGIC_64,
            .ncmds = header_ncmds,
            .sizeofcmds = header_sizeofcmds,
        };

        uint32_t text_segment_cmdsize = sizeof(segment_load_cmd) + 2 * sizeof(section_data);
        uint32_t text_segment_nsects = 2;
        segment_load_cmd test_text_segment = {
            .cmd = LC_SEGMENT_64,
            .cmdsize = text_segment_cmdsize,
            .segname = "__TEXT",
            .nsects = text_segment_nsects,
        };

        uint32_t text_section_offset = sizeof(macho_header) + sizeof(segment_load_cmd) + 2 * sizeof(section_data) + sizeof(symtab_load_cmd);
        uint64_t text_section_size = TEXT_DATA_SIZE; // {0xC3}
        section_data test_text_section = {
            .sectname = "__text",
            .size = text_section_size, 
            .offset = text_section_offset,
        };

        uint32_t const_section_offset = text_section_offset + text_section_size;
        uint64_t const_section_size = CONST_DATA_SIZE;  // "hi"
        section_data test_const_section = {
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
        fwrite(&test_text_section, sizeof(section_data), 1, file);
        fwrite(&test_const_section, sizeof(section_data), 1, file);
        fwrite(&test_symtab_command, sizeof(symtab_load_cmd), 1, file);

        int *test_text_data = text_data;
        char *test_const_data = const_data;

        fseek(file, test_text_section.offset, SEEK_SET);
        fwrite(test_text_data, sizeof(test_text_data), 1, file);

        fseek(file, test_const_section.offset, SEEK_SET);
        fwrite(test_const_data, sizeof(test_const_data), 1, file);
    
        symbol_info symbol1 = {
        .n_un = {.n_strx = expected_symbol1_ind},
        .n_type = 0,
        .n_sect = 1,
        .n_desc = 0,
        .n_value = expected_symbol1_ind,
        };

        symbol_info symbol2 = {
            .n_un = {.n_strx = expected_symbol2_ind},
            .n_type = 0,
            .n_sect = 2,
            .n_desc = 0,
            .n_value = expected_symbol2_ind,
        };

        fseek(file, symtab_command_symoff, SEEK_SET);
        fwrite(&symbol1, sizeof(symbol_info), 1, file);
        fwrite(&symbol2, sizeof(symbol_info), 1, file);

        // Write the string table
        fseek(file, symtab_command_stroff, SEEK_SET);
        fwrite(expected_strtab, symtab_command_strsize, 1, file);

        if (fclose(file) != 0) {
            LOG_ERROR("Error closing file\n");
        }

        section_info *expected_text_section = (section_info*) malloc(sizeof(section_info));
        strcpy(expected_text_section->name, "__text");
        expected_text_section->size = text_section_size;
        expected_text_section->offset = text_section_offset;

        section_info *expected_const_section = (section_info*) malloc(sizeof(section_info));
        strcpy(expected_const_section->name, "__const");
        expected_const_section->size = const_section_size;
        expected_const_section->offset = const_section_offset;

        section_info *expected_symbol_table = (section_info*) malloc(sizeof(section_info));
        strcpy(expected_symbol_table->name, "__symbol_table");
        expected_symbol_table->size = num_syms * sizeof(symbol_info);
        expected_symbol_table->offset = symtab_command_symoff;

        section_info *expected_string_table = (section_info*) malloc(sizeof(section_info));
        strcpy(expected_string_table->name, "__string_table");
        expected_string_table->size = symtab_command_strsize;
        expected_string_table->offset = symtab_command_stroff;

        section_info *expected_sections = (section_info*) malloc(sizeof(section_info) * 4);
        memcpy(&expected_sections[0], expected_text_section, sizeof(section_info));
        memcpy(&expected_sections[1], expected_const_section, sizeof(section_info));
        memcpy(&expected_sections[2], expected_symbol_table, sizeof(section_info));
        memcpy(&expected_sections[3], expected_string_table, sizeof(section_info));

        free(expected_text_section);
        free(expected_const_section);
        free(expected_symbol_table);
        free(expected_string_table);

        expected_macho = (machofile*) malloc(sizeof(machofile));
        expected_macho->macho_header = test_header;
        expected_macho->num_sections = 4;
        expected_macho->sections = expected_sections;

        expected_symtab = (symbol_info*) malloc(num_syms * sizeof(symbol_info));
        expected_symtab[0] = symbol1;
        expected_symtab[1] = symbol2;
    }

    static void TearDownTestSuite() {
        if (expected_macho != NULL) {
            free_macho_file(expected_macho);
        }
        if (expected_symtab != NULL) {
            free(expected_symtab);
        }
        if (remove(TEST_FILE) != 0) {
            LOG_ERROR("Error deleting %s", TEST_FILE);
        }
    }
};
