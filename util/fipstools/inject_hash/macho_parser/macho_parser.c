// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <stdint.h>

#include "common.h"
#include "macho_parser.h"

// Documentation for the Mach-O structs can be found in macho-o/loader.h and mach-o/nlist.h
int read_macho_file(const char *filename, machofile *macho) {
    FILE *file = NULL;
    struct load_command *load_commands = NULL;
    uint32_t bytes_read;
    int ret = 0;

    file = fopen(filename, "rb");
    if (file == NULL) {
        LOG_ERROR("Error opening file %s", filename);
        goto end;
    }

    bytes_read = fread(&macho->macho_header, 1, sizeof(struct mach_header_64), file);
    if (bytes_read != sizeof(struct mach_header_64)) {
        LOG_ERROR("Error reading macho_header from file %s", filename);
        goto end;
    }
    if (macho->macho_header.magic != MH_MAGIC_64) {
        LOG_ERROR("File is not a 64-bit Mach-O file");
        goto end;
    }

    load_commands = malloc(macho->macho_header.sizeofcmds);
    if (load_commands == NULL) {
        LOG_ERROR("Error allocating memory for load_commands");
        goto end;
    }
    bytes_read = fread(load_commands, 1, macho->macho_header.sizeofcmds, file);
    if (bytes_read != macho->macho_header.sizeofcmds) {
        LOG_ERROR("Error reading load commands from file %s", filename);
        goto end;
    }

    // We're only looking for __text, __const in the __TEXT segment, and the string & symbol tables
    macho->num_sections = 4;
    macho->sections = malloc(macho->num_sections * sizeof(section_info));
    if (macho->sections == NULL) {
        LOG_ERROR("Error allocating memory for macho sections");
    }

    uint32_t section_index = 0;
    for (uint32_t i = 0; i < macho->macho_header.sizeofcmds / BIT_MODIFIER; i += load_commands[i].cmdsize / BIT_MODIFIER) {
        if (load_commands[i].cmd == LC_SEGMENT_64) {
            struct segment_command_64 *segment = (struct segment_command_64 *)&load_commands[i];
            if (strcmp(segment->segname, "__TEXT") == 0) {
                struct section_64 *sections = (struct section_64 *)&segment[1];
                for (uint32_t j = 0; j < segment->nsects; j++) {
                    if (strcmp(sections[j].sectname, "__text") == 0 || strcmp(sections[j].sectname, "__const") == 0) {
                        macho->sections[section_index].offset = sections[j].offset;
                        macho->sections[section_index].size = sections[j].size;
                        strcpy(macho->sections[section_index].name, sections[j].sectname);
                        section_index++;
                    }
                }
            }
        } else if (load_commands[i].cmd == LC_SYMTAB) {
            struct symtab_command *symtab = (struct symtab_command *)&load_commands[i];
            macho->sections[section_index].offset = symtab->symoff;
            macho->sections[section_index].size = symtab->nsyms * sizeof(struct nlist_64);
            strcpy(macho->sections[section_index].name, "__symbol_table");
            section_index++;
            macho->sections[section_index].offset = symtab->stroff;
            macho->sections[section_index].size = symtab->strsize;
            strcpy(macho->sections[section_index].name, "__string_table");
            section_index++;
        }

        if (section_index > 4) {
            LOG_ERROR("Duplicate sections found, %d", section_index);
            goto end;
        }
    }
    if (section_index != 4) {
        LOG_ERROR("Not all required sections found");
        goto end;
    }

    ret = 1;
end:
    free(load_commands);
    if (file != NULL) {
        fclose(file);
    }
    return ret;
}

void free_macho_file(machofile *macho) {
    free(macho->sections);
    free(macho);
    macho = NULL;
}

uint8_t* get_macho_section_data(const char *filename, machofile *macho, const char *section_name, size_t *size, uint32_t *offset) {
    FILE *file = NULL;
    uint8_t *section_data = NULL;
    uint8_t *ret = NULL;
    uint32_t bytes_read;

    file = fopen(filename, "rb");
    if (file == NULL) {
        LOG_ERROR("Error opening file %s", filename);
        goto end;
    }
    for (uint32_t i = 0; i < macho->num_sections; i++) {
        if (strcmp(macho->sections[i].name, section_name) == 0) {
            section_data = malloc(macho->sections[i].size);
            if (section_data == NULL) {
                LOG_ERROR("Error allocating memory for section data");
                goto end;
            }

            fseek(file, macho->sections[i].offset, SEEK_SET);
            bytes_read = fread(section_data, 1, macho->sections[i].size, file);
            if (bytes_read != macho->sections[i].size) {
                LOG_ERROR("Error reading section data from file %s", filename);
                goto end;
            }

            if (size != NULL) {
                *size = macho->sections[i].size;
            }
            if (offset != NULL) {
                *offset = macho->sections[i].offset;
            }

            ret = section_data;
            goto end;
        }
    }

    LOG_ERROR("Section %s not found in macho file %s", section_name, filename);
end:
    if (file != NULL) {
        fclose(file);
    }
    if (ret == NULL) {
        free(section_data);
    }
    return ret;
}

uint32_t find_macho_symbol_index(uint8_t *symbol_table_data, size_t symbol_table_size, uint8_t *string_table_data, size_t string_table_size, const char *symbol_name, uint32_t *base) {
    char* string_table = NULL;
    int ret = 0;

    if (symbol_table_data == NULL || string_table_data == NULL) {
        LOG_ERROR("Symbol and string table pointers cannot be null to find the symbol index");
        goto end;
    }

    string_table = malloc(string_table_size);
    if (string_table == NULL) {
        LOG_ERROR("Error allocating memory for string table");
        goto end;
    }
    memcpy(string_table, string_table_data, string_table_size);

    int found = 0;
    uint32_t index = 0;
    for (uint32_t i = 0; i < symbol_table_size / sizeof(struct nlist_64); i++) {
        struct nlist_64 *symbol = (struct nlist_64 *)(symbol_table_data + i * sizeof(struct nlist_64));
        if (strcmp(symbol_name, &string_table[symbol->n_un.n_strx]) == 0) {
            if (found == 0) {
                index = symbol->n_value;
                found = 1;
            } else {
                LOG_ERROR("Duplicate symbol %s found", symbol_name);
                goto end;
            }
        }
    }
    if (found == 0) {
        LOG_ERROR("Requested symbol %s not found", symbol_name);
        goto end;
    }
    if (base != NULL) {
        index = index - *base;
    }
    ret = index;

end:
    free(string_table);
    return ret;
}
