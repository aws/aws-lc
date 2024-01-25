// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <stdint.h>

#include "common.h"
#include "macho_parser.h"

/**
 * TODOs
 * use goto for cleaner exits in this and tests (if necessary)
 * make all variable and function names snake case in all files
 * finish tests
*/

// Documentation for the Mach-O structs can be found in macho-o/loader.h and mach-o/nlist.h
int read_macho_file(const char *filename, machofile *macho) {
    FILE *file = NULL;
    load_cmd *load_commands = NULL;
    int ret = 1;

    file = fopen(filename, "rb");
    if (!file) {
        LOG_ERROR("Error opening file %s", filename);
        ret = 0;
        goto end;
    }

    fread(&macho->macho_header, sizeof(macho_header), 1, file);
    if(macho->macho_header.magic != MH_MAGIC_64) {
        LOG_ERROR("File is not a 64-bit Mach-O file");
        ret = 0;
        goto end;
    }

    load_commands = malloc(macho->macho_header.sizeofcmds);
    fread(load_commands, macho->macho_header.sizeofcmds, 1, file);

    // We're only looking for __text, __const in the __TEXT segment, and the string & symbol tables
    macho->num_sections = 4;
    macho->sections = malloc(macho->num_sections * sizeof(section_info));

    // Iterate through load commands again to populate section information
    uint32_t sectionIndex = 0;
    for (uint32_t i = 0; i < macho->macho_header.sizeofcmds / BIT_MODIFIER; i += load_commands[i].cmdsize / BIT_MODIFIER) {
        if (load_commands[i].cmd == LC_SEG) {
            segment_load_cmd *segment = (segment_load_cmd *)&load_commands[i];
            if (strcmp(segment->segname, "__TEXT") == 0) {
                section *sections = (section *)&segment[1];
                for (uint32_t j = 0; j < segment->nsects; j++) {
                    if (strcmp(sections[j].sectname, "__text") == 0 || strcmp(sections[j].sectname, "__const") == 0) {
                        macho->sections[sectionIndex].offset = sections[j].offset;
                        macho->sections[sectionIndex].size = sections[j].size;
                        strcpy(macho->sections[sectionIndex].name, sections[j].sectname);
                        sectionIndex++;
                    }
                }
            }
        } else if (load_commands[i].cmd == LC_SYMTAB) {
            symtab_load_cmd *symtab = (symtab_load_cmd *)&load_commands[i];
            macho->sections[sectionIndex].offset = symtab->symoff;
            macho->sections[sectionIndex].size = symtab->nsyms * sizeof(symbol_info);
            strcpy(macho->sections[sectionIndex].name, "__symbol_table");
            sectionIndex++;
            macho->sections[sectionIndex].offset = symtab->stroff;
            macho->sections[sectionIndex].size = symtab->strsize;
            strcpy(macho->sections[sectionIndex].name, "__string_table");
            sectionIndex++;
        }
    }


end:
    if (load_commands != NULL) {
        free(load_commands);
    }
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

// Takes a filename, machofile struct, the name of the section to get data for, and pointers to size & offset as input
// size and offset pointers are set to the size and offset of the section retrived in the file.
uint8_t* get_macho_section_data(const char *filename, machofile *macho, const char *sectionName, size_t *size, uint32_t *offset) {
    FILE *file = NULL;
    uint8_t *sectionData = NULL;
    uint8_t *ret = NULL;

    file = fopen(filename, "rb");
    if (!file) {
        LOG_ERROR("Error opening file %s", filename);
        goto end;
    }
    for (uint32_t i = 0; i < macho->num_sections; i++) {
        if (strcmp(macho->sections[i].name, sectionName) == 0) {
            sectionData = malloc(macho->sections[i].size);
            if (!sectionData) {
                LOG_ERROR("Error allocating memory for section data");
                goto end;
            }

            fseek(file, macho->sections[i].offset, SEEK_SET);
            fread(sectionData, 1, macho->sections[i].size, file);

            if (size != NULL) {
                *size = macho->sections[i].size;
            }
            if (offset) {
                *offset = macho->sections[i].offset;
            }

            ret = sectionData;
            goto end;
        }
    }

    LOG_ERROR("Section %s not found in macho file %s", sectionName, filename);
end:
    if (file != NULL) {
        fclose(file);
    }
    if (ret == NULL && sectionData != NULL) {
        free(sectionData);
    }
    return ret;
}

uint32_t find_macho_symbol_index(uint8_t *symbolTableData, size_t symbolTableSize, uint8_t *stringTableData, size_t stringTableSize, const char *symbolName, uint32_t *base) {
    char* stringTable = NULL;
    int ret = 0;

    if (symbolTableData == NULL || stringTableData == NULL) {
        LOG_ERROR("Symbol and string table pointers cannot be null to find the symbol index");
        goto end;
    }

    stringTable = malloc(stringTableSize);
    memcpy(stringTable, stringTableData, stringTableSize);

    int found = 0;
    uint32_t index = 0;
    for (uint32_t i = 0; i < symbolTableSize / sizeof(symbol_info); i++) {
        symbol_info *symbol = (symbol_info *)(symbolTableData + i * sizeof(symbol_info));
        if (strcmp(symbolName, &stringTable[symbol->n_un.n_strx]) == 0) {
            if (!found) {
                index = symbol->n_value;
                found = 1;
            } else {
                LOG_ERROR("Duplicate symbol %s found", symbolName);
                goto end;
            }
        }
    }
    if (!found) {
        LOG_ERROR("Requested symbol %s not found", symbolName);
        goto end;
    }
    if (base) {
        index = index - *base;
    }
    ret = index;

end:
    if (stringTable != NULL) {
        free(stringTable);
    }
    return ret;
}
