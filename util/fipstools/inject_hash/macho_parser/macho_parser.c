// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <stdint.h>

#include "common.h"
#include "macho_parser.h"

/**
 * TODOs
 * use goto for cleaner exits
 * make all variable and function names snake case
*/

// Documentation for the Mach-O structs can be found in macho-o/loader.h and mach-o/nlist.h
int read_macho_file(const char *filename, MachOFile *macho) {
    FILE *file = fopen(filename, "rb");
    if (!file) {
        LOG_ERROR("Error opening file %s", filename);
        return 0;
    }

    fread(&macho->machHeader, sizeof(MachOHeader), 1, file);
    if(macho->machHeader.magic != MH_MAGIC_64) {
        LOG_ERROR("File is not a 64-bit Mach-O file");
        return 0;
    }

    LoadCommand *load_commands = malloc(macho->machHeader.sizeofcmds);
    fread(load_commands, macho->machHeader.sizeofcmds, 1, file);

    // We're only looking for __text, __const in the __TEXT segment, and the string & symbol tables
    macho->numSections = 4;
    macho->sections = malloc(macho->numSections * sizeof(SectionInfo));

    // Iterate through load commands again to populate section information
    uint32_t sectionIndex = 0;
    for (uint32_t i = 0; i < macho->machHeader.sizeofcmds / BIT_MODIFIER; i += load_commands[i].cmdsize / BIT_MODIFIER) {
        if (load_commands[i].cmd == LC_SEG) {
            SegmentLoadCommand *segment = (SegmentLoadCommand *)&load_commands[i];
            if (strcmp(segment->segname, "__TEXT") == 0) {
                SectionHeader *sections = (SectionHeader *)&segment[1];
                for (uint32_t j = 0; j < segment->nsects; j++) {
                    if (strcmp(sections[j].sectname, "__text") == 0 || strcmp(sections[j].sectname, "__const") == 0) {
                        macho->sections[sectionIndex].offset = sections[j].offset;
                        macho->sections[sectionIndex].size = sections[j].size;
                        macho->sections[sectionIndex].name = strdup(sections[j].sectname);
                        sectionIndex++;
                    }
                }
            }
        } else if (load_commands[i].cmd == LC_SYMTAB) {
            SymtabLoadCommand *symtab = (SymtabLoadCommand *)&load_commands[i];
            macho->sections[sectionIndex].offset = symtab->symoff;
            macho->sections[sectionIndex].size = symtab->nsyms * sizeof(nList);
            macho->sections[sectionIndex].name = strdup("__symbol_table");
            sectionIndex++;
            macho->sections[sectionIndex].offset = symtab->stroff;
            macho->sections[sectionIndex].size = symtab->strsize;
            macho->sections[sectionIndex].name = strdup("__string_table");
            sectionIndex++;
        }
    }


    free(load_commands);
    fclose(file);
    return 1;
}

void free_macho_file(MachOFile *macho) {
    for (uint32_t i = 0; i < macho->numSections; i++) {
        free(macho->sections[i].name);
    }
    free(macho->sections);
}

void print_macho_section_info(MachOFile *macho) {
    printf("Number of sections: %u\n", macho->numSections);
    for (uint32_t i = 0; i < macho->numSections; i++) {
        printf("Section: %s, Offset: %u, Size: %zu\n", macho->sections[i].name,
               macho->sections[i].offset, macho->sections[i].size);
    }
}

uint8_t* get_macho_section_data(char *filename, MachOFile *macho, const char *sectionName, size_t *size, uint32_t *offset) {
    FILE *file = fopen(filename, "rb");
    if (!file) {
        LOG_ERROR("Error opening file %s", filename);
        return NULL;
    }
    for (uint32_t i = 0; i < macho->numSections; i++) {
        if (strcmp(macho->sections[i].name, sectionName) == 0) {
            uint8_t *sectionData = malloc(macho->sections[i].size);
            if (!sectionData) {
                fclose(file);
                LOG_ERROR("Error allocating memory for section data");
                return NULL;
            }

            fseek(file, macho->sections[i].offset, SEEK_SET);
            fread(sectionData, 1, macho->sections[i].size, file);

            if (size != NULL) {
                *size = macho->sections[i].size;
            }
            if (offset) {
                *offset = macho->sections[i].offset;
            }

            fclose(file);
            return sectionData;
        }
    }

    LOG_ERROR("Section %s not found in macho file %s", sectionName, filename);
    fclose(file);
    return NULL;
}

uint32_t find_macho_symbol_index(uint8_t *symbolTableData, size_t symbolTableSize, uint8_t *stringTableData, size_t stringTableSize, const char *symbolName, uint32_t *base) {
    if (symbolTableData == NULL || stringTableData == NULL) {
        LOG_ERROR("Symbol and string table pointers cannot be null to find the symbol index");
        return 0;
    }

    char* stringTable = malloc(stringTableSize);
    memcpy(stringTable, stringTableData, stringTableSize);

    int found = 0;
    uint32_t index = 0;
    for (uint32_t i = 0; i < symbolTableSize / sizeof(nList); i++) {
        nList *symbol = (nList *)(symbolTableData + i * sizeof(nList));
        if (strcmp(symbolName, &stringTable[symbol->n_un.n_strx]) == 0) {
            if (!found) {
                index = symbol->n_value;
                found = 1;
            } else {
                LOG_ERROR("Duplicate symbol %s found", symbolName);
                return 0;
            }
            
        }
    }

    free(stringTable);
    if (base) {
        index = index - *base;
    }
    return index;
}
