#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "macho_parser.h"

int readMachOFile(const char *filename, MachOFile *macho) {
    FILE *file = fopen(filename, "rb");
    if (!file) {
        perror("Error opening file");
        return 0;
    }

    // Read Mach-O header
    fread(&macho->machHeader, sizeof(MachOHeader), 1, file);
    printf("Header Info:\n");
    printf("Number of Commands: %d\n", macho->machHeader.ncmds);
    printf("Size of Commands: %d\n", macho->machHeader.sizeofcmds);

    // Allocate memory for load commands
    macho->loadCommands = (LoadCommand *)malloc(macho->machHeader.sizeofcmds);
    fread(macho->loadCommands, macho->machHeader.sizeofcmds, 1, file);

    // Iterate through load commands to find sections
    macho->numSections = 0;
    for (uint32_t i = 0; i < macho->machHeader.sizeofcmds / BIT_MODIFIER; i += macho->loadCommands[i].cmdsize / BIT_MODIFIER) {
        if (macho->loadCommands[i].cmd == LOAD_COMMAND_SEG) {
            SegmentLoadCommand *segment = (SegmentLoadCommand *)&macho->loadCommands[i];
            macho->numSections += segment->nsects;
            printf("segment->name %s\n", segment->segname);
            printf("segment->nsects: %d\n", segment->nsects);
        }
    }

    // Allocate memory for section information
    macho->sections = (SectionInfo *)malloc(macho->numSections * sizeof(SectionInfo));

    uint32_t sectionIndex = 0;

    for (uint32_t i = 0; i < macho->machHeader.sizeofcmds / BIT_MODIFIER; i += macho->loadCommands[i].cmdsize / BIT_MODIFIER) {
        if (macho->loadCommands[i].cmd == LOAD_COMMAND_SEG) {
            SegmentLoadCommand *segment = (SegmentLoadCommand *)&macho->loadCommands[i];
            for (uint32_t j = 0; j < segment->nsects; j++) {
                SectionHeader *section = (SectionHeader *)(file + segment->fileoff) + j;
                macho->sections[sectionIndex].offset = section->offset;
                macho->sections[sectionIndex].size = section->size;
                macho->sections[sectionIndex].name = strdup(section->sectname);
                sectionIndex++;
            }
        }
    }

    fclose(file);
    return 1;
}

void freeMachOFile(MachOFile *macho) {
    free(macho->loadCommands);

    for (uint32_t i = 0; i < macho->numSections; ++i) {
        free(macho->sections[i].name);
    }
    free(macho->sections);
}

void printSectionInfo(MachOFile *macho) {
    printf("Number of sections: %u\n", macho->numSections);
    for (uint32_t i = 0; i < macho->numSections; ++i) {
        printf("Section: %s, Offset: %u, Size: %u\n", macho->sections[i].name,
               macho->sections[i].offset, macho->sections[i].size);
    }
}

uint8_t* getSectionData(MachOFile *macho, const char *sectionName, uint32_t *size) {
    for (uint32_t i = 0; i < macho->numSections; ++i) {
        if (strcmp(macho->sections[i].name, sectionName) == 0) {
            FILE *file = fopen("your_macho_file", "rb");
            if (!file) {
                perror("Error opening file");
                return NULL;
            }

            uint8_t *sectionData = (uint8_t *)malloc(macho->sections[i].size);
            if (!sectionData) {
                fclose(file);
                perror("Memory allocation error");
                return NULL;
            }

            fseek(file, macho->sections[i].offset, SEEK_SET);
            fread(sectionData, 1, macho->sections[i].size, file);

            fclose(file);

            if (size != NULL) {
                *size = macho->sections[i].size;
            }

            return sectionData;
        }
    }

    // Section not found
    return NULL;
}
