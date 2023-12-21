#ifndef MACHO_PARSER_H
#define MACHO_PARSER_H

#include <mach-o/loader.h>

typedef struct {
    uint32_t offset;
    uint32_t size;
    char *name;
} SectionInfo;

#define LC_SEG LC_SEGMENT_64
#define BIT_MODIFIER 8

typedef struct mach_header_64 MachOHeader;
typedef struct load_command LoadCommand;
typedef struct segment_command_64 SegmentLoadCommand;
typedef struct section_64 SectionHeader;

// MachOHeader is mach_header_64
// LoadCommand is load_command
// SegmentLoadCommand is segment_command_64
// SectionHeader is section_64

typedef struct {
    MachOHeader machHeader;
    LoadCommand *loadCommands;
    SectionInfo *sections;
    uint32_t numSections;
} MachOFile;

int readMachOFile(const char *filename, MachOFile *macho);
void freeMachOFile(MachOFile *macho);
void printSectionInfo(MachOFile *macho);
uint8_t* getSectionData(MachOFile *macho, const char *sectionName, uint32_t *size);

#endif
