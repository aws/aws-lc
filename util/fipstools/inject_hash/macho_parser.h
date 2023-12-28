/* Copyright (c) 2017, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#ifndef MACHO_PARSER_H
#define MACHO_PARSER_H

#include <mach-o/loader.h>
#include <mach-o/nlist.h>

typedef struct {
    uint32_t offset;
    size_t size;
    char *name;
} SectionInfo;

// Since we only support 64-bit architectures on Apple, we don't need to account for any of the 32-bit structures
#define LC_SEG LC_SEGMENT_64
#define BIT_MODIFIER 8

typedef struct mach_header_64 MachOHeader;
typedef struct load_command LoadCommand;
typedef struct segment_command_64 SegmentLoadCommand;
typedef struct symtab_command SymtabLoadCommand;
typedef struct section_64 SectionHeader;
typedef struct nlist_64 nList;

typedef struct {
    MachOHeader machHeader;
    LoadCommand *loadCommands;
    SectionInfo *sections;
    uint32_t numSections;
} MachOFile;

int readMachOFile(const char *filename, MachOFile *macho);
void freeMachOFile(MachOFile *macho);
void printMachOSectionInfo(MachOFile *macho);
SectionInfo* getMachOSectioninfo(MachOFile *macho, const char *sectionName);
uint8_t* getMachOSectionData(char* filename, MachOFile *macho, const char *sectionName, size_t *size, uint32_t *offset);
uint32_t findMachOSymbolIndex(uint8_t *sectionData, size_t sectionSize, uint8_t *stringTableData, size_t stringTableSize, const char *symbolName, uint32_t *base);

#endif
