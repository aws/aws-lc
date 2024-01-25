// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef MACHO_PARSER_H
#define MACHO_PARSER_H

#include <mach-o/loader.h>
#include <mach-o/nlist.h>

typedef struct {
    char name[16];
    size_t size;
    uint32_t offset;
} section_info;

// Since we only support 64-bit architectures on Apple, we don't need to account for any of the 32-bit structures
#define LC_SEG LC_SEGMENT_64
#define BIT_MODIFIER 8

typedef struct mach_header_64 macho_header;
typedef struct load_command load_cmd;
typedef struct segment_command_64 segment_load_cmd;
typedef struct symtab_command symtab_load_cmd;
typedef struct section_64 section;
typedef struct nlist_64 symbol_info;

typedef struct {
    macho_header macho_header;
    section_info *sections;
    uint32_t num_sections;
} machofile;

int read_macho_file(const char *filename, machofile *macho);
void free_macho_file(machofile *macho);
void print_macho_section_info(machofile *macho);
uint8_t* get_macho_section_data(const char* filename, machofile *macho, const char *section_name, size_t *size, uint32_t *offset);
uint32_t find_macho_symbol_index(uint8_t *symbol_table_data, size_t symbol_table_size, uint8_t *string_table_data, size_t string_table_size, const char *symbol_name, uint32_t *base);

#endif
