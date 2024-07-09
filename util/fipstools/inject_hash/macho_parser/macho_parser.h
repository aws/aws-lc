// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef MACHO_PARSER_H
#define MACHO_PARSER_H
#ifdef __cplusplus
extern "C"
{
#endif

#include <mach-o/loader.h>
#include <mach-o/nlist.h>

typedef struct {
    char name[16];
    size_t size;
    uint32_t offset;
} section_info;

typedef struct {
    struct mach_header_64 macho_header;
    section_info *sections;
    uint32_t num_sections;
} machofile;

// read_macho_file reads a Mach-O file [in] and populates a machofile struct [out] with its contents.
// It returns 0 on failure, 1 on success.
int read_macho_file(const char *filename, machofile *macho);

// free_macho_file frees the memory allocated to a machofile struct [in]
void free_macho_file(machofile *macho);

// get_macho_section_data retrieves data from a specific section [in] the provided Mach-O file [in].
// In addition to returning a pointer to the retrieved data, or NULL if it doesn't find said section,
// it also populates the size [out] & offset [out] pointers provided they are not NULL.
uint8_t* get_macho_section_data(const char* filename, machofile *macho, const char *section_name, size_t *size, uint32_t *offset);

// find_macho_symbol_index finds the index of a symbol [in] in the Mach-O file's [in] symbol table.
// It returns the index on success, and 0 on failure.
uint32_t find_macho_symbol_index(uint8_t *symbol_table_data, size_t symbol_table_size, uint8_t *string_table_data, size_t string_table_size, const char *symbol_name, uint32_t *base);

#ifdef __cplusplus
} // extern "C"
#endif
#endif
