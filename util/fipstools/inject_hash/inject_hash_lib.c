// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <unistd.h>

#include "common.h"
#include "macho_parser/macho_parser.h"

#include <openssl/base.h>
#include <openssl/hmac.h>
#include <openssl/mem.h>

static uint8_t* read_object(const char *filename, size_t *size) {
    FILE *file = fopen(filename, "rb");
    uint8_t *object_bytes = NULL;
    if (file == NULL) {
        LOG_ERROR("Error opening file %s", filename);
        goto end;
    }

    fseek(file, 0, SEEK_END);
    size_t file_size = ftell(file);
    fseek(file, 0, SEEK_SET);

    object_bytes = malloc(file_size);
    if (object_bytes == NULL) {
        LOG_ERROR("Error allocating object_bytes memory");
        goto end;
    }

    *size = fread(object_bytes, 1, file_size, file);
    if (*size != file_size) {
        LOG_ERROR("Error reading from file %s", filename);
        free(object_bytes);
        object_bytes = NULL;
        goto end;
    }

end:
    fclose(file);
    return object_bytes;
}

static int write_object(const char *filename, uint8_t *bytes, size_t size) {
    int ret = 0;

    FILE *file = fopen(filename, "wb");
    if (file == NULL) {
        LOG_ERROR("Error opening file %s", filename);
        goto end;
    }

    size_t written = fwrite(bytes, sizeof(uint8_t), size, file);
    if (written != size) {
        LOG_ERROR("Error writing file %s", filename);
        goto end;
    }

    ret = 1;

end:
    fclose(file);
    return ret;
}

static uint32_t find_hash(uint8_t *object_bytes, size_t object_bytes_size, uint8_t *hash, size_t hash_size) {
    uint8_t *ptr = memmem(object_bytes, object_bytes_size, hash, hash_size);
    if (ptr == NULL) {
        LOG_ERROR("Error finding hash in object");
        return 0;
    }

    return ptr - object_bytes;
}

static void size_to_little_endian_bytes(size_t size, uint8_t *result) {
    for (int i = 0; i < 8; i++) {
        result[i] = (size >> (i * 8)) & 0xFF;
    }
}

static int do_apple(const char *object_file, uint8_t **text_module, size_t *text_module_size, uint8_t **rodata_module, size_t *rodata_module_size) {
    uint8_t *text_section = NULL;
    size_t text_section_size;
    uint32_t text_section_offset;

    uint8_t *rodata_section = NULL;
    size_t rodata_section_size;
    uint32_t rodata_section_offset;

    uint8_t *symbol_table = NULL;
    size_t symbol_table_size;

    uint8_t *string_table = NULL;
    size_t string_table_size;

    uint32_t text_start;
    uint32_t text_end;
    uint32_t rodata_start;
    uint32_t rodata_end;

    machofile *macho = NULL;

    int ret = 0;
    
    macho = malloc(sizeof(machofile));
    if (read_macho_file(object_file, macho)) {
        text_section = get_macho_section_data(object_file, macho, "__text", &text_section_size, &text_section_offset);
        if (text_section == NULL) {
            LOG_ERROR("Error getting text_section");
            goto end;
        }
        // Not guaranteed to have a rodata section so we won't error out if this returns NULL
        rodata_section = get_macho_section_data(object_file, macho, "__const", &rodata_section_size, &rodata_section_offset);
        symbol_table = get_macho_section_data(object_file, macho, "__symbol_table", &symbol_table_size, NULL);
        if (symbol_table == NULL) {
            LOG_ERROR("Error getting symbol table");
            goto end;
        }
        string_table = get_macho_section_data(object_file, macho, "__string_table", &string_table_size, NULL);
        if (string_table == NULL) {
            LOG_ERROR("Error getting string table");
            goto end;
        }

        if(!find_macho_symbol_index(symbol_table, symbol_table_size, string_table, string_table_size, "_BORINGSSL_bcm_text_start", &text_section_offset, &text_start)) {
            LOG_ERROR("Could not find .text module start symbol in object");
            goto end;
        }
        if (!find_macho_symbol_index(symbol_table, symbol_table_size, string_table, string_table_size, "_BORINGSSL_bcm_text_end", &text_section_offset, &text_end)) {
            LOG_ERROR("Could not find .text module end symbol in object");
            goto end;
        }
        find_macho_symbol_index(symbol_table, symbol_table_size, string_table, string_table_size, "_BORINGSSL_bcm_rodata_start", &rodata_section_offset, &rodata_start);
        find_macho_symbol_index(symbol_table, symbol_table_size, string_table, string_table_size, "_BORINGSSL_bcm_rodata_end", &rodata_section_offset, &rodata_end);


        if ((!rodata_start) != (!rodata_section)) {
            LOG_ERROR(".rodata start marker inconsistent with rodata section presence");
            goto end;
        }

        if ((!rodata_start) != (!rodata_end)) {
            LOG_ERROR(".rodata marker presence inconsistent");
            goto end;
        }

        if (text_start > text_section_size || text_start > text_end || text_end > text_section_size) {
            LOG_ERROR("Invalid .text module boundaires: start %x, end: %x, max: %zx", rodata_start, rodata_end, rodata_section_size);
            goto end;
        }

        // Get text and rodata modules from text_section/rodata_section using obtained indices
        *text_module_size = text_end - text_start;
        *text_module = malloc(*text_module_size);
        memcpy(*text_module, text_section + text_start, *text_module_size);

        if (rodata_section != NULL) {
            *rodata_module_size = rodata_end - rodata_start;
            *rodata_module = malloc(*rodata_module_size);
            memcpy(*rodata_module, rodata_section + rodata_start, *rodata_module_size);
        }
        ret = 1;
    } else {
        LOG_ERROR("Error reading Mach-O file");
        goto end;
    }

end:
    free(text_section);
    free(rodata_section);
    free(symbol_table);
    free(string_table);
    free(macho->sections);
    free(macho);

    return ret;
}

int inject_hash_no_write(const char *ar_input, const char *o_input, const char *out_path, int apple_flag, uint8_t **object_bytes, size_t *object_bytes_size) {
    int ret = 0;

    uint8_t uninit_hash[] = {
        0xae, 0x2c, 0xea, 0x2a, 0xbd, 0xa6, 0xf3, 0xec, 
        0x97, 0x7f, 0x9b, 0xf6, 0x94, 0x9a, 0xfc, 0x83, 
        0x68, 0x27, 0xcb, 0xa0, 0xa0, 0x9f, 0x6b, 0x6f, 
        0xde, 0x52, 0xcd, 0xe2, 0xcd, 0xff, 0x31, 0x80,
    };

    uint8_t *text_module = NULL;
    size_t text_module_size;
    uint8_t *rodata_module = NULL;
    size_t rodata_module_size;

    uint8_t *calculated_hash = NULL;
    uint8_t length_bytes[8];

    uint32_t hash_index;

    if (ar_input) {
        // TODO: work with an archive, not needed for Apple platforms
    } else {
        *object_bytes = read_object(o_input, object_bytes_size);
        if (object_bytes == NULL) {
            LOG_ERROR("Error reading object bytes from %s", o_input);
            goto end;
        }
    }

    if (apple_flag) {
        if (!do_apple(o_input, &text_module, &text_module_size, &rodata_module, &rodata_module_size)) {
            LOG_ERROR("Error getting text and rodata modules from Apple OS object");
            goto end;
        }
    }
    // TODO: else handle linux, not needed for Apple platforms

    if (text_module == NULL || rodata_module == NULL) {
        LOG_ERROR("Error getting text or rodata section");
        goto end;
    }

    hash_index = find_hash(*object_bytes, *object_bytes_size, uninit_hash, sizeof(uninit_hash));
    if (!hash_index) {
        LOG_ERROR("Error finding hash");
        goto end;
    }

    uint8_t zero_key[64] = {0};
    HMAC_CTX ctx;
    if (!HMAC_Init(&ctx, &zero_key, sizeof(zero_key), EVP_sha256())) {
        LOG_ERROR("Error in HMAC_Init()");
        goto end;
    }

    if(rodata_module != NULL) {
        size_to_little_endian_bytes(text_module_size, length_bytes);
        if (!HMAC_Update(&ctx, length_bytes, 8)) {
            LOG_ERROR("Error in HMAC_Update() of textModuleSize");
            goto end;
        }
        if (!HMAC_Update(&ctx, text_module, text_module_size)) {
            LOG_ERROR("Error in HMAC_Update() of textModule");
            goto end;
        }
        size_to_little_endian_bytes(rodata_module_size, length_bytes);
        if (!HMAC_Update(&ctx, length_bytes, 8)) {
            LOG_ERROR("Error in HMAC_Update() of rodataModuleSize");
            goto end;
        }
        if (!HMAC_Update(&ctx, rodata_module, rodata_module_size)) {
            LOG_ERROR("Error in HMAC_Update() of rodataModule");
            goto end;
        }
    } else {
        if (!HMAC_Update(&ctx, text_module, text_module_size)) {
            LOG_ERROR("Error in HMAC_Update() of textModule");
            goto end;
        }
    }

    calculated_hash = malloc(HMAC_size(&ctx));
    unsigned int calculated_hash_len;
    if (!HMAC_Final(&ctx, calculated_hash, &calculated_hash_len)) {
        LOG_ERROR("Error in HMAC_Final()");
        goto end;
    }

    memcpy(*object_bytes + hash_index, calculated_hash, calculated_hash_len);

    ret = 1;

end:
    free(text_module);
    free(rodata_module);
    // free(object_bytes);
    free(calculated_hash);
    return ret;
}

int inject_hash(int argc, char *argv[]) {
    char *ar_input = NULL;
    char *o_input = NULL;
    char *out_path = NULL;
    int apple_flag = 0;

    int ret = 0;

    uint8_t *object_bytes = NULL;
    size_t object_bytes_size;

    int opt;
    while ((opt = getopt(argc, argv, "a:o:p:f")) != -1) {
        switch(opt) {
            case 'a':
                ar_input = optarg;
                break;
            case 'o':
                o_input = optarg;
                break;
            case 'p':
                out_path = optarg;
                break;
            case 'f':
                apple_flag = 1;
                break;
            case '?':
            default:
                LOG_ERROR("Usage: %s [-a in-archive] [-o in-object] [-p out-path] [-f apple-flag]", argv[0]);
                goto end;
        }
    }

    if ((ar_input == NULL && o_input == NULL) || out_path == NULL) {
        LOG_ERROR("Usage: %s [-a in-archive] [-o in-object] [-p out-path] [-f apple-flag]", argv[0]);
        LOG_ERROR("Note that either the -a or -o option and -p options are required.");
        goto end;
    }

    if (!inject_hash_no_write(ar_input, o_input, out_path, apple_flag, &object_bytes, &object_bytes_size)) {
        LOG_ERROR("Error encountered while injecting hash");
        goto end;
    }

    if (!write_object(out_path, object_bytes, object_bytes_size)) {
        LOG_ERROR("Error writing file %s", out_path);
        goto end;
    }

    ret = 1;
end:
    free(object_bytes);
    return ret;
}
