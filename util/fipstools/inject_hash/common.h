// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef COMMON_H
#define COMMON_H
#ifdef __cplusplus
extern "C"
{
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LOG_ERROR(...) do { \
    fprintf(stderr, "File: %s, Line: %d, ", __FILE__, __LINE__); \
    fprintf(stderr, __VA_ARGS__); \
    fprintf(stderr, "\n"); \
} while(0)

int inject_hash_no_write(const char *o_input, int apple_flag,
                         uint8_t **object_bytes, size_t *object_bytes_size);
int inject_hash(int argc, char *argv[]);

#ifdef __cplusplus
} // extern "C"
#endif
#endif
