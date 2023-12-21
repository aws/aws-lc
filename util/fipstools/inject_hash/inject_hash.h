#ifndef INJECT_HASH_H
#define INJECT_HASH_H

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>


size_t readObject(const char *filename, uint8_t **objectBytes);

int findHash(uint8_t *objectBytes, size_t objectBytesSize, uint8_t* hash, size_t hashSize);

#endif
