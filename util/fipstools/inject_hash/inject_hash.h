#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>


size_t readObject(const char *filename, unsigned char **objectBytes);

int findHash(unsigned char *objectBytes, size_t objectBytesSize, unsigned char* hash, size_t hashSize);
