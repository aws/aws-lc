#ifndef INJECT_HASH_H
#define INJECT_HASH_H

size_t readObject(const char *filename, uint8_t **objectBytes);

int findHash(uint8_t *objectBytes, size_t objectBytesSize, uint8_t* hash, size_t hashSize);

#endif
