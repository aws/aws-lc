#ifndef INJECT_HASH_H
#define INJECT_HASH_H

uint8_t* readObject(const char *filename, size_t *size);
int findHash(uint8_t *objectBytes, size_t objectBytesSize, uint8_t* hash, size_t hashSize);
int doAppleOS(char *objectFile, uint8_t **textModule, size_t *textModuleSize, uint8_t **rodataModule, size_t *rodataModuleSize);

#endif
