#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>

#include "inject_hash.h"

int readFile(const char *filename, unsigned char *objectBytes) {
    FILE *file = fopen(filename, "rb");

    if (file == NULL) {
        perror("Error opening file");
        return 1;
    }

    fseek(file, 0, SEEK_END);
    long file_size = ftell(file);
    fseek(file, 0, SEEK_SET);

    objectBytes = (unsigned char *)malloc(file_size + 1);

    if (objectBytes == NULL) {
        perror("Error allocating memory");
        fclose(file);
        return 1;
    }

    size_t bytesRead = fread(objectBytes, 1, file_size, file);
    objectBytes[bytesRead] = '\0';

    fclose(file);

    printf("File:\n%s\n", objectBytes);

    return 0;
}

int main(void) {
    const char *filepath = "build/crypto/fipsmodule/bcm.o";
    unsigned char *objectBytes = NULL;
    int ret = 0;

    ret = readFile(filepath, objectBytes);

    free(objectBytes);
    return ret;
}
