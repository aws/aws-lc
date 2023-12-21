#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "inject_hash.h"

size_t readObject(const char *filename, unsigned char **objectBytes) {
    FILE *file = fopen(filename, "rb");

    if (file == NULL) {
        perror("Error opening file");
        return 0;
    }

    fseek(file, 0, SEEK_END);
    size_t file_size = ftell(file);
    fseek(file, 0, SEEK_SET);

    *objectBytes = (unsigned char *)malloc(file_size);

    if (*objectBytes == NULL) {
        perror("Error allocating memory");
        fclose(file);
        return 0;
    }

    size_t bytesRead = fread(*objectBytes, 1, file_size, file);
    fclose(file);

    if (bytesRead != file_size) {
        perror("Error reading file");
        free(*objectBytes);
        return 0;
    }

    return bytesRead;
}

int findHash(unsigned char *objectBytes, size_t objectBytesSize, unsigned char* hash, size_t hashSize) {
    unsigned char *ptr = memmem(objectBytes, objectBytesSize, hash, hashSize);
    if (ptr == NULL) {
        perror("Error finding hash in object");
        return 1;
    }

    printf("Hash found at index: %ld\n", ptr - objectBytes);

    return 0;
}

int main(int argc, char *argv[]) {

    char *ar_input = NULL;
    char *o_input = NULL;
    char *out_path = NULL;
    int apple_flag = 0;

    int opt;
    while ((opt = getopt(argc, argv, "a:o:p::f")) != -1) {
        switch(opt) {
            case 'a':
                ar_input = optarg;
                break;
            case 'o':
                o_input = optarg;
                break;
            case 'p':
                apple_flag = 1;
                break;
            case 'f':
                out_path = optarg;
                break;
            default:
                fprintf(stderr, "Usage: %s [-a in-archive] [-o in-object] [-p apple] [-f out-path]\n", argv[0]);
                exit(EXIT_FAILURE);
        }
    }

    // The below is the real uninitialized hash
    // unsigned char uninitHash[] = {
    //     0xae, 0x2c, 0xea, 0x2a, 0xbd, 0xa6, 0xf3, 0xec, 
    //     0x97, 0x7f, 0x9b, 0xf6, 0x94, 0x9a, 0xfc, 0x83, 
    //     0x68, 0x27, 0xcb, 0xa0, 0xa0, 0x9f, 0x6b, 0x6f, 
    //     0xde, 0x52, 0xcd, 0xe2, 0xcd, 0xff, 0x31, 0x80,
    // };
    
    // This is the initialized hash used for testing
    // 53 39 5f 48 5c 36 d3 1f 77 7b 81 ed e0 dd 86 3c 6e 07 b6 76 f3 e9 34 a2 8c 07 49 b4 65 c5 d3 19
    unsigned char uninitHash[] = {
        0x53, 0x39, 0x5f, 0x48, 0x5c, 0x36, 0xd3, 0x1f,
        0x77, 0x7b, 0x81, 0xed, 0xe0, 0xdd, 0x86, 0x3c,
        0x6e, 0x07, 0xb6, 0x76, 0xf3, 0xe9, 0x34, 0xa2,
        0x8c, 0x07, 0x49, 0xb4, 0x65, 0xc5, 0xd3, 0x19,
    };
    unsigned char *objectBytes = NULL;
    size_t objectBytesSize = 0;
    int ret = 0;

    if (ar_input) {
        // Do something with archive input
    } else if (o_input) {
        // Do something with object input
        objectBytesSize = readObject(o_input, &objectBytes);
        if (objectBytesSize == 0) {
            perror("Error reading file");
            return -1;
        }
    } else {
        fprintf(stderr, "Either -a (archive input) or -o (object input) is required\n");
        exit(EXIT_FAILURE);
    }

    (void) apple_flag;
    (void) out_path;

    printf("Finding hash...\n");
    ret = findHash(objectBytes, objectBytesSize, uninitHash, sizeof(uninitHash));
    printf("Done\n");

    free(objectBytes);
    return ret;
}
