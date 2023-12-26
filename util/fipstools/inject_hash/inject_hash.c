#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>

#include "inject_hash.h"
#include "macho_parser.h"

uint8_t* readObject(const char *filename, size_t *size) {
    FILE *file = fopen(filename, "rb");

    if (file == NULL) {
        perror("Error opening file");
        return 0;
    }

    fseek(file, 0, SEEK_END);
    size_t file_size = ftell(file);
    fseek(file, 0, SEEK_SET);

    uint8_t *objectBytes = (uint8_t *)malloc(file_size);

    if (objectBytes == NULL) {
        perror("Error allocating memory");
        fclose(file);
        return 0;
    }

    *size = fread(objectBytes, 1, file_size, file);
    fclose(file);

    if (*size != file_size) {
        perror("Error reading file");
        free(objectBytes);
        return 0;
    }

    return objectBytes;
}

int findHash(uint8_t *objectBytes, size_t objectBytesSize, uint8_t* hash, size_t hashSize) {
    uint8_t *ptr = memmem(objectBytes, objectBytesSize, hash, hashSize);
    if (ptr == NULL) {
        perror("Error finding hash in object");
        return 1;
    }

    printf("Hash found at index: %ld\n", ptr - objectBytes);

    return 1;
}

int main(int argc, char *argv[]) {

    char *arInput = NULL;
    char *oInput = NULL;
    char *outPath = NULL;
    int appleFlag = 0;

    int opt;
    while ((opt = getopt(argc, argv, "a:o:p:f")) != -1) {
        switch(opt) {
            case 'a':
                arInput = optarg;
                break;
            case 'o':
                oInput = optarg;
                break;
            case 'p':
                outPath = optarg;
                break;
            case 'f':
                appleFlag = 1;
                break;
            case '?':
            default:
                fprintf(stderr, "Usage: %s [-a in-archive] [-o in-object] [-p out-path] [-f apple-flag]\n", argv[0]);
                exit(EXIT_FAILURE);
        }
    }

    if ((arInput == NULL && oInput == NULL) || outPath == NULL) {
        fprintf(stderr, "Usage: %s [-a in-archive] [-o in-object] [-p out-path] [-f apple-flag]\n", argv[0]);
        fprintf(stderr, "Note that either the -a or -o option and -p options are required.\n");
        exit(EXIT_FAILURE);
    }

    // The below is the real uninitialized hash
    // uint8_t uninitHash[] = {
    //     0xae, 0x2c, 0xea, 0x2a, 0xbd, 0xa6, 0xf3, 0xec, 
    //     0x97, 0x7f, 0x9b, 0xf6, 0x94, 0x9a, 0xfc, 0x83, 
    //     0x68, 0x27, 0xcb, 0xa0, 0xa0, 0x9f, 0x6b, 0x6f, 
    //     0xde, 0x52, 0xcd, 0xe2, 0xcd, 0xff, 0x31, 0x80,
    // };
    
    // This is the initialized hash used for testing
    uint8_t uninitHash[] = {
        0x53, 0x39, 0x5f, 0x48, 0x5c, 0x36, 0xd3, 0x1f,
        0x77, 0x7b, 0x81, 0xed, 0xe0, 0xdd, 0x86, 0x3c,
        0x6e, 0x07, 0xb6, 0x76, 0xf3, 0xe9, 0x34, 0xa2,
        0x8c, 0x07, 0x49, 0xb4, 0x65, 0xc5, 0xd3, 0x19,
    };
    uint8_t *objectBytes = NULL;
    size_t objectBytesSize = 0;

    if (arInput) {
        // Do something with archive input
    } else {
        objectBytes = readObject(oInput, &objectBytesSize);
        if (objectBytesSize == 0) {
            perror("Error reading file");
            exit(EXIT_FAILURE);
        }
    }


    uint8_t *textSection = NULL;
    size_t textSectionSize = 0;
    uint8_t *rodataSection = NULL;
    size_t rodataSectionSize = 0;
    uint8_t *symbolTable = NULL;
    size_t symbolTableSize = 0;
    uint8_t *stringTable = NULL;
    size_t stringTableSize = 0;

    int textStart = 0;
    int textEnd = 0;
    int rodataStart = 0;
    int rodataEnd = 0;

    if (appleFlag == 1) {
        // Handle Apple
        MachOFile macho;
        if (readMachOFile(oInput, &macho)) {
            printSectionInfo(&macho);
            textSection = getSectionData(oInput, &macho, "__text", &textSectionSize);
            if (!textSection) {
                perror("Error getting text section");
                exit(EXIT_FAILURE);
            }
            rodataSection = getSectionData(oInput, &macho, "__const", &rodataSectionSize);
            if (!rodataSection) {
                perror("Error getting rodata section");
                exit(EXIT_FAILURE);
            }
            symbolTable = getSectionData(oInput, &macho, "__symbol_table", &symbolTableSize);
            if(!symbolTable) {
                perror("Error getting symbol table");
                exit(EXIT_FAILURE);
            }
            stringTable = getSectionData(oInput, &macho, "__string_table", &stringTableSize);
            if(!stringTable) {
                perror("Error getting string table");
                exit(EXIT_FAILURE);
            }
            freeMachOFile(&macho);

            textStart = findSymbolIndex(symbolTable, symbolTableSize, stringTable, stringTableSize, "_BORINGSSL_bcm_text_start");
            textEnd = findSymbolIndex(symbolTable, symbolTableSize, stringTable, stringTableSize, "_BORINGSSL_bcm_text_end");
            rodataStart = findSymbolIndex(symbolTable, symbolTableSize, stringTable, stringTableSize, "_BORINGSSL_bcm_rodata_start");
            rodataEnd = findSymbolIndex(symbolTable, symbolTableSize, stringTable, stringTableSize, "_BORINGSSL_bcm_rodata_end");

            if (!textStart || !textEnd || !rodataStart || !rodataEnd) {
                perror("Error finding symbol indices:\ntextStart: %s\ntextEnd: %s\nrodataStart: %s\n rodataEnd: %s\n");
                exit(EXIT_FAILURE);
            }
        } else {
            perror("Error reading Mach-O file");
            exit(EXIT_FAILURE);
        }
    } else {
        // Handle Linux
    }

    if(textSection == NULL || rodataSection == NULL) {
        perror("Error getting text or rodata section");
        exit(EXIT_FAILURE);
    }
    
    printf("textStart location %d\n", textStart);
    printf("textEnd location %d\n", textEnd);
    printf("rodataStart location %d\n", rodataStart);
    printf("rodataEnd location %d\n", rodataEnd);

    // looks like the above are the indices in object data representing text and rodata modules?

    (void) outPath;

    printf("Finding placeholder hash...\n");
    if (!findHash(objectBytes, objectBytesSize, uninitHash, sizeof(uninitHash))) {
        perror("Error finding hash");
        exit(EXIT_FAILURE);
    }
    printf("Done\n");

    free(objectBytes);
    return EXIT_SUCCESS;
}
