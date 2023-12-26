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

int doAppleOS(char *objectFile, uint8_t **textModule, size_t *textModuleSize, uint8_t **rodataModule, size_t *rodataModuleSize) {
    uint8_t *textSection;
    size_t textSectionSize;
    uint32_t textSectionOffset;

    uint8_t *rodataSection;
    size_t rodataSectionSize;
    uint32_t rodataSectionOffset;

    uint8_t *symbolTable;
    size_t symbolTableSize;

    uint8_t *stringTable;
    size_t stringTableSize;

    uint32_t textStart;
    uint32_t textEnd;
    uint32_t rodataStart;
    uint32_t rodataEnd;

    MachOFile macho;

    if (readMachOFile(objectFile, &macho)) {
        printMachOSectionInfo(&macho);
        textSection = getMachOSectionData(objectFile, &macho, "__text", &textSectionSize, &textSectionOffset);
        if (!textSection) {
            perror("Error getting text section");
            exit(EXIT_FAILURE);
        }
        rodataSection = getMachOSectionData(objectFile, &macho, "__const", &rodataSectionSize, &rodataSectionOffset);
        if (!rodataSection) {
            perror("Error getting rodata section");
            exit(EXIT_FAILURE);
        }
        symbolTable = getMachOSectionData(objectFile, &macho, "__symbol_table", &symbolTableSize, NULL);
        if(!symbolTable) {
            perror("Error getting symbol table");
            exit(EXIT_FAILURE);
        }
        stringTable = getMachOSectionData(objectFile, &macho, "__string_table", &stringTableSize, NULL);
        if(!stringTable) {
            perror("Error getting string table");
            exit(EXIT_FAILURE);
        }
        freeMachOFile(&macho);

        textStart = findMachOSymbolIndex(symbolTable, symbolTableSize, stringTable, stringTableSize, "_BORINGSSL_bcm_text_start", &textSectionOffset);
        textEnd = findMachOSymbolIndex(symbolTable, symbolTableSize, stringTable, stringTableSize, "_BORINGSSL_bcm_text_end", &textSectionOffset);
        rodataStart = findMachOSymbolIndex(symbolTable, symbolTableSize, stringTable, stringTableSize, "_BORINGSSL_bcm_rodata_start", &rodataSectionOffset);
        rodataEnd = findMachOSymbolIndex(symbolTable, symbolTableSize, stringTable, stringTableSize, "_BORINGSSL_bcm_rodata_end", &rodataSectionOffset);

        if (!textStart || !textEnd) {
            perror("Could not find .text module boundaries in object\n");
            exit(EXIT_FAILURE);
        }

        if ((!rodataStart) != (!rodataSection)) {
            perror(".rodata start marker inconsistent with rodata section presence\n");
            exit(EXIT_FAILURE);
        }

        if ((!rodataStart) != (!rodataEnd)) {
            perror(".rodata marker presence inconsistent\n");
            exit(EXIT_FAILURE);
        }

        if (textStart > textSectionSize || textStart > textEnd || textEnd > textSectionSize) {
            fprintf(stderr, "invalid module __text boundaries: start: %x, end: %x, max: %zx", textStart, textEnd, textSectionSize);
            exit(EXIT_FAILURE);
        }

        if (rodataSection && (rodataStart > rodataSectionSize || rodataStart > rodataEnd || rodataEnd > rodataSectionSize)) {
            fprintf(stderr, "invalid module __rodata boundaries: start: %x, end: %x, max: %zx", rodataStart, rodataEnd, rodataSectionSize);
            exit(EXIT_FAILURE);
        }

        // Get text and rodata modules from textSection/rodataSection using the obtained indices
        *textModuleSize = textEnd - textStart;
        *textModule = (uint8_t *)malloc(*textModuleSize);
        memcpy(*textModule, textSection + textStart, *textModuleSize);

        if (rodataSection) {
            *rodataModuleSize = rodataEnd - rodataStart;
            *rodataModule = (uint8_t *)malloc(*rodataModuleSize);
            memcpy(*rodataModule, rodataSection + rodataStart, *rodataModuleSize);
        }
    } else {
        perror("Error reading Mach-O file");
        return 0;
    }

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
    size_t objectBytesSize;

    if (arInput) {
        // Do something with archive input
    } else {
        objectBytes = readObject(oInput, &objectBytesSize);
        if (!objectBytesSize) {
            perror("Error reading file");
            exit(EXIT_FAILURE);
        }
    }

    uint8_t *textModule = NULL;
    size_t textModuleSize;
    uint8_t *rodataModule = NULL;
    size_t rodataModuleSize;
    if (appleFlag == 1) {
        if (!doAppleOS(oInput, &textModule, &textModuleSize, &rodataModule, &rodataModuleSize)) {
            perror("Error getting text and rodata modules from Apple OS object");
            exit(EXIT_FAILURE);
        }
    } else {
        // Handle Linux
    }

    if(textModule == NULL || rodataModule == NULL) {
        perror("Error getting text or rodata section");
        exit(EXIT_FAILURE);
    }

    (void) outPath;

    printf("Finding placeholder hash...\n");
    if (!findHash(objectBytes, objectBytesSize, uninitHash, sizeof(uninitHash))) {
        perror("Error finding hash");
        exit(EXIT_FAILURE);
    }
    printf("Done\n");

    free(textModule);
    free(rodataModule);
    free(objectBytes);
    return EXIT_SUCCESS;
}
