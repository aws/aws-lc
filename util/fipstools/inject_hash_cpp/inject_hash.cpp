// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <LIEF/LIEF.hpp>
#include <iostream>
#include <string>
#include <vector>
#include <openssl/hmac.h>  
#include <openssl/sha.h>
#include <tool/internal.h>

static const argument_t kArguments[] = {
    {"-in-object", kRequiredArgument, "Input object file path"},
    {"-o", kRequiredArgument, "Output file path"},
    {"-apple", kBooleanArgument, "Apple platform flag"},
    {"", kOptionalArgument, ""}  // Terminating element
};

static void print_usage() {
    std::cout << "Usage: inject_hash_cpp -o output_file -in-object input_file [-apple]" << std::endl;
    PrintUsage(kArguments);
}

int main(int argc, char** argv) {
    // Convert argv to vector of strings, skipping program name (argv[0])
    std::vector<std::string> args;
    for (int i = 1; i < argc; i++) {
        args.push_back(argv[i]);
    }

    args_map_t args_map;
    args_list_t extra_args;

    if (!ParseKeyValueArguments(args_map, extra_args, args, kArguments)) {
        std::cerr << "❌ Failed to parse arguments" << std::endl;
        print_usage();
        return 1;
    }

    std::string test_file;
    if (GetString(&test_file, "--test-file", "", args_map)) {
        std::cout << "=== Test Mode: Calculating hash of file path ===" << std::endl;
        std::cout << "Test file path: " << test_file << std::endl;

        // Calculate HMAC of the file path string
        uint8_t zero_key[64] = {0};
        HMAC_CTX ctx;

        if (!HMAC_Init(&ctx, zero_key, sizeof(zero_key), EVP_sha256())) {
            std::cerr << "HMAC_Init failed" << std::endl;
            return 1;
        }

        if (!HMAC_Update(&ctx, 
                        reinterpret_cast<const uint8_t*>(test_file.data()), 
                        test_file.length())) {
            std::cerr << "HMAC_Update failed" << std::endl;
            return 1;
        }

        std::vector<uint8_t> hash(HMAC_size(&ctx));
        unsigned int hash_len;
        
        if (!HMAC_Final(&ctx, hash.data(), &hash_len)) {
            std::cerr << "HMAC_Final failed" << std::endl;
            return 1;
        }

        // Print hash
        std::cout << "Calculated hash of file path: ";
        for (unsigned int i = 0; i < hash_len; i++) {
            printf("%02x", hash[i]);
        }
        std::cout << std::endl;
        return 0;
    }

    // Get the input and output file paths
    std::string input_file, output_file;
    if (!GetString(&input_file, "-in-object", "", args_map) ||
        !GetString(&output_file, "-o", "", args_map)) {
        std::cerr << "❌ Error getting file paths" << std::endl;
        print_usage();
        return 1;
    }

    // Get the apple flag
    bool is_apple = false;
    GetBoolArgument(&is_apple, "-apple", args_map);

    // Display configuration
    std::cout << "Input file:  " << input_file << std::endl;
    std::cout << "Output file: " << output_file << std::endl;
    if (is_apple) {
        std::cout << "Platform: macOS" << std::endl;
    }
    std::cout << "=== C++ inject_hash started ===" << std::endl;
    if (LIEF::Parser::parse(input_file)) {
        std::cout << "LIEF parser successfully loaded: " << input_file << std::endl;
    } 
    else {
        std::cerr << "LIEF parser failed to load: " << input_file << std::endl;
        return 1;
                }
    std::cout << "LIEF parser loaded successfully" << std::endl;
    
    uint8_t zero_key[64] = {0};
    HMAC_CTX ctx;

    if (!HMAC_Init(&ctx, &zero_key, sizeof(zero_key), EVP_sha256())) {
        std::cerr << "HMAC_Init failed" << std::endl;
        return 1;
    }

    const std::string& input_str = input_file;
    if (!HMAC_Update(&ctx, 
                     reinterpret_cast<const uint8_t*>(input_str.data()), 
                     input_str.length())) {
        std::cerr << "HMAC_Update failed" << std::endl;
        return 1;
    }
    std::vector<uint8_t> calculate_hash(HMAC_size(&ctx));
    
    unsigned int calculate_hash_len;
    if (!HMAC_Final(&ctx, calculate_hash.data(), &calculate_hash_len)) {
        std::cerr << "HMAC_Final failed" << std::endl;
        return 1;
    }
    std::cout << "HMAC hash calculated successfully, the hash is: " << std::endl;     
    for (unsigned int i = 0; i < calculate_hash_len; i++) {
        printf("%02x", calculate_hash[i]);
    } 
    std::cout << std::endl;     

    std::cout << "=== C++ inject_hash completed ===" << std::endl;
    return 0;
}

