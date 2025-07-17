#include <LIEF/LIEF.hpp>
#include <iostream>
#include <string>
#include <vector>
#include <openssl/hmac.h>  
#include <openssl/digest.h>
#include <openssl/sha.h>

int main(int argc, char** argv) {
    std::cout << "\n=== C++ inject_hash starting ===" << std::endl;
    std::cout << "Testing LIEF integration..." << std::endl;

    const char* binary_path = nullptr;
    for (int i = 1; i < argc - 1; i++) {
        if (strcmp(argv[i], "-in-object") == 0) {
            binary_path = argv[i + 1];
            break;
        }
    }
    if (!binary_path) {
        std::cerr << "Error: -in-object argument not provided" << std::endl;
        return 1;
    }
    
       
    
    std::cout << "Binary Path Loaded" << binary_path << std::endl;
    if (auto binary = LIEF::Parser::parse(binary_path)) {
        std::cout << "LIEF parser successfully loaded: " << binary_path << std::endl;
    } 
    else {
        std::cerr << "LIEF parser failed to load: " << binary_path << std::endl;
        return 1;
                }
    std::cout << "LIEF parser loaded successfully" << std::endl;
    
    uint8_t zero_key[64] = {0};
    HMAC_CTX ctx;

    if (!HMAC_Init(&ctx, &zero_key, sizeof(zero_key), EVP_sha256())) {
        std::cerr << "HMAC_Init failed" << std::endl;
        return 1;
    }
    if (!HMAC_Update(&ctx, (const uint8_t*)binary_path, strlen(binary_path))) {
        std::cerr << "HMAC_Update failed" << std::endl;
        return 1;
    }
    std::vector<uint8_t> calculate_hash(HMAC_size(&ctx));
    
    unsigned int calculate_hash_len;
    if (!HMAC_Final(&ctx, calculate_hash.data(), &calculate_hash_len)) {
        std::cerr << "HMAC_Final failed" << std::endl;
    }
    std::cout << "HMAC hash calculated successfully, the hash is: " << std::endl;     
    for (unsigned int i = 0; i < calculate_hash_len; i++) {
        printf("%02x", calculate_hash[i]);
    } 
    std::cout << std::endl;     

    std::cout << "=== C++ inject_hash completed ===" << std::endl;
    return 0;
}

