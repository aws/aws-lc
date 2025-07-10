#ifndef TEST_SHA256_H
#define TEST_SHA256_H

#include <cstdint>
#include <cstddef>

class TestSHA256 {
public:
    static const size_t DIGEST_LENGTH = 32;
    
    static void calculate_hash(const uint8_t* data, 
                             size_t length, 
                             uint8_t* out);
};

#endif
