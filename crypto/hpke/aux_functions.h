

#include <math.h>

#include <openssl/cpucycles.h>
#include <openssl/hpke.h>

#include <cstdint>
#include <limits>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include <openssl/base.h>
#include <openssl/curve25519.h>

#include <openssl/sike_internal.h>

#include <openssl/digest.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/sha.h>
#include <openssl/span.h>

#include "../test/file_test.h"
#include "../test/test_util.h"

#include <fstream> 
#include <stdint.h>
#include <time.h>

#define SIKE_SECRETKEYBYTES \
  374  // MSG_BYTES + SECRETKEY_B_BYTES + CRYPTO_PUBLICKEYBYTES bytes
#define SIKE_PUBLICKEYBYTES 330
#define SIKE_BYTES 16
#define SIKE_CIPHERTEXTBYTES 346  // CRYPTO_PUBLICKEYBYTES + MSG_BYTES bytes


#define x25519_SECRETKEYBYTES X25519_PUBLIC_VALUE_LEN
#define x25519_PUBLICKEYBYTES X25519_PRIVATE_KEY_LEN
#define x25519_BYTES X25519_SHARED_KEY_LEN
#define x25519_CIPHERTEXTBYTES X25519_PUBLIC_VALUE_LEN

#define x25519_SIKE_SECRETKEYBYTES X25519_PUBLIC_VALUE_LEN + 374
#define x25519_SIKE_PUBLICKEYBYTES X25519_PRIVATE_KEY_LEN + 330
#define x25519_SIKE_BYTES X25519_SHARED_KEY_LEN + 16
#define x25519_SIKE_CIPHERTEXTBYTES X25519_PUBLIC_VALUE_LEN + 346


#define x25519_KYBER_SECRETKEYBYTES \
  X25519_PUBLIC_VALUE_LEN + KYBER_SECRETKEYBYTES
#define x25519_KYBER_PUBLICKEYBYTES \
  X25519_PRIVATE_KEY_LEN + KYBER_PUBLICKEYBYTES
#define x25519_KYBER_BYTES X25519_SHARED_KEY_LEN + KYBER_BYTES
#define x25519_KYBER_CIPHERTEXTBYTES \
  X25519_PUBLIC_VALUE_LEN + KYBER_CIPHERTEXTBYTES



using namespace std;



int algorithm_secretkeybytes(int alg);
int algorithm_publickeybytes(int alg);
int algorithm_ciphertextbytes(int alg);
const EVP_HPKE_KEM *algorithm_kdf(int alg);
void print_info(int aead, int kdf, int alg);
void print_info_file(int aead, int kdf, int alg, std::ofstream& MyFile);
void init_plaintext(uint8_t *plaintext, int size);
void print_text(std::vector<uint8_t> cleartext, int cleartext_len);