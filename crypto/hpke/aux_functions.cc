/* Copyright (c) 2020, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */


#include <math.h>

#include "aux_functions.h"
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

using namespace std;

#define HPKE_MODE 1



int algorithm_secretkeybytes(int alg) {
  int keylen = 0;
  switch (alg) {
    case 0:
      return x25519_SECRETKEYBYTES;
      break;
    case 1:
      return SIKE_SECRETKEYBYTES;
      break;
    case 2:
      return x25519_SIKE_SECRETKEYBYTES;
      break;
    case 3:
      return KYBER_SECRETKEYBYTES;
      break;
    case 4:
      return x25519_KYBER_SECRETKEYBYTES;
      break;
    default:
      break;
  }
  return keylen;
}


int algorithm_publickeybytes(int alg) {
  switch (alg) {
    case 0:
      return x25519_PUBLICKEYBYTES;
      break;
    case 1:
      return SIKE_PUBLICKEYBYTES;
      break;
    case 2:
      return x25519_PUBLICKEYBYTES + SIKE_PUBLICKEYBYTES;
      break;
    case 3:
      return KYBER_PUBLICKEYBYTES;
      break;
    case 4:
      return x25519_KYBER_PUBLICKEYBYTES;
      break;
    default:
      return x25519_PUBLICKEYBYTES + KYBER_PUBLICKEYBYTES;
      break;
  }
  return x25519_PUBLICKEYBYTES + KYBER_PUBLICKEYBYTES;
  ;
}

int algorithm_ciphertextbytes(int alg) {
  int keylen = 0;
  switch (alg) {
    case 0:
      return x25519_PUBLICKEYBYTES;
      break;
    case 1:
      return SIKE_CIPHERTEXTBYTES;
      break;
    case 2:
      return x25519_PUBLICKEYBYTES + SIKE_CIPHERTEXTBYTES;
      break;
    case 3:
      return KYBER_CIPHERTEXTBYTES;
      break;
    case 4:
      return x25519_PUBLICKEYBYTES + KYBER_CIPHERTEXTBYTES;
      break;
    default:
      break;
  }
  return keylen;
}





const EVP_HPKE_KEM *algorithm_kdf(int alg) {
  switch (alg) {
    case 0:
      return EVP_hpke_x25519_hkdf_sha256();
      break;
    case 1:
      return EVP_hpke_SIKE_hkdf_sha256();
      break;
    case 2:
      return EVP_hpke_x25519_SIKE_hkdf_sha256();
      break;
    case 3:
      return EVP_hpke_KYBER_hkdf_sha256();
      break;
    case 4:
      return EVP_hpke_x25519_KYBER_hkdf_sha256();
      break;
    default:
      return EVP_hpke_x25519_hkdf_sha256();
      break;
  }
  return EVP_hpke_x25519_hkdf_sha256();
}


uint64_t cpucycles(void) {  // Access system counter for benchmarking
  unsigned int hi, lo;
  __asm volatile("rdtsc\n\t" : "=a"(lo), "=d"(hi));
  return ((int64_t)lo) | (((int64_t)hi) << 32);
}


void print_info(int aead, int kdf, int alg) {
  printf("\n\n-------------------------------------------------------");

  printf("\nALGORITHM          ->   ");
  switch (alg) {
    case 0:
      printf("x25519");
      break;
    case 1:
      printf("SIKE");
      break;
    case 2:
      printf("x25519 + SIKE");
      break;
    case 3:
      printf("KYBER");
      break;
    case 4:
      printf("x25519 + KYBER");
      break;
    default:
      printf("Should never happen");
      break;
  }


  printf("\nAEAD               ->   ");
  switch (aead) {
    case 0x0001:
      printf("EVP_HPKE_AES_128_GCM");
      break;
    case 0x0002:
      printf("EVP_HPKE_AES_256_GCM");
      break;
    case 0x0003:
      printf("EVP_HPKE_CHACHA20_POLY1305");
      break;
    default:
      printf("Should never happen");
      break;
  }

  printf("\nKDF                ->   ");
  switch (kdf) {
    case 0x0001:
      printf("EVP_HPKE_HKDF_SHA256");
      break;
    default:
      printf("Should never happen");
      break;
  }



  printf("\n");
}




void print_info_file(int aead, int kdf, int alg, std::ofstream& MyFile) {

  MyFile << "\n\n-------------------------------------------------------" << endl;

   MyFile << "ALGORITHM          ->   ";
  switch (alg) {
    case 0:
      MyFile << ("x25519");
      break;
    case 1:
      MyFile << ("SIKE");
      break;
    case 2:
      MyFile << ("x25519 + SIKE");
      break;
    case 3:
      MyFile << ("KYBER");
      break;
    case 4:
      MyFile << ("x25519 + KYBER");
      break;
    default:
      MyFile << ("Should never happen");
      break;
  }


  MyFile << ("\nAEAD               ->   ");
 
  switch (aead) {
    case 0x0001:
      MyFile << ("EVP_HPKE_AES_128_GCM");
      break;
    case 0x0002:
      MyFile << ("EVP_HPKE_AES_256_GCM");
      break;
    case 0x0003:
      MyFile << ("EVP_HPKE_CHACHA20_POLY1305");
      break;
    default:
      MyFile << ("Should never happen");
      break;
  }

  MyFile << ("\nKDF                ->   ");
  switch (kdf) {
    case 0x0001:
      MyFile << ("EVP_HPKE_HKDF_SHA256");
      break;
    default:
      MyFile << ("Should never happen");
      break;
  }

  MyFile << ("\n");
}



void init_plaintext(uint8_t *plaintext, int size) {
  for (int i = 0; i < size; i++) {
    plaintext[i] = (uint8_t)((uint8_t)i % 256);
    // printf("%02x", (uint8_t)plaintext[i]);
  }
}

void print_text(std::vector<uint8_t> cleartext, int cleartext_len) {
  for (int i = 0; i < cleartext_len; i++) {
    printf("%02x ", cleartext.at(i));
  }
  printf("\n");
}