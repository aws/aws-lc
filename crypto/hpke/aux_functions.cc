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

#include <openssl/cpucycles.h>
#include <openssl/hpke.h>
#include "aux_functions.h"

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

#include <stdint.h>
#include <time.h>
#include <fstream>

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



void print_info_file(int aead, int kdf, int alg, std::ofstream &MyFile) {
  MyFile << "\n\n-------------------------------------------------------"
         << endl;

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



// STATISTICS AUX

float mean(unsigned long long array[], int n) {
  int i;
  unsigned long long sum = 0;
  for (i = 0; i < n; i++)
    sum = sum + array[i];
  return ((float)sum / (float)n);
}


void sort_array(unsigned long long arr[], int n) {
  unsigned long long temp;
  int i, j;
  for (i = n - 1; i >= 0; i--)
    for (j = 0; j < i; j++)
      if (arr[j] >= arr[j + 1]) {
        temp = arr[j];
        arr[j] = arr[j + 1];
        arr[j + 1] = temp;
      }
}

float median(unsigned long long array[], int n) {
  if (n % 2 == 0)
    return ((float)array[n / 2] + (float)array[n / 2 - 1]) / 2;
  else
    return (float)array[n / 2];
}


double standarddeviation(unsigned long long array[], const int n) {
  int j;
  double *max = (double *)malloc(sizeof(double) * n);
  double sum, variance, this_mean;

  this_mean = mean(array, n);
  sum = 0;
  for (j = 0; j < n; j++) {
    max[j] = pow((array[j] - this_mean), 2);
    sum += max[j];
  }
  variance = sum / (j - 1);
  free(max);
  return sqrt(variance);
}


void calculate_quartiles(unsigned long long arr[], int n, float quartiles[4],
                         int quartiles_positions[4]) {
  sort_array(arr, n);
  double Q1 = n / 4.0;
  double Q2 = (2 * n) / 4.0;
  double Q3 = (3 * n) / 4.0;

  int R1 = n / 4;
  int R2 = (n * 2) / 4;
  int R3 = (n * 3) / 4;

  if ((Q1 - R1) == 0) {
    // printf("First quartiles (Q1): %lld\n", arr[R1 - 1]);
    quartiles[0] = arr[R1 - 1];
    quartiles_positions[0] = R1 - 1;
  } else {
    float q1;
    q1 = arr[R1 - 1] + (Q1 - R1) * ((arr[R1] - arr[R1 - 1]));
    // printf("First quartiles (Q1): %.2f\n", q1);
    quartiles[0] = q1;
    quartiles_positions[0] = R1;
  }
  if ((Q2 - R2) == 0) {
    // printf("Second quartiles (Q2): %lld\n", arr[R2 - 1]);
    quartiles[1] = arr[R2 - 1];
    quartiles_positions[1] = R2 - 1;
  } else {
    float q2;
    q2 = arr[R2 - 1] + (Q2 - R2) * ((arr[R2] - arr[R2 - 1]));
    // printf("Second quartiles (Q2): %.2f\n", q2);
    quartiles[1] = q2;
    quartiles_positions[1] = R2;
  }
  if ((Q3 - R3) == 0) {
    // printf("Third quartiles (Q3): %lld\n", arr[R3 - 1]);
    quartiles[2] = arr[R3 - 1];
    quartiles_positions[2] = R3 - 1;
  } else {
    float q3;
    q3 = arr[R3 - 1] + (Q3 - R3) * ((arr[R3] - arr[R3 - 1]));
    // printf("Third quartiles (Q3): %.2f\n", q3);
    quartiles[3] = q3;
    quartiles_positions[2] = R3;
  }
  // printf("Forth quartiles (Q4): %lld\n", arr[n - 1]);
  quartiles[3] = arr[n - 1];
}

void analyze_protocol(uint8_t mode, unsigned long long *arr_cycles_setup_sender,
                      unsigned long long *arr_cycles_setup_recipient,
                      unsigned long long *arr_cycles_seal,
                      unsigned long long *arr_cycles_open, int n,
                      std::ofstream &MyFile) {
  // Analyze setup_sender clock cycles
  MyFile << "set_up_sender           ";
  unsigned long long cycles_set_up_sender_total =
      analyze_statistics(mode, arr_cycles_setup_sender, n, MyFile);

  // Analyze setup_recipient clock cycles
  MyFile << "set_up_recipient        ";
  unsigned long long cycles_set_up_recipient_total =
      analyze_statistics(mode, arr_cycles_setup_recipient, n, MyFile);

  // Analyze seal clock cycles
  MyFile << "seal                      ";
  unsigned long long cycles_seal_total =
      analyze_statistics(mode, arr_cycles_seal, n, MyFile);

  // Analyze open clock cycles
  MyFile << "open                      ";
  unsigned long long cycles_open_total =
      analyze_statistics(mode, arr_cycles_open, n, MyFile);

  // Analyze total protocol clock cycles
  unsigned long long clean_protocol = cycles_set_up_sender_total +
                                      cycles_set_up_recipient_total +
                                      cycles_seal_total + cycles_open_total;
  MyFile << "TOTAL protocol          " << fixed << setprecision(0)
         << clean_protocol / 1000 << "   CCs x10^3\n";

  // Analyze % of clock cycles per HPKE function
  analyze_percentage(cycles_set_up_sender_total, cycles_set_up_recipient_total,
                     cycles_seal_total, cycles_open_total, clean_protocol,
                     MyFile);
}


float analyze_statistics(uint8_t mode, unsigned long long arr_cycles[], int n,
                         std::ofstream &MyFile) {
  sort_array(arr_cycles, n);

  int start_index = n / 4;
  int number_elements = n / 4 * 2;

  // Consider only central 50% of the data -> eliminate quartile I and IV
  float mean_val = mean(arr_cycles + start_index, number_elements);
  if (mode == 1) {
    MyFile << fixed << setprecision(0) << mean_val / 1000 << "   CCs x10^3, ";

    MyFile << "M " << fixed << setprecision(0)
           << median(arr_cycles + start_index, number_elements) / 1000
           << " CCs x10^3, ";

    MyFile << "SD " << fixed << setprecision(0)
           << standarddeviation(arr_cycles + start_index, number_elements)
           << "\n";
  } else {
    MyFile << fixed << setprecision(0) << mean_val / 1000 << "   CCs x10^3\n";
  }

  return mean_val;
}

void analyze_percentage(unsigned long long cycles_set_up_sender_total,
                        unsigned long long cycles_set_up_recipient_total,
                        unsigned long long cycles_seal_total,
                        unsigned long long cycles_open_total,
                        unsigned long long clean_protocol,
                        std::ofstream &MyFile) {
  MyFile << "% set_up_sender         " << fixed << setprecision(3)
         << ((float)(cycles_set_up_sender_total) / ((float)clean_protocol) *
             100)
         << " % \n";

  MyFile << "% set_up_recipient      " << fixed << setprecision(3)
         << ((float)cycles_set_up_recipient_total) / ((float)clean_protocol) *
                100
         << " % \n";

  MyFile << "% seal                  " << fixed << setprecision(3)
         << ((float)cycles_seal_total) / ((float)clean_protocol) * 100
         << "  % \n";

  MyFile << "% open                  " << fixed << setprecision(3)
         << ((float)cycles_open_total) / ((float)clean_protocol) * 100
         << "  % \n";
}



void check_RSA_pt_lengths(int *pt_size) {
  switch (*pt_size) {
    case STARTING_PT_VALUE:
      *pt_size = RSA_PKCS1_PADDING_MAX_PT_RSA2048;
      break;
    case (RSA_PKCS1_PADDING_MAX_PT_RSA2048 * 10):
      *pt_size = RSA_NO_PADDING_MAX_PT_RSA2048;
      break;
    case RSA_NO_PADDING_MAX_PT_RSA2048 * 10:
      *pt_size = RSA_PKCS1_OAEP_PADDING_MAX_PT_RSA2048;
      break;

    case RSA_PKCS1_OAEP_PADDING_MAX_PT_RSA2048 * 10:
      *pt_size = RSA_PKCS1_PADDING_MAX_PT_RSA3072;
      break;

    case RSA_PKCS1_PADDING_MAX_PT_RSA3072 * 10:
      *pt_size = RSA_NO_PADDING_MAX_PT_RSA3072;
      break;

    case RSA_NO_PADDING_MAX_PT_RSA3072 * 10:
      *pt_size = RSA_PKCS1_OAEP_PADDING_MAX_PT_RSA3072;
      break;

    case RSA_PKCS1_OAEP_PADDING_MAX_PT_RSA3072 * 10:
      *pt_size = RSA_PKCS1_PADDING_MAX_PT_RSA4096;
      break;

    case RSA_PKCS1_PADDING_MAX_PT_RSA4096 * 10:
      *pt_size = RSA_NO_PADDING_MAX_PT_RSA4096;
      break;

    case RSA_NO_PADDING_MAX_PT_RSA4096 * 10:
      *pt_size = RSA_PKCS1_OAEP_PADDING_MAX_PT_RSA4096;
      break;

    case RSA_PKCS1_OAEP_PADDING_MAX_PT_RSA4096 * 10:
      *pt_size = 1000;
      break;

    default:
      // Just keep the same value
      break;
  }
}
