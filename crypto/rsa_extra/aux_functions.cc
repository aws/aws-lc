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

#include <stdint.h>
#include <time.h>
#include <fstream>
#include <iomanip>
#include <iostream>
#include "aux_functions.h"

using namespace std;


#define RSA_PKCS1_PADDING 1
#define RSA_NO_PADDING 3
#define RSA_PKCS1_OAEP_PADDING 4



void print_padding_mode_RSA(int mode, std::ofstream &MyFile, int n) {
  switch (mode) {
    case RSA_PKCS1_PADDING:
      MyFile << ("Padding Mode        ->      RSA_PKCS1_PADDING\n");
      break;
    case RSA_NO_PADDING:
      MyFile << ("Number Tests        ->      RSA_NO_PADDING\n");
      break;
    case RSA_PKCS1_OAEP_PADDING:
      MyFile << ("Number Tests        ->      RSA_PKCS1_OAEP_PADDING\n");
      break;


    default:
      break;
  }
  MyFile << "Number Tests        ->      " << n << "\n\n";
}


void init_plaintext_RSA(uint8_t *plaintext, int size) {
  for (int i = 0; i < size; i++) {
    plaintext[i] = (uint8_t)((uint8_t)i % 256);
    // printf("%02x", (uint8_t)plaintext[i]);
  }
}


// STATISTICS AUX

float mean_RSA(unsigned long long array[], int n) {
  int i;
  unsigned long long sum = 0;
  for (i = 0; i < n; i++)
    sum = sum + array[i];
  return ((float)sum / (float)n);
}


void sort_array_RSA(unsigned long long arr[], int n) {
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

float median_RSA(unsigned long long array[], int n) {
  if (n % 2 == 0)
    return ((float)array[n / 2] + (float)array[n / 2 - 1]) / 2;
  else
    return (float)array[n / 2];
}


double standarddeviation_RSA(unsigned long long array[], const int n) {
  int j;
  double *max = (double *)malloc(sizeof(double) * n);
  double sum, variance, this_mean;

  this_mean = mean_RSA(array, n);
  sum = 0;
  for (j = 0; j < n; j++) {
    max[j] = pow((array[j] - this_mean), 2);
    sum += max[j];
  }
  variance = sum / (j - 1);
  free(max);
  return sqrt(variance);
}


void calculate_quartiles_RSA(unsigned long long arr[], int n,
                             float quartiles[4], int quartiles_positions[4]) {
  sort_array_RSA(arr, n);
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

void check_pt_chunks_RSA(int mode, int *pt_max_len_chunk,
                         int *plaintext_length_bytes, int bits,
                         std::ofstream &MyFile) {
  switch (mode) {
    case RSA_PKCS1_PADDING:
      *pt_max_len_chunk = bits / 8 - 11;
      break;
    case RSA_NO_PADDING:
      *pt_max_len_chunk = bits / 8;
      break;
    case RSA_PKCS1_OAEP_PADDING:
      *pt_max_len_chunk = bits / 8 - 42;
      break;
    default:
      *pt_max_len_chunk = 0;
      break;
  }

  if (*plaintext_length_bytes == 100) {
    *plaintext_length_bytes = *pt_max_len_chunk;
  }

  if (*plaintext_length_bytes == (*pt_max_len_chunk) * 10) {
    *plaintext_length_bytes = 1000;
  }

  MyFile << "Bytes Encrypted     ->      " << *plaintext_length_bytes << "\n";

  MyFile << "Plaintext Bytes     ->      " << *pt_max_len_chunk << "\n";

  MyFile << "Key Size Bytes      ->      " << (int)bits << "\n\n";
}


void analyze_protocol_RSA(uint8_t mode,
                          unsigned long long *arr_cycles_encrypt_total,
                          unsigned long long *arr_cycles_decrypt_total, int n,
                          std::ofstream &MyFile) {

  MyFile << "cycles_encrypt_total        ";
  unsigned long long cycles_encrypt_total =
      analyze_statistics_RSA(mode, arr_cycles_encrypt_total, n, MyFile);

  MyFile << "cycles_decrypt_total        ";
  unsigned long long cycles_decrypt_total =
      analyze_statistics_RSA(mode, arr_cycles_decrypt_total, n, MyFile);

  // Print the value of the 4 functions (no overhead for array
  // initialization, etc)
  unsigned long long cycles_protocol_total =
      cycles_encrypt_total + cycles_decrypt_total;

  MyFile << "TOTAL protocol              " << fixed << setprecision(0)
         << cycles_protocol_total / 1000 << "   CCs x10^3\n";


  analyze_percentage_RSA(cycles_encrypt_total, cycles_decrypt_total,
                         cycles_protocol_total, MyFile);
}


float analyze_statistics_RSA(uint8_t mode, unsigned long long arr_cycles[],
                             int n, std::ofstream &MyFile) {
  sort_array_RSA(arr_cycles, n);

  int start_index = n / 4;
  int number_elements = n / 4 * 2;

  // Consider only central 50% of the data -> eliminate quartile I and IV
  float mean_val = mean_RSA(arr_cycles + start_index, number_elements);

  if (mode == 1) {
    MyFile << fixed << setprecision(0) << mean_val / 1000 << "    CCs x10^3"
           << ", ";
    MyFile << "M " << fixed << setprecision(0)
           << median_RSA(arr_cycles + start_index, number_elements) / 1000
           << " CCs x10^3, ";

    MyFile << "SD " << fixed << setprecision(0)
           << standarddeviation_RSA(arr_cycles + start_index, number_elements)
           << "\n";
  } else {
    MyFile << fixed << setprecision(0) << mean_val / 1000 << "    CCs x10^3"
           << "\n";
  }
  return mean_val;
}


void analyze_percentage_RSA(unsigned long long cycles_encrypt,
                            unsigned long long cycles_decrypt,
                            unsigned long long clean_protocol,
                            std::ofstream &MyFile) {
  MyFile << "% encrypt                   " << fixed << setprecision(3)
         << ((float)(cycles_encrypt) / ((float)clean_protocol) * 100)
         << " % \n";

  MyFile << "% decrypt                   " << fixed << setprecision(3)
         << ((float)cycles_decrypt) / ((float)clean_protocol) * 100
         << " % \n";
}