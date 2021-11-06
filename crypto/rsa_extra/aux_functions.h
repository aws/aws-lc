#include <stdint.h>
#include <time.h>
#include <fstream>
#include <iomanip>
#include <iostream>

using namespace std;

void print_padding_mode_RSA(int mode, std::ofstream &MyFile, int n);
void init_plaintext_RSA(uint8_t *plaintext, int size);
void check_pt_chunks_RSA(int mode, int *pt_max_len_chunk,
                         int *plaintext_length_bytes, int bits,
                         std::ofstream &MyFile);

float mean_RSA(unsigned long long array[], int n);

float median_RSA(unsigned long long array[], int n);

void sort_array_RSA(unsigned long long arr[], int n);

double standarddeviation_RSA(unsigned long long array[], const int n);
void calculate_quartiles_RSA(unsigned long long arr[], int n,
                             float quartiles[4], int quartiles_positions[4]);

void analyze_percentage_RSA(unsigned long long cycles_encrypt,
                            unsigned long long cycles_decrypt,
                            unsigned long long clean_protocol,
                            std::ofstream &MyFile);

float analyze_statistics_RSA(uint8_t mode, unsigned long long arr_cycles[],
                             int n, std::ofstream &MyFile);

void analyze_protocol_RSA(uint8_t mode,
                          unsigned long long *arr_cycles_keygen_total,
                          unsigned long long *arr_cycles_encrypt_total,
                          unsigned long long *arr_cycles_decrypt_total, int n,
                          std::ofstream &MyFile);
