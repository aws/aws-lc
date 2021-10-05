/* 
 * From PQCrypto-SIDH MR
 */

#include <openssl/cpucycles.h>
#include <stdint.h>

//UNIX
#include <time.h>

uint64_t cpucycles(void)
{ // Access system counter for benchmarking
    unsigned int hi, lo;
    __asm volatile ("rdtsc\n\t" : "=a" (lo), "=d"(hi));
    return ((int64_t)lo) | (((int64_t)hi) << 32);
}
