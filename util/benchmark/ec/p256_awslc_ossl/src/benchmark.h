#include <sys/types.h>
#include <stdint.h>
#include <openssl/err.h>
#include <openssl/bio.h>

#if defined(__linux__) && defined(CPU_TICKS)
#define PID_CPU_TICKS   1
#endif

#define NUM_ELEM(x)    (sizeof(x)/sizeof((x)[0]))
extern BIO *bio_err;
extern BIO *bio_out;

void handle_errors(void);
void test_open_streams(void);
void test_close_streams(void);
uint64_t time_now(void);

#if defined(PID_CPU_TICKS)
FILE* open_fpstat(void);
void close_fpstat(FILE *fpstat);
int64_t cpu_now(FILE *fpstat, unsigned int *flags);
#endif

void benchmark_ecdh_p256(int num_itr);
void benchmark_ecdsa_p256(int num_itr);
