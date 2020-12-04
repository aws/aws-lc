#include <openssl/err.h>
#include <openssl/bio.h>

#define NUM_ELEM(x)    (sizeof(x)/sizeof((x)[0]))
extern BIO *bio_err;
extern BIO *bio_out;

void handle_errors(void);
void test_open_streams(void);
void test_close_streams(void);
FILE* open_fpstat(void);
void close_fpstat(FILE *fpstat);
uint64_t time_now(void);

#ifdef __linux__
int64_t cpu_now(FILE *fpstat, unsigned int *flags);
#endif

void benchmark_ecdh_p256(int num_itr);
void benchmark_ecdsa_p256(int num_itr);
