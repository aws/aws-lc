#include <stdio.h>
#include <time.h>
#include <assert.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/times.h>
#include <string.h>

#include "benchmark.h"

void handle_errors(void)
{
    printf("Error!\n");
}

BIO *bio_out = NULL;
BIO *bio_err = NULL;

void test_open_streams(void)
{
    bio_out = BIO_new_fp(stdout, BIO_NOCLOSE);
    bio_err = BIO_new_fp(stderr, BIO_NOCLOSE);

    assert(bio_out != NULL);
    assert(bio_err != NULL);
}

void test_close_streams(void)
{
    (void)BIO_flush(bio_out);
    (void)BIO_flush(bio_err);

    BIO_free_all(bio_out);
    BIO_free_all(bio_err);
}

FILE* open_fpstat(void)
{
    char filename[100];
    pid_t pid;
    FILE *fpstat;

    pid = getpid();
    printf("pid: %d\n", pid);

    sprintf(filename, "/proc/%d/stat", pid);
    //printf("filename: %s\n", filename);
    fpstat = fopen(filename, "r");
    if (fpstat == NULL)
    {
        perror("FOPEN ERROR ");
    }

    return fpstat;
}

void close_fpstat(FILE *fpstat)
{
    fclose(fpstat);
}

uint64_t time_now(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);

    uint64_t ret = ts.tv_sec;
    ret *= 1000000;
    ret += ts.tv_nsec / 1000;
    return ret;
}

#ifdef __linux__
int64_t cpu_now(FILE *fpstat, unsigned int *flags)
{
    long unsigned int utime_ticks = 0;
    long int cutime_ticks = -1;
    long unsigned int stime_ticks = 0;
    long int cstime_ticks = -1;

    // https://github.com/fho/code_snippets/blob/master/c/getusage.c#L48
    // https://linux.die.net/man/5/proc
    if (fscanf(fpstat, "%*d %*s %*c %*d %*d %*d %*d %*d %u %*u %*u %*u %*u"
               "%lu %lu %ld %ld %*d %*d %*d %*d %*u %*u %*d",
               flags, &utime_ticks, &stime_ticks, &cutime_ticks, &cstime_ticks) == EOF)
    {
        perror("ERROR: fscanf");
    }
    printf("uticks: %lu\n", utime_ticks);
    printf("cuticks: %ld\n", cutime_ticks);
    printf("sticks: %lu\n", stime_ticks);
    printf("csticks: %ld\n", cstime_ticks);
    printf("flags: %.8X\n\n", *flags);
#if 0
    // calling this on EC2 causes "Illegal instruction (core dumped)"
    register uint64_t x0 __asm__ ("x0");
    __asm__ ("mrs x0, CurrentEL;" : : : "%x0");
    printf("EL = %lX\n", x0 >> 2);
#endif
    return ((int64_t)utime_ticks + (int64_t)cutime_ticks);
}
#endif
