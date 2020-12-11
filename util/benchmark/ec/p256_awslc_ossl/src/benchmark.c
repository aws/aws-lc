#include <stdio.h>
#include <time.h>
#include <assert.h>
#include <unistd.h>
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

#if defined(PID_CPU_TICKS)
FILE* open_fpstat(void)
{
    char filename[100];
    pid_t pid;
    FILE *fpstat;

    pid = getpid();
    printf("pid: %d\n", pid);

    sprintf(filename, "/proc/%d/stat", pid);
    fpstat = fopen(filename, "r");
    if (fpstat == NULL)
    {
        BIO_printf(bio_err, "ERROR: opening /proc/<pid>/stat failed.\n");
        ERR_print_errors(bio_err);
    }
    return fpstat;
}
#endif

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

#if defined(PID_CPU_TICKS)
int64_t cpu_now(FILE *fpstat, unsigned int *flags)
{
	if (NULL == fpstat)
    {
        return -1;
    }

    // Values read from proc/<pid>/stat:
    // flags: (9) kernel flags;
    // see the PF_* defines in the Linux kernel source file include/linux/sched.h

    // (14) clock ticks when process is scheduled in user mode
    long unsigned int utime_ticks = 0;
    // (16) clock ticks when process' children are scheduled in user mode
    long int cutime_ticks = -1;
    // (15) clock ticks when process is scheduled in kernel mode
    long unsigned int stime_ticks = 0;
    // (17) clock ticks when process' children are scheduled in kernel mode
    long int cstime_ticks = -1;

    // https://github.com/fho/code_snippets/blob/master/c/getusage.c#L48
    // https://linux.die.net/man/5/proc
    if (fscanf(fpstat, "%*d %*s %*c %*d %*d %*d %*d %*d "
               "%u %*u %*u %*u %*u "
               "%lu %lu %ld %ld %*d %*d %*d %*d %*u %*u %*d",
               flags, &utime_ticks, &stime_ticks, &cutime_ticks, &cstime_ticks) == EOF)
    {
        BIO_printf(bio_err, "ERROR: reading from /proc/<pid>/stat.\n");
        ERR_print_errors(bio_err);
    }
    printf("uticks: %lu, cuticks: %ld\n", utime_ticks, cutime_ticks);
    printf("sticks: %lu, csticks: %ld\n", stime_ticks, cstime_ticks);
    printf("flags: %.8X\n\n", *flags);
#if 0
    // calling this on Graviton2 EC2 causes "Illegal instruction (core dumped)"
    register uint64_t x0 __asm__ ("x0");
    __asm__ ("mrs x0, CurrentEL;" : : : "%x0");
    printf("EL = %lX\n", x0 >> 2);
#endif
    return ((int64_t)utime_ticks + (int64_t)cutime_ticks);
}
#endif
