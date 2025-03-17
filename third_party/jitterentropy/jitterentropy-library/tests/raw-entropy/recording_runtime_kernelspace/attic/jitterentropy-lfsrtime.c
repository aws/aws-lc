/*
 * Copyright (C) 2019 - 2025, Stephan Mueller <smueller@chronox.de>
 *
 * License: see LICENSE file in root directory
 *
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ALL OF
 * WHICH ARE HEREBY DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
 * USE OF THIS SOFTWARE, EVEN IF NOT ADVISED OF THE POSSIBILITY OF SUCH
 * DAMAGE.
 */

#include <stdint.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <limits.h>

#ifdef __MACH__
#include <assert.h>
#include <CoreServices/CoreServices.h>
#include <mach/mach.h>
#include <mach/mach_time.h>
#include <unistd.h>
#endif

#undef NULL
typedef unsigned long long __u64;

/***************************************************************************
 * Link code for user space
 ***************************************************************************/

void *jent_zalloc(unsigned int len)
{
	return calloc(1, len);
}

void jent_zfree(void *ptr)
{
	free(ptr);
}

int jent_fips_enabled(void)
{
	/* Enable full SP800-90B health test handling */
	return 1;
}

void jent_panic(char *s)
{
	printf("%s", s);
	exit(1);
}

void jent_memcpy(void *dest, const void *src, unsigned int n)
{
	memcpy(dest, src, n);
}

/* taken from Linux kernel */
#ifdef X86_64
#define DECLARE_ARGS(val, low, high)    unsigned low, high
#define EAX_EDX_VAL(val, low, high)     ((low) | ((__u64)(high) << 32))
#define EAX_EDX_RET(val, low, high)     "=a" (low), "=d" (high)
#else
#define DECLARE_ARGS(val, low, high)    unsigned long long val
#define EAX_EDX_VAL(val, low, high)     (val)
#define EAX_EDX_RET(val, low, high)     "=A" (val)
#endif

/*
 * Obtain a high-resolution time stamp value. The time stamp is used to measure
 * the execution time of a given code path and its variations. Hence, the time
 * stamp must have a sufficiently high resolution.
 *
 * Note, if the function returns zero because a given architecture does not
 * implement a high-resolution time stamp, the RNG code's runtime test
 * will detect it and will not produce output.
 */
void jent_get_nstime(__u64 *out)
{
	/* OSX does not have clock_gettime -- taken from
	 * http://developer.apple.com/library/mac/qa/qa1398/_index.html */
#ifdef __MACH__
	*out = mach_absolute_time();

#elif _AIX
	/* clock_gettime() on AIX returns a timer value that increments in
	 * steps of 1000
	 */
	uint64_t tmp = 0;
	timebasestruct_t aixtime;
	read_real_time(&aixtime, TIMEBASE_SZ);
	tmp = aixtime.tb_high;
	tmp = tmp << 32;
	tmp = tmp | aixtime.tb_low;
	*out = tmp;

#elif (defined(__i386__) || defined(__x86_64__))
	DECLARE_ARGS(val, low, high);
	__asm__ __volatile__("rdtsc" : EAX_EDX_RET(val, low, high));
	*out = EAX_EDX_VAL(val, low, high);

#else
	/* we could use CLOCK_MONOTONIC(_RAW), but with CLOCK_REALTIME
	 * we get some nice extra entropy once in a while from the NTP actions
	 * that we want to use as well... though, we do not rely on that
	 * extra little entropy */
	uint64_t tmp = 0;
	struct timespec time;
	if (clock_gettime(CLOCK_REALTIME, &time) == 0)
	{
		tmp = time.tv_sec;
		tmp = tmp << 32;
		tmp = tmp | time.tv_nsec;
	}
	*out = tmp;
#endif
}

/***************************************************************************
 * Include Jitter RNG code
 ***************************************************************************/

#include "jitterentropy.c"

/***************************************************************************
 * Statistical test logic not compiled for regular operation
 ***************************************************************************/
/*
 * Statistical test: return the time duration for the folding operation. If min
 * is set, perform the given number of LFSR ops. Otherwise, allow the
 * loop count shuffling to define the number of LFSR ops.
 */
static
uint64_t jent_lfsr_var_stat(struct rand_data *ec, unsigned int min)
{
	__u64 time = 0;
	__u64 time2 = 0;

	jent_get_nstime(&time);
	jent_memaccess(ec, min);
	jent_lfsr_time(ec, time, min, 0);
	jent_get_nstime(&time2);
	return ((time2 - time));
}

static int jent_one_test(const char *pathname, unsigned long rounds)
{
	unsigned long size = 0;
	struct rand_data *ec;
	FILE *out = NULL;
	int ret = 0;

	printf("Processing %s\n", pathname);

	out = fopen(pathname, "w");
	if (!out) {
		ret = 1;
		goto out;
	}

	ec = jent_entropy_collector_alloc(0, 0);
	if(!ec) {
		ret = 1;
		goto out;
	}

	for (size = 0; size < rounds; size++) {
		uint64_t duration = 0;
		uint64_t duration_min = 0;

		duration = jent_lfsr_var_stat(ec, 0);
		duration_min = jent_lfsr_var_stat(ec, 1);
		fprintf(out, "%lu %lu\n", duration, duration_min);
	}

out:
	if (out)
		fclose(out);

	return ret;
}

/*
 * Invoke the application with
 *	argv[1]: number of raw entropy measurements to be obtained for one
 *		 entropy collector instance.
 *	argv[2]: number of test repetitions with a new entropy estimator
 *		 allocated for each round - this satisfies the restart tests
 *		 defined in SP800-90B section 3.1.4.3 and FIPS IG 7.18.
 *	argv[3]: File name of the output data
 */
int main(int argc, char * argv[])
{
	unsigned long i, rounds, repeats;
	int ret;
	char pathname[4096];

	if (argc != 4) {
		printf("%s <rounds per repeat> <number of repeats> <filename>\n", argv[0]);
		return 1;
	}

	rounds = strtoul(argv[1], NULL, 10);
	if (rounds >= UINT_MAX)
		return 1;

	repeats = strtoul(argv[2], NULL, 10);
	if (repeats >= UINT_MAX)
		return 1;

	for (i = 1; i <= repeats; i++) {
		snprintf(pathname, sizeof(pathname), "%s-%.4lu.data", argv[3],
			 i);
		ret = jent_one_test(pathname, rounds);
		if (ret)
			return ret;
	}

	return 0;
}
