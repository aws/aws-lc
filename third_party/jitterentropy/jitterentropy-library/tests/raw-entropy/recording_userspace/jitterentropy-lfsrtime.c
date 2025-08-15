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

#include <stdlib.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>

#include "jitterentropy-base.c"

/***************************************************************************
 * Statistical test logic not compiled for regular operation
 ***************************************************************************/
/*
 * Statistical test: return the time duration for the folding operation. If min
 * is set, perform the given number of LFSR ops. Otherwise, allow the
 * loop count shuffling to define the number of LFSR ops.
 */
static uint64_t jent_lfsr_var_stat(struct rand_data *ec, unsigned int min)
{
	uint64_t time = 0;
	uint64_t time2 = 0;

	jent_get_nstime(&time);

	jent_memaccess(ec, min);
	jent_stuck(ec, time);
	jent_lfsr_time(ec, time, min, 0);
	jent_get_nstime(&time2);

	return ((time2 - time));
}

static int jent_one_test(const char *pathname, unsigned long rounds)
{
	unsigned long size = 0;
	struct rand_data *ec = NULL;
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

	/* Enable full SP800-90B health test handling */
	ec->fips_enabled = 1;

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

	if (ec)
		jent_entropy_collector_free(ec);

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

