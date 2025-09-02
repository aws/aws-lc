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
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <math.h>
#include <float.h>
#include <assert.h>

#include "jitterentropy.h"

/* We use a linear interpolation to estimate where the value is going to be.
 * The way these variable are named, this is technically the inverse function
 * for the resulting line, as we are trying to get the expected osr for a
 * provided time.
 *
 * Recall that point-point form for a line is
 * y - y1 = ((y2 - y1)/(x2 - x1))*(x - x1)
 * which is valid for non-vertical lines (i.e., so long as x1 != x2)
 * We actually want the functional inverse of this, so solving for x, we get
 * (y - y1) * ((x2 - x1) / (y2 - y1)) + x1 = x
 * This is valid so long as y2 != y1.
 * This functional inverse is the form that we use here.
 */
double linearInverse(double y, double x1, double y1, double x2, double y2) {
	assert(fabs(y1-y2)>=DBL_EPSILON);
	return (y-y1)*((x2-x1)/(y2-y1)) + x1;
}

/* Returns the number of nanoseconds per output for the selected flags and osr. */
uint64_t jent_output_time(unsigned int rounds, unsigned int osr, unsigned int flags)
{
	struct rand_data *ec_nostir;
	struct timespec start, finish;
	uint64_t runtime;
	int ret;

	ret = jent_entropy_init_ex(osr, flags);
	if (ret) {
		fprintf(stderr, "The initialization failed with error code %d\n", ret);
		return ret;
	}

	ec_nostir = jent_entropy_collector_alloc(osr, flags);

	clock_gettime(CLOCK_REALTIME, &start);
	
	if (!ec_nostir) {
		fprintf(stderr, "Jitter RNG handle cannot be allocated\n");
		return 1;
	}

	for (unsigned long size = 0; size < rounds; size++) {
		char tmp[32];

		if (0 > jent_read_entropy_safe(&ec_nostir, tmp, sizeof(tmp))) {
			fprintf(stderr, "FIPS 140-2 continuous test failed\n");
			return 1;
		}
	}

	clock_gettime(CLOCK_REALTIME, &finish);
	runtime = ((uint64_t)finish.tv_sec * UINT64_C(1000000000) + (uint64_t)finish.tv_nsec) - ((uint64_t)start.tv_sec * UINT64_C(1000000000) + (uint64_t)start.tv_nsec);

	jent_entropy_collector_free(ec_nostir);

	return runtime / (uint64_t)rounds;
}

int main(int argc, char * argv[])
{
	unsigned long rounds;
	unsigned int flags = 0;
	char *endtimeparam;
	double timeBoundIn;
	uint64_t timeBound;
	unsigned int maxBound, minBound, firstLinearGuess, secondLinearGuess;
	uint64_t minTime, maxTime, firstLinearTime, secondLinearTime;

	if (argc < 2) {
		fprintf(stderr, "%s <number of measurements> <target time> [--force-fips|--disable-memory-access|--disable-internal-timer|--force-internal-timer|--max-mem <NUM>]\n", argv[0]);
		return 1;
	}

	rounds = strtoul(argv[1], NULL, 10);
	if ((rounds >= UINT_MAX) || (rounds == 0))
		return 1;
	argc--;
	argv++;

	timeBoundIn = strtod(argv[1], &endtimeparam);
	if ((timeBoundIn <= 0.0) || (*endtimeparam != '\0'))
		return 1;

	/* The time upper bound, expressed as an integer number of nanoseconds. */
	timeBound = (uint64_t)floor(timeBoundIn * 1000000000.0);
	argc--;
	argv++;

	while (argc > 1) {
		if (!strncmp(argv[1], "--force-fips", 12))
			flags |= JENT_FORCE_FIPS;
		else if (!strncmp(argv[1], "--disable-memory-access", 23))
			flags |= JENT_DISABLE_MEMORY_ACCESS;
		else if (!strncmp(argv[1], "--disable-internal-timer", 24))
			flags |= JENT_DISABLE_INTERNAL_TIMER;
		else if (!strncmp(argv[1], "--force-internal-timer", 22))
			flags |= JENT_FORCE_INTERNAL_TIMER;
		else if (!strncmp(argv[1], "--max-mem", 9)) {
			unsigned long val;

			argc--;
			argv++;
			if (argc <= 1) {
				fprintf(stderr, "Maximum memory value missing.\n");
				return 1;
			}

			val = strtoul(argv[1], NULL, 10);
			switch (val) {
			case 0:
				/* Allow to set no option */
				break;
			case 1:
				flags |= JENT_MAX_MEMSIZE_32kB;
				break;
			case 2:
				flags |= JENT_MAX_MEMSIZE_64kB;
				break;
			case 3:
				flags |= JENT_MAX_MEMSIZE_128kB;
				break;
			case 4:
				flags |= JENT_MAX_MEMSIZE_256kB;
				break;
			case 5:
				flags |= JENT_MAX_MEMSIZE_512kB;
				break;
			case 6:
				flags |= JENT_MAX_MEMSIZE_1MB;
				break;
			case 7:
				flags |= JENT_MAX_MEMSIZE_2MB;
				break;
			case 8:
				flags |= JENT_MAX_MEMSIZE_4MB;
				break;
			case 9:
				flags |= JENT_MAX_MEMSIZE_8MB;
				break;
			case 10:
				flags |= JENT_MAX_MEMSIZE_16MB;
				break;
			case 11:
				flags |= JENT_MAX_MEMSIZE_32MB;
				break;
			case 12:
				flags |= JENT_MAX_MEMSIZE_64MB;
				break;
			case 13:
				flags |= JENT_MAX_MEMSIZE_128MB;
				break;
			case 14:
				flags |= JENT_MAX_MEMSIZE_256MB;
				break;
			case 15:
				flags |= JENT_MAX_MEMSIZE_512MB;
				break;
			default:
				fprintf(stderr, "Unknown maximum memory value\n");
				return 1;
			}
		} else {
			fprintf(stderr, "Unknown option %s\n", argv[1]);
			return 1;
		}

		argc--;
		argv++;
	}

	/* We don't start with a maxBound. */
	maxBound = 0;
	maxTime = 0;

	/* Verify the first invariant: generation using minBound occurs in less than or equal time than the targeted time. */
	minBound = JENT_MIN_OSR;
	if((minTime = jent_output_time(rounds, minBound, flags)) > timeBound) {
		fprintf(stderr, "Minimum osr %u exceeds the target time. Invariant not met.\n", minBound);
		return 1;
	} else
		fprintf(stderr, "A minimum was found: osr upper bound is >= %u.\n", minBound);

	/* If there were no constant value in the linear expression, then we could estimate a cutoff
	 * using only this timing. We imagine that there is a fixed cost, so simple division overestimates
	 * the time cost per osr, and so this produces a likely underestimate.
	 */
	firstLinearGuess = (unsigned int)(timeBound / (1U + minTime / minBound));
	fprintf(stderr, "The initial linear estimate is osr=%u\n", firstLinearGuess);
	firstLinearTime = jent_output_time(rounds, firstLinearGuess, flags);

	/* We now have two points (minBound, minTime) and (firstLinearGuess, firstLinearTime), so we can
	 * perform a full linear interpolation.
	 * We are presently looking for an overestimate, so let's round up here.
	 */
	secondLinearGuess = (unsigned int)ceil(linearInverse((double)timeBound, (double)minBound, (double)minTime, (double)firstLinearGuess, (double)firstLinearTime));
	fprintf(stderr, "Linear interpolation suggests a cutoff of %u\n", secondLinearGuess);

	/* These estimates were done in two related ways, but they could have produced the same value.
	 * Looking at the timing of two identical guesses isn't helpful, so adjust the result in this case.*/
	if(secondLinearGuess == firstLinearGuess) {
		secondLinearGuess++;
	}
	secondLinearTime = jent_output_time(rounds, secondLinearGuess, flags);

	/* We now expect that secondLinearGuess > firstLinearGuess but weird things could have occurred.
	 * They can't be equal, by the above adjustment.
	 * Exchange them if they don't have the expected relationship.
	 */
	if(secondLinearGuess < firstLinearGuess) {
		uint64_t tmpTime;
		unsigned int tmpGuess;

		tmpGuess = firstLinearGuess;
		tmpTime = firstLinearTime;

		firstLinearGuess = secondLinearGuess;
		firstLinearTime = secondLinearTime;

		secondLinearGuess = tmpGuess;
		secondLinearTime = tmpTime;
	}

	/* Now secondLinearGuess > firstLinearGuess, and the time values should have a similar relationship. */
	assert(secondLinearTime > firstLinearTime);

	/* Use the linear interpolation guesses as bounds where possible. */
	if(firstLinearTime > timeBound) {
		/* Here, we have timeBound < firstLinearTime < secondLinearTime.
		 * In this case, the linear interpolations didn't yield a minBound
		 * so we'll proceed with the initial minBound.
		 */
		maxBound = firstLinearGuess;
		maxTime = firstLinearTime;
	} else if(secondLinearTime > timeBound) {
		/* Here, we have firstLinearTime <= timeBound < secondLinearTime.
		 * so the linear interpolations provide both a minBound and maxBound. */
		minBound = firstLinearGuess;
		minTime = firstLinearTime;
		maxBound = secondLinearGuess;
		maxTime = secondLinearTime;
	} else {
		/* here, we have know that firstLinearTime < secondLinearTime <= timeBound */
		/* so linear interpolation didn't supply a maxBound, and will have to look for it. */
		minBound = secondLinearGuess;
		minTime = secondLinearTime;
	}

	/* If we don't yet have a maxBound, find one. This will also adjust minBound up as the search goes.*/
	if(maxBound == 0) {
		maxBound = minBound*2;
		fprintf(stderr, "Trying to find a maximum: %u", maxBound);
		/* Locate the maxBound */
		while((maxTime = jent_output_time(rounds, maxBound, flags)) <= timeBound) {
			minBound = maxBound;
			minTime = maxTime;
			maxBound = maxBound * 2;
			fprintf(stderr, " %u", maxBound);
			assert(maxBound > minBound);
		}
		fprintf(stderr, ".\nMaximum found: osr upper bound is < %u.\n", maxBound);
	}

	fprintf(stderr, "Desired osr upper bound is in [%u, %u)\n", minBound, maxBound);
	assert(maxBound > minBound);
	assert(maxTime > minTime);
	assert(maxTime > timeBound);
	assert(minTime <= timeBound);

	/* All invariants are now verified:
	 * maxBound > minBound
	 * maxTime > timeBound >= minTime
	 *
	 * We now perform a binary search (if necessary).
	 */
	while(maxBound - minBound > 1) {
		unsigned int curosr;
		uint64_t curTime;
		/* Calculate (minBound + maxBound)/2 without risk of overflow. */
		curosr = minBound + (maxBound - minBound) / 2;
		assert(curosr > minBound);
		assert(curosr < maxBound);

		fprintf(stderr, "Trying osr=%u. ", curosr);
		curTime = jent_output_time(rounds, curosr, flags);
		assert(curTime > minTime);
		assert(curTime < maxTime);

		if(curTime <= timeBound) {
			fprintf(stderr, "Timing is less than or equal to the target time. ");
			minBound = curosr;
			minTime = curTime;
		} else {
			fprintf(stderr, "Timing is greater than the target time. ");
			maxBound = curosr;
			maxTime = curTime;
		}

		fprintf(stderr, "Desired osr upper bound is in [%u, %u)\n", minBound, maxBound);
		assert(maxBound > minBound);
		assert(maxTime > minTime);
		assert(maxTime > timeBound);
		assert(minTime <= timeBound);
	}

	printf("%u\n", minBound);
			
	return 0;
}
