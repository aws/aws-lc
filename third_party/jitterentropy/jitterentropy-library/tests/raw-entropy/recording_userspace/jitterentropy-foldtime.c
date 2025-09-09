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

#include <stdio.h>
#include <unistd.h>
#include <string.h>

#include "jitterentropy.h"
#ifndef CONFIG_CRYPTO_CPU_JITTERENTROPY_STAT
#error This program is meaningless without CONFIG_CRYPTO_CPU_JITTERENTROPY_STAT
#endif

int main(int argc, char * argv[])
{
#ifdef ROUNDS
	size_t size = 0;
	struct rand_data *ec;

	ec = jent_entropy_collector_alloc(0, 0);
	if(!ec)
		return 1;

	while(size < ROUNDS)
#else
	while(1)
#endif
	{
		__u64 duration = 0;
		__u64 duration_min = 0;
		/* When enabling the for loops, you effectively get a cache
		 * and TLB flush -- but tests show that flushing the cache
		 * does not change the results, considering that you want to
		 * remove the outliers from the dataset before processing it
		 * as you do not want to have measurements based interferred
		 * by interrupts, etc.
		 */
/*		int i = 0;
		for(i=0; i<1000; i++) */
/*		mb(); */
			duration = jent_fold_var_stat(ec, 0);
/*		mb(); */
/*		for(i=0; i<1000; i++) */
			duration_min = jent_fold_var_stat(ec, 1);
/*		mb(); */
		printf("%llu %llu\n", duration, duration_min);
#ifdef ROUNDS
		size++;
#endif
	}

	return 0;
}

