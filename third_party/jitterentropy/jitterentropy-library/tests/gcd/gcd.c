/*
 * Copyright (C) 2021 - 2025, Stephan Mueller <smueller@chronox.de>
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
#include <stdint.h>
#include <inttypes.h>

#include "jitterentropy-gcd.h"

#define MAJVERSION 0   /* API / ABI incompatible changes,
			* functional changes that require consumer
			* to be updated (as long as this number is
			* zero, the API is not considered stable
			* and can change without a bump of the
			* major version). */
#define MINVERSION 1   /* API compatible, ABI may change,
			* functional enhancements only, consumer
			* can be left unchanged if enhancements are
			* not considered. */
#define PATCHLEVEL 0   /* API / ABI compatible, no functional
			* changes, no enhancements, bug fixes
			* only. */

#define ELEM 1000
#define EXP_GCD 50ULL
int main(int argc, char *argv[])
{
	uint64_t *gcd = jent_gcd_init(ELEM);
	uint64_t val;
	unsigned int i;

	(void)argc;
	(void)argv;

	for (i = 0; i < ELEM; i++)
		jent_gcd_add_value(gcd, i * EXP_GCD, i);

	if (jent_gcd_analyze(gcd, ELEM))
		return 1;

	jent_gcd_fini(gcd, ELEM);

	if (jent_gcd_get(&val))
		return 2;

	if (val != EXP_GCD)
		return 3;

	return 0;
}
