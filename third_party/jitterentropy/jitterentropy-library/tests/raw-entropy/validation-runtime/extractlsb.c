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

/*
 * The tool extracts the 4 or 8 LSB of the high-res time stamp and
 * concatenates them to form a binary data stream.
 *
 */

#include <sys/types.h>
#include <sys/stat.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>

#define BITS_PER_SAMPLE 64

/*
	Extract bits from sample based on significant bit mask
*/

static unsigned char extract(uint64_t sample, uint64_t mask)
{
	unsigned char byte = 0;
	int i, j = 0;

	for (i = 0; i < BITS_PER_SAMPLE && mask; i++) {
		if (mask & 1) {
			byte |= (sample & 1) << j;
			j++;
		}
		mask >>= 1;
		sample >>= 1;
	}
	return (byte);
}

/*
	Convert mask in hexadecimal format to binary
*/

static int hextolong(char *p_strmask, uint64_t *p_mask)
{

	uint64_t mask = 0;
	int count = 0;

	while (*p_strmask) {
		count++;
		mask <<= 4;

		if ((*p_strmask >= '0') && (*p_strmask <= '9'))
			mask |= *p_strmask - '0';
		else if ((*p_strmask >= 'A') && (*p_strmask <= 'F'))
			mask |= *p_strmask - 'A' + 10;
		else if ((*p_strmask >= '0') && (*p_strmask <= '9'))
			mask |= *p_strmask - 'a' + 10;
		else
			return -1;

		p_strmask++;
	}

	if (count > 16)
		return(-1);

	*p_mask = mask;
	return(0);
}

/*
	Count the number of bits on
*/

static int bitcount(uint64_t mask)
{
	int i, j = 0;

	for (i = 0; i < BITS_PER_SAMPLE && mask; i++) {
		if (mask & 1) {
			j++;
		}
		mask >>= 1;
	}
	return (j);
}

/*
	Print 64 bits of long word masking with '-' those not matching value
*/

static char *printbits(uint64_t sample, int value)
{
	static char buf[BITS_PER_SAMPLE + 9];
	char *p_buf = buf + sizeof(buf) - 1;
	int i;
	*p_buf-- = '\0';
	for (i = 0; i < BITS_PER_SAMPLE; i++) {
		if (i % 8 == 0)
			*p_buf-- = ' ';

		if ((sample & 1) ^ value)
			*p_buf = '-';
		else
			*p_buf = '0' + value;
		p_buf--;
		sample >>= 1;
	}

	return buf;
}


int main(int argc, char *argv[])
{
	FILE *f = NULL;
	char buf[64];
	int varfd = -1;
	int singlefd = -1;
	uint32_t count;
	uint32_t i = 0;

	uint64_t mask;
	uint64_t var_unchanged0s, var_unchanged1s;
	uint64_t single_unchanged0s, single_unchanged1s;
	int rc;

	if (argc != 6) {
		printf("Usage: %s inputfile varoutfile singleoutfile maxevents mask\n", argv[0]);
		return 1;
	}

	f = fopen(argv[1], "r");
	if (!f) {
		printf("File %s cannot be opened for read\n", argv[1]);
		return 1;
	}

	varfd = open(argv[2], O_CREAT|O_WRONLY|O_EXCL, 0777);
	if (varfd < 0) {
		printf("File %s cannot be opened for write\n", argv[2]);
		fclose(f);
		return 1;
	}

	singlefd = open(argv[3], O_CREAT|O_WRONLY|O_EXCL, 0777);
	if (singlefd < 0) {
		printf("File %s cannot be opened for write\n", argv[3]);
		fclose(f);
		close(varfd);
		return 1;
	}

	count = strtoul(argv[4], NULL, 10);
	rc = hextolong(argv[5], &mask);

	if (rc) {
		printf("Mask value is incorrect [%s], use up to 16 hexadecimal characters", argv[5]);
		return 1;
	}

	if (bitcount(mask) > 8) {
		printf("SP800-90B tool only supports up to 8 bits. Check the mask value");
		return 1;
	}

	var_unchanged0s = 0;
	var_unchanged1s = ~0;
	single_unchanged0s = 0;
	single_unchanged1s = ~0;

	while (fgets(buf, sizeof(buf), f)) {
		uint64_t sample;
		unsigned char var, single;
		char *saveptr = NULL;
	 	char *res = NULL;

		i++;

		res = strtok_r(buf, " ", &saveptr);
		if (!res) {
			printf("strtok_r error\n");
			return 1;
		}

		sample = strtoul(res, NULL, 10);
		var_unchanged0s |= sample;
		var_unchanged1s &= sample;

		var = extract(sample, mask);
		write(varfd, &var, sizeof(var));

		res = strtok_r(NULL, " ", &saveptr);
		if (res) {
			sample = strtoul(res, NULL, 10);
			single_unchanged0s |= sample;
			single_unchanged1s &= sample;

			single = extract(sample, mask);
			write(singlefd, &single, sizeof(single));
		}

		if (i >= count)
			break;
	}

	printf("Processed %d items from %s samples with mask [0x%016llx] significant bits [%d]\n", i, argv[0], (unsigned long long)mask, bitcount(mask));

	printf("Constant 0s in var sample: \n%s\n", printbits(var_unchanged0s, 0));
	printf("Constant 1s in var sample: \n%s\n", printbits(var_unchanged1s, 1));
	printf("Constant 0s in single sample: \n%s\n", printbits(single_unchanged0s, 0));
	printf("Constant 1s in single sample: \n%s\n", printbits(single_unchanged1s, 1));

	fclose(f);
	close(varfd);
	close(singlefd);
	return 0;
}
