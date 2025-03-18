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
 * Compile:
 * gcc -Wall -pedantic -Wextra -o getrawentropy getrawentropy.c
 */

#include <sys/types.h>
#include <sys/stat.h>

#include <errno.h>
#include <getopt.h>
#include <limits.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>

#define RAWENTROPY_SAMPLES	1000
#define DEBUGFS_INTERFACE	"/sys/kernel/debug/jitterentropy_testing/jent_raw_hires"

struct opts {
	size_t samples;
	char *debugfs_file;
};

static int getrawentropy(struct opts *opts)
{
#define BUFFER_SIZE		(RAWENTROPY_SAMPLES * sizeof(uint32_t))
	uint32_t requested = opts->samples * sizeof(uint32_t);
	uint8_t *buffer_p, buffer[BUFFER_SIZE];
	ssize_t ret;
	int fd = -1;

	fd = open(opts->debugfs_file, O_RDONLY);
	if (fd < 0)
		return errno;

	while (requested) {
		unsigned int i;
		unsigned int gather = ((BUFFER_SIZE > requested) ?
				       requested : BUFFER_SIZE);

		buffer_p = buffer;

		ret = read(fd, buffer_p, gather);
		if (ret < 0) {
			ret = -errno;
			goto out;
		}

		for (i = 0; i < ret / (sizeof(uint32_t)); i++) {
			uint32_t val;

			memcpy(&val, buffer_p, sizeof(uint32_t));
			printf("%u\n", val);
			buffer_p += sizeof(uint32_t);
		}

		requested -= ret;
	}

	ret = 0;

out:
	if (fd >= 0)
		close(fd);

	return (int)ret;
}

int main(int argc, char *argv[])
{
	struct opts opts;
	int c = 0;

	opts.samples = RAWENTROPY_SAMPLES;
	opts.debugfs_file = DEBUGFS_INTERFACE;

	while (1)
	{
		int opt_index = 0;
		static struct option options[] =
		{
			{"samples", 		required_argument,	0, 's'},
			{"debugfs-file", 	required_argument,	0, 'f'},
			{0, 0, 0, 0}
		};
		c = getopt_long(argc, argv, "f:s:", options, &opt_index);
		if (c == -1)
			break;
		switch (c) {
		case 0:
			switch (opt_index) {
			case 0:
				opts.samples = strtoul(optarg, NULL, 10);
				if (opts.samples == ULONG_MAX)
					return -EINVAL;
				break;
			case 1:
				opts.debugfs_file = optarg;
				break;
			}
			break;

		case 's':
			opts.samples = strtoul(optarg, NULL, 10);
			if (opts.samples == ULONG_MAX)
				return -EINVAL;
			break;
		case 'f':
			opts.debugfs_file = optarg;
			break;
		default:
			return -EINVAL;
		}
	}

	return getrawentropy(&opts);
}
