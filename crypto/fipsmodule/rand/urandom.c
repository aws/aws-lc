/* Copyright (c) 2014, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#if !defined(_GNU_SOURCE)
#define _GNU_SOURCE  // needed for syscall() on Linux.
#endif

#include <openssl/rand.h>

#include "internal.h"

#if defined(OPENSSL_RAND_URANDOM)

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#if defined(OPENSSL_LINUX)
#if defined(BORINGSSL_FIPS)
#if !defined(AWS_LC_URANDOM_U32)
  // On old Linux OS: unknown type name '__u32' when include <linux/random.h>.
  // If '__u32' is predefined, redefine will cause compiler error.
  typedef unsigned int __u32;
#endif
#include <linux/random.h>
#include <sys/ioctl.h>
#endif
#include <sys/param.h>
#include <sys/syscall.h>

#if defined(OPENSSL_ANDROID)
#include <sys/system_properties.h>
#endif

#if !defined(OPENSSL_ANDROID)
#define OPENSSL_HAS_GETAUXVAL
#endif
// glibc prior to 2.16 does not have getauxval and sys/auxv.h. Android has some
// host builds (i.e. not building for Android itself, so |OPENSSL_ANDROID| is
// unset) which are still using a 2.15 sysroot.
//
// TODO(davidben): Remove this once Android updates their sysroot.
#if defined(__GLIBC_PREREQ)
#if !__GLIBC_PREREQ(2, 16)
#undef OPENSSL_HAS_GETAUXVAL
#endif
#endif
#if defined(OPENSSL_HAS_GETAUXVAL)
#include <sys/auxv.h>
#endif
#endif  // OPENSSL_LINUX

#if defined(OPENSSL_APPLE)
#include <CommonCrypto/CommonRandom.h>
#endif

#if defined(OPENSSL_FREEBSD)
#define URANDOM_BLOCKS_FOR_ENTROPY
#if __FreeBSD__ >= 12
// getrandom is supported in FreeBSD 12 and up.
#define FREEBSD_GETRANDOM
#include <sys/random.h>
#endif
#endif

#include <openssl/thread.h>
#include <openssl/mem.h>

#include "getrandom_fillin.h"
#include "../delocate.h"
#include "../../internal.h"

#ifndef MIN
#define AWSLC_MIN(X,Y) (((X) < (Y)) ? (X) : (Y))
#else
#define AWSLC_MIN(X,Y) MIN(X,Y)
#endif

// One second in nanoseconds.
#define ONE_SECOND INT64_C(1000000000)
// 250 milliseconds in nanoseconds.
#define MILLISECONDS_250 INT64_C(250000000)
#define INITIAL_BACKOFF_DELAY 1

// handle_rare_urandom_error initiates exponential backoff. |backoff| holds the
// previous backoff delay. Initial backoff delay is |INITIAL_BACKOFF_DELAY|.
// This function will be called so rarely (if ever), that we keep it as a
// function call and don't care about attempting to inline it.
static void handle_rare_urandom_error(long *backoff) {

  // Exponential backoff.
  //
  // iteration          delay
  // ---------    -----------------
  //    1         10          nsec
  //    2         100         nsec
  //    3         1,000       nsec
  //    4         10,000      nsec
  //    5         100,000     nsec
  //    6         1,000,000   nsec
  //    7         10,000,000  nsec
  //    8         99,999,999  nsec
  //    9         99,999,999  nsec
  //    ...

  struct timespec sleep_time = {.tv_sec = 0, .tv_nsec = 0 };

  // Cap backoff at 99,999,999  nsec, which is the maximum value the nanoseconds
  // field in |timespec| can hold.
  *backoff = AWSLC_MIN((*backoff) * 10, ONE_SECOND - 1);
  // |nanosleep| can mutate |sleep_time|. Hence, we use |backoff| for state.
  sleep_time.tv_nsec = *backoff;

  nanosleep(&sleep_time, &sleep_time);
}

#if defined(USE_NR_getrandom)

#if defined(OPENSSL_MSAN)
void __msan_unpoison(void *, size_t);
#endif

static ssize_t boringssl_getrandom(void *buf, size_t buf_len, unsigned flags) {

  ssize_t ret;
  long backoff = INITIAL_BACKOFF_DELAY;
  size_t retry_counter = 0;

  do {
    ret = syscall(__NR_getrandom, buf, buf_len, flags);
    if ((ret == -1) && (errno != EINTR)) {
      // Don't block in non-block mode except if a signal handler interrupted
      // |getrandom|.
      if ((flags & GRND_NONBLOCK) != 0 ||
          (retry_counter >= MAX_BACKOFF_RETRIES)) {
        break;
      }

      // We have observed extremely rare events in which a |read| on a
      // |urandom| fd failed with |errno| != |EINTR|. |getrandom| uses |urandom|
      // under the covers. Assuming transitivity, |getrandom| is therefore also
      // subject to the same rare error events.
      handle_rare_urandom_error(&backoff);
      retry_counter = retry_counter + 1;
    }
  } while (ret == -1);

#if defined(OPENSSL_MSAN)
  if (ret > 0) {
    // MSAN doesn't recognise |syscall| and thus doesn't notice that we have
    // initialised the output buffer.
    __msan_unpoison(buf, ret);
  }
#endif  // OPENSSL_MSAN

  return ret;
}

#endif  // USE_NR_getrandom

// kHaveGetrandom in |urandom_fd| signals that |getrandom| or |getentropy| is
// available and should be used instead.
static const int kHaveGetrandom = -3;

// urandom_fd is a file descriptor to /dev/urandom. It's protected by |once|.
DEFINE_BSS_GET(int, urandom_fd)

#if defined(USE_NR_getrandom)

// getrandom_ready is one if |getrandom| had been initialized by the time
// |init_once| was called and zero otherwise.
DEFINE_BSS_GET(int, getrandom_ready)

// extra_getrandom_flags_for_seed contains a value that is ORed into the flags
// for getrandom() when reading entropy for a seed.
DEFINE_BSS_GET(int, extra_getrandom_flags_for_seed)

// On Android, check a system property to decide whether to set
// |extra_getrandom_flags_for_seed| otherwise they will default to zero.  If
// ro.oem_boringcrypto_hwrand is true then |extra_getrandom_flags_for_seed| will
// be set to GRND_RANDOM, causing all random data to be drawn from the same
// source as /dev/random.
static void maybe_set_extra_getrandom_flags(void) {
#if defined(BORINGSSL_FIPS) && defined(OPENSSL_ANDROID)
  char value[PROP_VALUE_MAX + 1];
  int length = __system_property_get("ro.boringcrypto.hwrand", value);
  if (length < 0 || length > PROP_VALUE_MAX) {
    return;
  }

  value[length] = 0;
  if (OPENSSL_strcasecmp(value, "true") == 0) {
    *extra_getrandom_flags_for_seed_bss_get() = GRND_RANDOM;
  }
#endif
}

#endif  // USE_NR_getrandom

DEFINE_STATIC_ONCE(rand_once)

// init_once initializes the state of this module to values previously
// requested. This is the only function that modifies |urandom_fd|, which may be
// read safely after calling the once.
static void init_once(void) {
#if defined(USE_NR_getrandom)
  int have_getrandom;
  uint8_t dummy;
  ssize_t getrandom_ret =
      boringssl_getrandom(&dummy, sizeof(dummy), GRND_NONBLOCK);
  if (getrandom_ret == 1) {
    *getrandom_ready_bss_get() = 1;
    have_getrandom = 1;
  } else if (getrandom_ret == -1 && errno == EAGAIN) {
    // We have getrandom, but the entropy pool has not been initialized yet.
    have_getrandom = 1;
  } else if (getrandom_ret == -1 && errno == ENOSYS) {
    // Fallthrough to using /dev/urandom, below.
    have_getrandom = 0;
  } else {
    // Other errors are fatal.
    perror("getrandom");
    abort();
  }

  if (have_getrandom) {
    *urandom_fd_bss_get() = kHaveGetrandom;
    maybe_set_extra_getrandom_flags();
    return;
  }
#endif  // USE_NR_getrandom

#if defined(OPENSSL_APPLE)
  // To get system randomness on MacOS and iOS we use |CCRandomGenerateBytes|
  // function provided by Apple rather than /dev/urandom or |getentropy|
  // function which is available on MacOS but not on iOS.
  return;
#endif

#if defined(FREEBSD_GETRANDOM)
  *urandom_fd_bss_get() = kHaveGetrandom;
  return;
#endif

  // Android FIPS builds must support getrandom.
#if defined(BORINGSSL_FIPS) && defined(OPENSSL_ANDROID)
  perror("getrandom not found");
  abort();
#endif

  int fd;
  do {
    fd = open("/dev/urandom", O_RDONLY);
  } while (fd == -1 && errno == EINTR);

  if (fd < 0) {
    perror("failed to open /dev/urandom");
    abort();
  }

  int flags = fcntl(fd, F_GETFD);
  if (flags == -1) {
    // Native Client doesn't implement |fcntl|.
    if (errno != ENOSYS) {
      perror("failed to get flags from urandom fd");
      abort();
    }
  } else {
    flags |= FD_CLOEXEC;
    if (fcntl(fd, F_SETFD, flags) == -1) {
      perror("failed to set FD_CLOEXEC on urandom fd");
      abort();
    }
  }
  *urandom_fd_bss_get() = fd;
}

DEFINE_STATIC_ONCE(wait_for_entropy_once)

static void wait_for_entropy(void) {
  int fd = *urandom_fd_bss_get();
  if (fd == kHaveGetrandom) {
    // |getrandom| and |getentropy| support blocking in |fill_with_entropy|
    // directly. For |getrandom|, we first probe with a non-blocking call to aid
    // debugging.
#if defined(USE_NR_getrandom)
    if (*getrandom_ready_bss_get()) {
      // The entropy pool was already initialized in |init_once|.
      return;
    }

    uint8_t dummy;
    ssize_t getrandom_ret =
        boringssl_getrandom(&dummy, sizeof(dummy), GRND_NONBLOCK);
    if (getrandom_ret == -1 && errno == EAGAIN) {
      // Attempt to get the path of the current process to aid in debugging when
      // something blocks.
      const char *current_process = "<unknown>";
#if defined(OPENSSL_HAS_GETAUXVAL)
      const unsigned long getauxval_ret = getauxval(AT_EXECFN);
      if (getauxval_ret != 0) {
        current_process = (const char *)getauxval_ret;
      }
#endif

      fprintf(
          stderr,
          "%s: getrandom indicates that the entropy pool has not been "
          "initialized. Rather than continue with poor entropy, this process "
          "will block until entropy is available.\n",
          current_process);

      getrandom_ret =
          boringssl_getrandom(&dummy, sizeof(dummy), 0 /* no flags */);
    }

    if (getrandom_ret != 1) {
      perror("getrandom");
      abort();
    }
#endif  // USE_NR_getrandom
    return;
  }

#if defined(BORINGSSL_FIPS) && !defined(URANDOM_BLOCKS_FOR_ENTROPY) && \
    !defined(OPENSSL_APPLE) // On MacOS and iOS we don't use /dev/urandom.

  // In FIPS mode on platforms where urandom doesn't block at startup, we ensure
  // that the kernel has sufficient entropy before continuing. This is
  // automatically handled by getrandom, which requires that the entropy pool
  // has been initialised, but for urandom we have to poll.

  for (;;) {
    int entropy_bits;
    if (ioctl(fd, RNDGETENTCNT, &entropy_bits)) {
      fprintf(stderr,
              "RNDGETENTCNT on /dev/urandom failed. We cannot continue in this "
              "case when in FIPS mode.\n");
      abort();
    }

    static const int kBitsNeeded = 256;
    if (entropy_bits >= kBitsNeeded) {
      break;
    }

    struct timespec sleep_time = {.tv_sec = 0, .tv_nsec = MILLISECONDS_250 };
    nanosleep(&sleep_time, &sleep_time);
  }
#endif  // BORINGSSL_FIPS && !URANDOM_BLOCKS_FOR_ENTROPY
}

// fill_with_entropy writes |len| bytes of entropy into |out|. It returns one
// on success and zero on error. If |block| is one, this function will block
// until the entropy pool is initialized. Otherwise, this function may fail,
// setting |errno| to |EAGAIN| if the entropy pool has not yet been initialized.
// If |seed| is one, this function will OR in the value of
// |*extra_getrandom_flags_for_seed()| when using |getrandom|.
static int fill_with_entropy(uint8_t *out, size_t len, int block, int seed) {
  if (len == 0) {
    return 1;
  }

#if defined(OPENSSL_APPLE)
  // To get system randomness on MacOS and iOS we use |CCRandomGenerateBytes|
  // rather than |getentropy| and /dev/urandom.
  if (CCRandomGenerateBytes(out, len) == kCCSuccess) {
    return 1;
  } else {
    fprintf(stderr, "CCRandomGenerateBytes failed.\n");
    abort();
  }
#endif

#if defined(USE_NR_getrandom) || defined(FREEBSD_GETRANDOM)
  int getrandom_flags = 0;
  if (!block) {
    getrandom_flags |= GRND_NONBLOCK;
  }
#endif

#if defined (USE_NR_getrandom)
  if (seed) {
    getrandom_flags |= *extra_getrandom_flags_for_seed_bss_get();
  }
#endif

  CRYPTO_init_sysrand();
  if (block) {
    CRYPTO_once(wait_for_entropy_once_bss_get(), wait_for_entropy);
  }

  // Clear |errno| so it has defined value if |read| or |getrandom|
  // "successfully" returns zero.
  errno = 0;
  while (len > 0) {
    ssize_t r;

    if (*urandom_fd_bss_get() == kHaveGetrandom) {
#if defined(USE_NR_getrandom)
      r = boringssl_getrandom(out, len, getrandom_flags);
#elif defined(FREEBSD_GETRANDOM)
      r = getrandom(out, len, getrandom_flags);
#else  // USE_NR_getrandom
      fprintf(stderr, "urandom fd corrupt.\n");
      abort();
#endif
    } else {
      size_t retry_counter = 0;
      long backoff = INITIAL_BACKOFF_DELAY;
      do {
        r = read(*urandom_fd_bss_get(), out, len);
        if ((r == -1) && (errno != EINTR)) {
          if (retry_counter >= MAX_BACKOFF_RETRIES) {
            break;
          }
          // We have observed extremely rare events in which a |read| on a
          // |urandom| fd failed with |errno| != |EINTR|. We regard this as an
          // intermittent error that is recoverable. Therefore, backoff to allow
          // recovery and to avoid creating a tight spinning loop.
          handle_rare_urandom_error(&backoff);
          retry_counter = retry_counter + 1;
        }
      } while (r == -1);
    }

    if (r <= 0) {
      return 0;
    }
    out += r;
    len -= r;
  }

  return 1;
}

void CRYPTO_init_sysrand(void) {
  CRYPTO_once(rand_once_bss_get(), init_once);
}

// CRYPTO_sysrand puts |requested| random bytes into |out|.
void CRYPTO_sysrand(uint8_t *out, size_t requested) {
  if (!fill_with_entropy(out, requested, /*block=*/1, /*seed=*/0)) {
    perror("entropy fill failed");
    abort();
  }
}

void CRYPTO_sysrand_for_seed(uint8_t *out, size_t requested) {
  if (!fill_with_entropy(out, requested, /*block=*/1, /*seed=*/1)) {
    perror("entropy fill failed");
    abort();
  }
}

int CRYPTO_sysrand_if_available(uint8_t *out, size_t requested) {
  if (fill_with_entropy(out, requested, /*block=*/0, /*seed=*/0)) {
    return 1;
  } else if (errno == EAGAIN) {
    OPENSSL_memset(out, 0, requested);
    return 0;
  } else {
    perror("opportunistic entropy fill failed");
    abort();
  }
}

#endif  // OPENSSL_RAND_URANDOM
