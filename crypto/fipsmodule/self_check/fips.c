// Copyright (c) 2017, Google Inc.
// SPDX-License-Identifier: ISC

// Ensure we can't call OPENSSL_malloc
#define _BORINGSSL_PROHIBIT_OPENSSL_MALLOC
#include <openssl/crypto.h>

#include "../../internal.h"
#include "../delocate.h"

#include "../rand/entropy/internal.h"

// When built for distribution packaging (ENABLE_DIST_PKG), a FIPS build on
// Linux reports FIPS mode as enabled only when the host requests it.
#if defined(BORINGSSL_FIPS) && !defined(OPENSSL_ASAN) && \
    !defined(OPENSSL_MSAN) && defined(AWSLC_DIST_PKG) && \
    defined(OPENSSL_LINUX)
#define AWSLC_FIPS_MODE_HOST_SWITCH
#endif

#if defined(AWSLC_FIPS_MODE_HOST_SWITCH)
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>

// fips_mode_host_flag caches the host's answer so the environment and /proc
// are consulted once per process.
DEFINE_BSS_GET(int, fips_mode_host_flag)
DEFINE_STATIC_ONCE(fips_mode_host_flag_once)

// read_fips_mode_host_flag sets |fips_mode_host_flag| to one if the
// AWSLC_FORCE_FIPS_MODE environment variable is set or the kernel's
// /proc/sys/crypto/fips_enabled switch reads "1", and to zero otherwise.
static void read_fips_mode_host_flag(void) {
  if (getenv("AWSLC_FORCE_FIPS_MODE") != NULL) {
    *fips_mode_host_flag_bss_get() = 1;
    return;
  }

  int fd;
  do {
    fd = open("/proc/sys/crypto/fips_enabled", O_RDONLY);
  } while (fd < 0 && errno == EINTR);
  if (fd < 0) {
    *fips_mode_host_flag_bss_get() = 0;
    return;
  }

  char buf[2] = {0};
  ssize_t n;
  do {
    n = read(fd, buf, sizeof(buf));
  } while (n < 0 && errno == EINTR);
  close(fd);

  *fips_mode_host_flag_bss_get() = (n > 0 && buf[0] == '1');
}
#endif  // AWSLC_FIPS_MODE_HOST_SWITCH

int FIPS_mode(void) {
#if defined(AWSLC_FIPS_MODE_HOST_SWITCH)
  CRYPTO_once(fips_mode_host_flag_once_bss_get(), read_fips_mode_host_flag);
  return *fips_mode_host_flag_bss_get();
#elif defined(BORINGSSL_FIPS) && !defined(OPENSSL_ASAN) && \
    !defined(OPENSSL_MSAN)
  return 1;
#else
  return 0;
#endif
}

int FIPS_is_entropy_cpu_jitter(void) {
  if (OPT_OUT_CPU_JITTER_ENTROPY_SOURCE == get_entropy_source_method_id_FOR_TESTING()) {
    return 0;
  }
  return 1;
}

uint32_t FIPS_version(void) {
#if defined(BORINGSSL_FIPS) && !defined(OPENSSL_ASAN) && !defined(OPENSSL_MSAN)
  return AWSLC_FIPS_VERSION_NUMBER;
#else
  return 0;
#endif
}

const char *FIPS_module_name(void) { return AWSLC_MODULE_NAME_STRING; }

int FIPS_mode_set(int on) { return on == FIPS_mode(); }
