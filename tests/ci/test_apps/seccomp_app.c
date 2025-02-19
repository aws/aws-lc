// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <seccomp.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <openssl/crypto.h>
#include <openssl/rand.h>

static void enable_seccomp(void) {

  // Kill on all system calls by default.
  scmp_filter_ctx ctx = seccomp_init(SCMP_ACT_KILL);
  if (ctx == NULL) {
    exit(EXIT_FAILURE);
  }

  // Allow write and exit system calls. In addition, on success we exit with
  // exit_group. Hence, allow that as well.
  seccomp_rule_add(ctx, SCMP_ACT_ALLOW, SCMP_SYS(write), 0);
  seccomp_rule_add(ctx, SCMP_ACT_ALLOW, SCMP_SYS(exit), 0);
  seccomp_rule_add(ctx, SCMP_ACT_ALLOW, SCMP_SYS(exit_group), 0);
  seccomp_rule_add(ctx, SCMP_ACT_ALLOW, SCMP_SYS(futex), 0);

  // Since we are running this test on a Linux system, we must allow both
  // |getrandom|. It is assumed that the Linux system has |getrandom|. If the
  // sandbox test fails with a read on |/dev/urandom| this is not the case.
  seccomp_rule_add(ctx, SCMP_ACT_ALLOW, SCMP_SYS(getrandom), 0);

  if (seccomp_load(ctx) < 0) {
    seccomp_release(ctx);
    exit(EXIT_FAILURE);
  }

  seccomp_release(ctx);
}

int main() {

  const char notice[] = "\nTesting AWS-LC pre-sandbox.\n";
#if defined(USE_AWS_LC_PRE_SANDBOX)
  const char status[] = "Pre-sandbox configuration is ENABLED, expect success.\n\n";
#else
  const char status[] = "Pre-sandbox configuration is DISABLED, expect failure.\n\n";
#endif

  write(STDOUT_FILENO, notice, sizeof(notice));
  write(STDOUT_FILENO, status, sizeof(status));

#if defined(USE_AWS_LC_PRE_SANDBOX)
  // Must be invoked before enabling seccomp filter.
  CRYPTO_pre_sandbox_init();
#endif

  // Enable seccomp filter.
  enable_seccomp();

  uint8_t buffer[10];
  if (RAND_bytes(buffer, 10) != 1) {
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}
