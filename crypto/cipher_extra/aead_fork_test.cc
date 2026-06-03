// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>

// This test requires fork() and mmap(), only available on Linux/POSIX.
// TSAN cannot cope with fork-based tests.
#if defined(OPENSSL_LINUX) && !defined(OPENSSL_TSAN)

#include <errno.h>
#include <signal.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#include <gtest/gtest.h>

#include <openssl/aead.h>
#include <openssl/rand.h>

// Tests that EVP_AEAD_CTX_cleanup is safe when used across fork() boundaries
// with shared memory. DEFINE_METHOD_FUNCTION stores AEAD vtables in .bss and
// lazily initializes them via CRYPTO_once. After fork(), parent and child have
// independent copies of .bss. If only the child triggers initialization, the
// parent's vtable remains zeroed. EVP_AEAD_CTX_cleanup must tolerate this.

static pid_t WaitpidEINTR(pid_t pid, int *out_status) {
  pid_t ret = 0;
  do {
    ret = waitpid(pid, out_status, 0);
  } while (ret < 0 && errno == EINTR);
  return ret;
}

// RunInChild forks and runs |func| in the child. Returns the child's exit
// status. If the child is killed by a signal, returns -(signal_number).
static int RunInChild(std::function<void()> func) {
  fflush(stdout);
  fflush(stderr);

  pid_t pid = fork();
  if (pid < 0) {
    return -1;
  }
  if (pid == 0) {
    func();
    _exit(0);
  }

  int status;
  if (WaitpidEINTR(pid, &status) < 0) {
    return -1;
  }
  if (WIFEXITED(status)) {
    return WEXITSTATUS(status);
  }
  if (WIFSIGNALED(status)) {
    return -(WTERMSIG(status));
  }
  return -1;
}

// Test that EVP_AEAD_CTX_cleanup tolerates an uninitialized AEAD vtable.
// A child process initializes an EVP_AEAD_CTX in shared memory (triggering
// lazy vtable init in its own .bss), then the parent process (whose vtable
// is still zeroed) calls cleanup. EVP_AEAD_CTX_cleanup must not crash.
TEST(AEADForkTest, CleanupToleratesUninitializedVtable) {
  void *shm = mmap(NULL, 4096, PROT_READ | PROT_WRITE,
                   MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  ASSERT_NE(shm, MAP_FAILED);
  memset(shm, 0, 4096);

  EVP_AEAD_CTX *ctx = reinterpret_cast<EVP_AEAD_CTX *>(shm);

  // Child: initialize the AEAD context in shared memory.
  int child_status = RunInChild([ctx]() {
    const EVP_AEAD *aead = EVP_aead_aes_128_gcm_tls12();
    uint8_t key[16];
    RAND_bytes(key, sizeof(key));
    if (!EVP_AEAD_CTX_init(ctx, aead, key, sizeof(key),
                           EVP_AEAD_DEFAULT_TAG_LENGTH, NULL)) {
      _exit(1);
    }
  });
  ASSERT_EQ(child_status, 0) << "Child failed to initialize AEAD context";
  ASSERT_NE(ctx->aead, nullptr);

  // Parent attempts cleanup. Its vtable copy is uninitialized (all zeros)
  // because CRYPTO_once was never triggered in this process for this AEAD.
  // The fix: EVP_AEAD_CTX_cleanup null-checks the cleanup function pointer.
  int cleanup_status = RunInChild([ctx]() {
    signal(SIGSEGV, SIG_DFL);
    EVP_AEAD_CTX_cleanup(ctx);
  });

  EXPECT_EQ(cleanup_status, 0)
      << "EVP_AEAD_CTX_cleanup should not crash with uninitialized vtable, "
         "got status " << cleanup_status;

  munmap(shm, 4096);
}

// Test that the crash is prevented when the parent initializes the AEAD vtable
// before attempting cleanup. This is the workaround: ensure all AEAD vtables
// are initialized before fork(), or at least before any cross-process cleanup.
TEST(AEADForkTest, CleanupSucceedsWithInitializedVtable) {
  void *shm = mmap(NULL, 4096, PROT_READ | PROT_WRITE,
                   MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  ASSERT_NE(shm, MAP_FAILED);
  memset(shm, 0, 4096);

  EVP_AEAD_CTX *ctx = reinterpret_cast<EVP_AEAD_CTX *>(shm);

  // Parent pre-initializes AEAD vtables BEFORE fork (the workaround).
  (void)EVP_aead_aes_128_gcm_tls12();

  // Child initializes context in shared memory.
  int child_status = RunInChild([ctx]() {
    const EVP_AEAD *aead = EVP_aead_aes_128_gcm_tls12();
    uint8_t key[16];
    RAND_bytes(key, sizeof(key));
    if (!EVP_AEAD_CTX_init(ctx, aead, key, sizeof(key),
                           EVP_AEAD_DEFAULT_TAG_LENGTH, NULL)) {
      _exit(1);
    }
  });
  ASSERT_EQ(child_status, 0);

  // Parent cleanup should now succeed because its vtable is initialized.
  int cleanup_status = RunInChild([ctx]() {
    signal(SIGSEGV, SIG_DFL);
    EVP_AEAD_CTX_cleanup(ctx);
  });

  EXPECT_EQ(cleanup_status, 0)
      << "Cleanup should succeed when parent vtable is initialized, got status "
      << cleanup_status;

  munmap(shm, 4096);
}

// Test pre-fork initialization: if vtables are initialized before fork(),
// both parent and child inherit initialized state.
TEST(AEADForkTest, PreForkInitProtectsBothProcesses) {
  // Initialize ALL common AEAD vtables before fork.
  (void)EVP_aead_aes_128_gcm();
  (void)EVP_aead_aes_256_gcm();
  (void)EVP_aead_aes_128_gcm_tls12();
  (void)EVP_aead_aes_256_gcm_tls12();
  (void)EVP_aead_aes_128_gcm_tls13();
  (void)EVP_aead_aes_256_gcm_tls13();

  void *shm = mmap(NULL, 4096, PROT_READ | PROT_WRITE,
                   MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  ASSERT_NE(shm, MAP_FAILED);
  memset(shm, 0, 4096);

  EVP_AEAD_CTX *ctx = reinterpret_cast<EVP_AEAD_CTX *>(shm);

  // Child initializes and seals data.
  int child_status = RunInChild([ctx]() {
    const EVP_AEAD *aead = EVP_aead_aes_128_gcm_tls12();
    uint8_t key[16];
    RAND_bytes(key, sizeof(key));
    if (!EVP_AEAD_CTX_init(ctx, aead, key, sizeof(key),
                           EVP_AEAD_DEFAULT_TAG_LENGTH, NULL)) {
      _exit(1);
    }
    // Seal some data to exercise the full path.
    uint8_t nonce[12] = {0};
    uint8_t pt[] = "test";
    uint8_t ct[128];
    size_t ct_len;
    if (!EVP_AEAD_CTX_seal(ctx, ct, &ct_len, sizeof(ct), nonce, sizeof(nonce),
                           pt, sizeof(pt), NULL, 0)) {
      _exit(2);
    }
  });
  ASSERT_EQ(child_status, 0);

  // Parent cleanup should work.
  int cleanup_status = RunInChild([ctx]() {
    signal(SIGSEGV, SIG_DFL);
    EVP_AEAD_CTX_cleanup(ctx);
  });

  EXPECT_EQ(cleanup_status, 0);

  munmap(shm, 4096);
}

#endif  // OPENSSL_LINUX && !OPENSSL_TSAN
