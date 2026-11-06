// Copyright (c) 2020, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/base.h>

// TSAN cannot cope with this test and complains that "starting new threads
// after multi-threaded fork is not supported".
#if defined(OPENSSL_LINUX) && !defined(OPENSSL_TSAN)
#include <errno.h>

#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif
#include <inttypes.h>

#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include <atomic>
#include <functional>

#if defined(OPENSSL_THREADS)
#include <thread>
#include <vector>
#endif

#include <gtest/gtest.h>

#include "fork_ube_detect.h"

#include "../test/test_util.h"


static pid_t WaitpidEINTR(pid_t pid, int *out_status, int options) {
  pid_t ret;
  do {
    ret = waitpid(pid, out_status, options);
  } while (ret < 0 && errno == EINTR);

  return ret;
}

// The *InChild functions run inside a child process and must report errors via
// |stderr| and |_exit| rather than GTest.

static void CheckGenerationInChild(const char *name, uint64_t expected) {
  uint64_t generation = CRYPTO_get_fork_ube_generation();
  if (generation != expected) {
    fprintf(stderr, "%s generation (#1) was %" PRIu64 ", wanted %" PRIu64 ".\n",
            name, generation, expected);
    _exit(1);
  }

  // The generation should be stable.
  generation = CRYPTO_get_fork_ube_generation();
  if (generation != expected) {
    fprintf(stderr, "%s generation (#2) was %" PRIu64 ", wanted %" PRIu64 ".\n",
            name, generation, expected);
    _exit(1);
  }
}

// ForkInChild forks a child which runs |f|. If the child exits unsuccessfully,
// this function will also exit unsuccessfully.
static void ForkInChild(std::function<void()> f) {
  fflush(stderr);  // Avoid duplicating any buffered output.

  const pid_t pid = fork();
  if (pid < 0) {
    perror("fork");
    _exit(1);
  } else if (pid == 0) {
    f();
    _exit(0);
  }

  // Wait for the child and pass its exit code up.
  int status;
  if (WaitpidEINTR(pid, &status, 0) < 0) {
    perror("waitpid");
    _exit(1);
  }
  if (!WIFEXITED(status)) {
    fprintf(stderr, "Child did not exit cleanly.\n");
    _exit(1);
  }
  if (WEXITSTATUS(status) != 0) {
    // Pass the failure up.
    _exit(WEXITSTATUS(status));
  }
}

TEST(ForkDetect, Test) {

  maybeDisableSomeForkUbeDetectMechanisms();

  const uint64_t start = CRYPTO_get_fork_ube_generation();
  if (start == 0) {
    fprintf(stderr, "Fork detection not supported. Skipping test.\n");
    return;
  }

  // The fork generation should be stable.
  EXPECT_EQ(start, CRYPTO_get_fork_ube_generation());

  fflush(stderr);
  const pid_t child = fork();

  if (child == 0) {
    // Fork grandchildren before observing the fork generation. The
    // grandchildren will observe |start| + 1.
    for (int i = 0; i < 2; i++) {
      ForkInChild([&] { CheckGenerationInChild("Grandchild", start + 1); });
    }

    // Now the child also observes |start| + 1. This is fine because it has
    // already diverged from the grandchild at this point.
    CheckGenerationInChild("Child", start + 1);

    // Forked grandchildren will now observe |start| + 2.
    for (int i = 0; i < 2; i++) {
      ForkInChild([&] { CheckGenerationInChild("Grandchild", start + 2); });
    }

#if defined(OPENSSL_THREADS)
    // The fork generation logic itself must be thread-safe. We test this in a
    // child process to capture the actual fork detection. This segment is meant
    // to be tested in TSan.
    ForkInChild([&] {
      std::vector<std::thread> threads(4);
      for (int i = 0; i < 2; i++) {
        for (auto &t : threads) {
          t = std::thread(
              [&] { CheckGenerationInChild("Grandchild thread", start + 2); });
        }
        for (auto &t : threads) {
          t.join();
        }
      }
    });
#endif  // OPENSSL_THREADS

    // The child still observes |start| + 1.
    CheckGenerationInChild("Child", start + 1);
    _exit(0);
  }

  ASSERT_GT(child, 0) << "Error in fork: " << strerror(errno);
  int status;
  ASSERT_EQ(child, WaitpidEINTR(child, &status, 0))
      << "Error in waitpid: " << strerror(errno);
  ASSERT_TRUE(WIFEXITED(status));
  EXPECT_EQ(0, WEXITSTATUS(status)) << "Error in child process";

  // We still observe |start|.
  EXPECT_EQ(start, CRYPTO_get_fork_ube_generation());
}

#if defined(OPENSSL_THREADS)
// Allow time for instrumented runs (such as Valgrind), without letting a
// stuck fork regression block the suite. Always kill and reap on failure.
static bool WaitForForkTestChild(pid_t child, int *status) {
  for (int tick = 0; tick < 3000; ++tick) {
    const pid_t result = WaitpidEINTR(child, status, WNOHANG);
    if (result == child) {
      return true;
    }
    if (result < 0) {
      break;
    }
    usleep(10000);
  }
  kill(child, SIGKILL);
  WaitpidEINTR(child, status, 0);
  return false;
}

// Every reader enters the fork-generation check simultaneously in a new
// child. No generation read or RAND call may re-arm the fork flag first.
TEST(ForkDetect, SimultaneousFirstReadAfterFork) {
  maybeDisableSomeForkUbeDetectMechanisms();
  const uint64_t parent_generation = CRYPTO_get_fork_ube_generation();
  if (parent_generation == 0) {
    GTEST_SKIP() << "Fork detection unavailable";
  }
  constexpr int kReaders = 8;
  constexpr int kForks = 40;
  for (int round = 0; round < kForks; ++round) {
    fflush(stderr);
    const pid_t child = fork();
    if (child == 0) {
      std::atomic<int> ready{0};
      std::atomic<bool> go{false}, failed{false};
      std::vector<std::thread> threads;
      for (int i = 0; i < kReaders; ++i) {
        threads.emplace_back([&] {
          ready.fetch_add(1, std::memory_order_release);
          while (!go.load(std::memory_order_acquire)) {
            std::this_thread::yield();
          }
          const uint64_t first = CRYPTO_get_fork_ube_generation();
          const uint64_t second = CRYPTO_get_fork_ube_generation();
          if (first != parent_generation + 1 ||
              second != parent_generation + 1) {
            failed.store(true, std::memory_order_release);
          }
        });
      }
      while (ready.load(std::memory_order_acquire) != kReaders) {
        std::this_thread::yield();
      }
      go.store(true, std::memory_order_release);
      for (auto &thread : threads) {
        thread.join();
      }
      _exit(failed.load(std::memory_order_acquire) ? 1 : 0);
    }
    ASSERT_GT(child, 0) << "fork failed: " << strerror(errno);
    int status = 0;
    ASSERT_TRUE(WaitForForkTestChild(child, &status))
        << "Child timed out or waitpid failed in round " << round;
    ASSERT_TRUE(WIFEXITED(status)) << "child terminated abnormally";
    ASSERT_EQ(0, WEXITSTATUS(status))
        << "first read mismatch in round " << round;
    EXPECT_EQ(parent_generation, CRYPTO_get_fork_ube_generation());
  }
}
#endif  // OPENSSL_THREADS

#endif  // OPENSSL_LINUX && !OPENSSL_TSAN
