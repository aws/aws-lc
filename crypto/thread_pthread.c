/* Copyright (c) 2015, Google Inc.
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

// Ensure we can't call OPENSSL_malloc circularly.
#define _BORINGSSL_PROHIBIT_OPENSSL_MALLOC
#include <errno.h>

#include "internal.h"

#if defined(OPENSSL_PTHREADS)

#include <pthread.h>
#include <stdlib.h>
#include <string.h>

#include <openssl/type_check.h>


OPENSSL_STATIC_ASSERT(sizeof(CRYPTO_MUTEX) >= sizeof(pthread_rwlock_t),
                      CRYPTO_MUTEX_is_too_small)
OPENSSL_STATIC_ASSERT(alignof(CRYPTO_MUTEX) >= alignof(pthread_rwlock_t),
                      CRYPTO_MUTEX_has_insufficient_alignment)

void CRYPTO_MUTEX_init(CRYPTO_MUTEX *lock) {
  if (pthread_rwlock_init((pthread_rwlock_t *) lock, NULL) != 0) {
    abort();
  }
}

void CRYPTO_MUTEX_lock_read(CRYPTO_MUTEX *lock) {
  if (pthread_rwlock_rdlock((pthread_rwlock_t *) lock) != 0) {
    abort();
  }
}

void CRYPTO_MUTEX_lock_write(CRYPTO_MUTEX *lock) {
  if (pthread_rwlock_wrlock((pthread_rwlock_t *) lock) != 0) {
    abort();
  }
}

void CRYPTO_MUTEX_unlock_read(CRYPTO_MUTEX *lock) {
  if (pthread_rwlock_unlock((pthread_rwlock_t *) lock) != 0) {
    abort();
  }
}

void CRYPTO_MUTEX_unlock_write(CRYPTO_MUTEX *lock) {
  if (pthread_rwlock_unlock((pthread_rwlock_t *) lock) != 0) {
    abort();
  }
}

void CRYPTO_MUTEX_cleanup(CRYPTO_MUTEX *lock) {
  pthread_rwlock_destroy((pthread_rwlock_t *) lock);
}

// Some MinGW pthreads implementations might fail on first use of
// locks initialized using PTHREAD_RWLOCK_INITIALIZER.
// See: https://sourceforge.net/p/mingw-w64/bugs/883/
typedef int (*pthread_rwlock_func_ptr)(pthread_rwlock_t *);
static int rwlock_EINVAL_fallback_retry(const pthread_rwlock_func_ptr func_ptr, pthread_rwlock_t* lock) {
  int result = EINVAL;
#ifdef __MINGW32__
  const int MAX_ATTEMPTS = 10;
  int attempt_num = 0;
  do {
    sched_yield();
    attempt_num += 1;
    result = func_ptr(lock);
  } while(result == EINVAL && attempt_num < MAX_ATTEMPTS);
#endif
  return result;
}

void CRYPTO_STATIC_MUTEX_lock_read(struct CRYPTO_STATIC_MUTEX *lock) {
  const int result = pthread_rwlock_rdlock(&lock->lock);
  if (result != 0) {
    if (result == EINVAL &&
        0 == rwlock_EINVAL_fallback_retry(pthread_rwlock_rdlock, &lock->lock)) {
      return;
    }
    abort();
  }
}

void CRYPTO_STATIC_MUTEX_lock_write(struct CRYPTO_STATIC_MUTEX *lock) {
  const int result = pthread_rwlock_wrlock(&lock->lock);
  if (result != 0) {
    if (result == EINVAL &&
        0 == rwlock_EINVAL_fallback_retry(pthread_rwlock_wrlock, &lock->lock)) {
      return;
    }
    abort();
  }
}

void CRYPTO_STATIC_MUTEX_unlock_read(struct CRYPTO_STATIC_MUTEX *lock) {
  if (pthread_rwlock_unlock(&lock->lock) != 0) {
    abort();
  }
}

void CRYPTO_STATIC_MUTEX_unlock_write(struct CRYPTO_STATIC_MUTEX *lock) {
  if (pthread_rwlock_unlock(&lock->lock) != 0) {
    abort();
  }
}

#if !defined(NDEBUG)
int CRYPTO_STATIC_MUTEX_is_write_locked(struct CRYPTO_STATIC_MUTEX *lock) {
  assert(lock != NULL);

  int result = pthread_rwlock_tryrdlock(&lock->lock);

  if (result == 0) {
    // If we successfully acquired the lock, it wasn't locked
    // Release it immediately and return false
    pthread_rwlock_unlock(&lock->lock);
    return 0;
  }
  // errno may be set to EDEADLK if the current thread is already has a write lock
  if (result == EBUSY || result == EDEADLK) {
    return 1;
  }

  return -1;
}
#endif

void CRYPTO_once(CRYPTO_once_t *once, void (*init)(void)) {
  if (pthread_once(once, init) != 0) {
    abort();
  }
}

static pthread_mutex_t g_destructors_lock = PTHREAD_MUTEX_INITIALIZER;
static thread_local_destructor_t g_destructors[NUM_OPENSSL_THREAD_LOCALS];

// thread_local_destructor is called when a thread exits. It releases thread
// local data for that thread only.
static void thread_local_destructor(void *arg) {
  if (arg == NULL) {
    return;
  }

  thread_local_destructor_t destructors[NUM_OPENSSL_THREAD_LOCALS];
  if (pthread_mutex_lock(&g_destructors_lock) != 0) {
    return;
  }
  OPENSSL_memcpy(destructors, g_destructors, sizeof(destructors));
  pthread_mutex_unlock(&g_destructors_lock);

  unsigned i;
  void **pointers = arg;
  for (i = 0; i < NUM_OPENSSL_THREAD_LOCALS; i++) {
    if (destructors[i] != NULL) {
      destructors[i](pointers[i]);
    }
  }

  free(pointers);
}

static pthread_once_t g_thread_local_init_once = PTHREAD_ONCE_INIT;
static pthread_key_t g_thread_local_key;
static int g_thread_local_key_created = 0;

static void thread_local_init(void) {
  g_thread_local_key_created =
      pthread_key_create(&g_thread_local_key, thread_local_destructor) == 0;
}

void *CRYPTO_get_thread_local(thread_local_data_t index) {
  CRYPTO_once(&g_thread_local_init_once, thread_local_init);
  if (!g_thread_local_key_created) {
    return NULL;
  }

  void **pointers = pthread_getspecific(g_thread_local_key);
  if (pointers == NULL) {
    return NULL;
  }
  return pointers[index];
}

int CRYPTO_set_thread_local(thread_local_data_t index, void *value,
                            thread_local_destructor_t destructor) {
  CRYPTO_once(&g_thread_local_init_once, thread_local_init);
  if (!g_thread_local_key_created) {
    destructor(value);
    return 0;
  }

  void **pointers = pthread_getspecific(g_thread_local_key);
  if (pointers == NULL) {
    pointers = malloc(sizeof(void *) * NUM_OPENSSL_THREAD_LOCALS);
    if (pointers == NULL) {
      destructor(value);
      return 0;
    }
    OPENSSL_memset(pointers, 0, sizeof(void *) * NUM_OPENSSL_THREAD_LOCALS);
    if (pthread_setspecific(g_thread_local_key, pointers) != 0) {
      free(pointers);
      destructor(value);
      return 0;
    }
  }

  if (pthread_mutex_lock(&g_destructors_lock) != 0) {
    destructor(value);
    return 0;
  }
  g_destructors[index] = destructor;
  pthread_mutex_unlock(&g_destructors_lock);

  pointers[index] = value;
  return 1;
}

int AWSLC_thread_local_clear(void) {
  if (!g_thread_local_key_created) {
    return 1;
  }
  void *pointers = pthread_getspecific(g_thread_local_key);
  thread_local_destructor(pointers);
  // By setting the value NULL, thread_local_destructor will not be called when
  // this thread dies.
  if (0 != pthread_setspecific(g_thread_local_key, NULL)) {
    return 0;
  }
  return 1;
}

// This function is not thread-safe. It should only be called on a thread that
// is prepared to also call `dlclose` to unload our shared library.
int AWSLC_thread_local_shutdown(void) {
  if (!g_thread_local_key_created) {
    return 1;
  }
  // This deletes the thread local key
  if (0 != pthread_key_delete(g_thread_local_key)) {
    return 0;
  }

  g_thread_local_key_created = 0;
  return 1;
}

#endif  // OPENSSL_PTHREADS
