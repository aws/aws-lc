// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>

#include <openssl/buf.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/x509.h>

#include "internal.h"
#include "../internal.h"

# include <signal.h>
# include <string.h>
# include <errno.h>

// We support two types of terminal interface:
// - termios for Linux/Unix
// - WIN32 Console for Windows
# if !defined(OPENSSL_WINDOWS)
#  include <termios.h>
#  define DEV_TTY "/dev/tty"
#  define TTY_STRUCT             struct termios
#  define TTY_FLAGS              c_lflag
#  define TTY_get(tty,data)      tcgetattr(tty, data)
#  define TTY_set(tty,data)      tcsetattr(tty, TCSANOW, data)
# else /* OPENSSL_WINDOWS */
#  include <windows.h>
# endif

# define NUM_SIG 32

static volatile sig_atomic_t intr_signal;
static struct CRYPTO_STATIC_MUTEX console_global_mutex = CRYPTO_STATIC_MUTEX_INIT;

# if !defined(OPENSSL_WINDOWS)
static struct sigaction savsig[NUM_SIG];
# else
static void (*savsig[NUM_SIG]) (int);
# endif

#if defined(OPENSSL_WINDOWS)
  DWORD tty_orig, tty_new;
#else
  TTY_STRUCT tty_orig, tty_new;
#endif

FILE *tty_in, *tty_out;
int is_a_tty;


static void popsig(void) {
# if !defined(OPENSSL_WINDOWS)
    for (int i = 1; i < NUM_SIG; i++) {
        if (i == SIGUSR1 || i == SIGUSR2 || i == SIGKILL) {
            continue;
        }
        sigaction(i, &savsig[i], NULL);
    }
# else
    signal(SIGABRT, savsig[SIGABRT]);
    signal(SIGFPE, savsig[SIGFPE]);
    signal(SIGILL, savsig[SIGILL]);
    signal(SIGINT, savsig[SIGINT]);
    signal(SIGSEGV, savsig[SIGSEGV]);
    signal(SIGTERM, savsig[SIGTERM]);
# endif
}

static void recsig(int signal) {
    intr_signal = signal;
}

static int discard_line_remainder(FILE *in) {
    char buf[5];

    do {
        if (!fgets(buf, 4, in)) {
            return 0;
        }
    } while (strchr(buf, '\n') == NULL);
    return 1;
}

/* Signal handling functions */
static void pushsig(void) {
# if !defined(OPENSSL_WINDOWS)
    struct sigaction sa;
    OPENSSL_cleanse(&sa, sizeof(sa));

    sa.sa_handler = recsig;

    for (int i = 1; i < NUM_SIG; i++) {
        if (i == SIGUSR1 || i == SIGUSR2 || i == SIGKILL) {
            continue;
        }
        sigaction(i, &sa, &savsig[i]);
    }
# else // Specific error codes for windows
    savsig[SIGABRT] = signal(SIGABRT, recsig);
    savsig[SIGFPE] = signal(SIGFPE, recsig);
    savsig[SIGILL] = signal(SIGILL, recsig);
    savsig[SIGINT] = signal(SIGINT, recsig);
    savsig[SIGSEGV] = signal(SIGSEGV, recsig);
    savsig[SIGTERM] = signal(SIGTERM, recsig);
# endif

// set SIGWINCH handler to default so our workflow is not
// triggered on user resizing of window
# if defined(SIGWINCH) && defined(SIG_DFL)
    signal(SIGWINCH, SIG_DFL);
# endif
}

/* Console management functions */
void openssl_console_acquire_mutex(void) {
    CRYPTO_STATIC_MUTEX_lock_write(&console_global_mutex);
}

void openssl_console_release_mutex(void) {
    CRYPTO_STATIC_MUTEX_unlock_write(&console_global_mutex);
}

int openssl_console_open(void) {
    is_a_tty = 1;
    assert(CRYPTO_STATIC_MUTEX_is_write_locked(&console_global_mutex) == 1);

#if !defined(OPENSSL_WINDOWS)
    if ((tty_in = fopen(DEV_TTY, "r")) == NULL) {
        tty_in = stdin;
    }
    if ((tty_out = fopen(DEV_TTY, "w")) == NULL) {
        tty_out = stderr;
    }
    if (TTY_get(fileno(tty_in), &tty_orig) == -1) {
        if (errno == ENOTTY || errno == EINVAL || errno == ENXIO || errno == EIO
          || errno == EPERM || errno == ENODEV) {
            is_a_tty = 0;
          } else {
              OPENSSL_PUT_ERROR(PEM, ERR_R_INTERNAL_ERROR);
              return 0;
          }
    }
# else
    DWORD console_mode;
    HANDLE hStdIn = GetStdHandle(STD_INPUT_HANDLE);

    // Check if console (equivalent to checking for /dev/tty on Linux)
    if (GetConsoleMode(hStdIn, &console_mode)) {
        // It's a real console, use conin$ and conout$ to bypass any redirection
        if ((tty_in = fopen("conin$", "r")) == NULL) {
            tty_in = stdin;
        }
        if ((tty_out = fopen("conout$", "w")) == NULL) {
            tty_out = stderr;
        }

        tty_orig = console_mode;
    } else {
        // Not a console, use stdin/stderr
        tty_in = stdin;
        tty_out = stderr;
        is_a_tty = 0;
    }
#endif
    return 1;
}

int openssl_console_close(void) {
    if (tty_in != stdin) {
        fclose(tty_in);
    }
    if (tty_out != stderr) {
        fclose(tty_out);
    }

    return 1;
}

static int openssl_console_echo_disable(void) {
# if !defined(OPENSSL_WINDOWS)
    OPENSSL_memcpy(&(tty_new), &(tty_orig), sizeof(tty_orig));
    tty_new.TTY_FLAGS &= ~ECHO;

    if (is_a_tty && (TTY_set(fileno(tty_in), &tty_new) == -1)) {
        return 0;
    }
# else
    if (is_a_tty) {
        tty_new = tty_orig;
        tty_new &= ~ENABLE_ECHO_INPUT;
        SetConsoleMode(GetStdHandle(STD_INPUT_HANDLE), tty_new);
    }
# endif

    return 1;
}

static int openssl_console_echo_enable(void) {
# if !defined(OPENSSL_WINDOWS)
    OPENSSL_memcpy(&(tty_new), &(tty_orig), sizeof(tty_orig));
    if (is_a_tty && (TTY_set(fileno(tty_in), &tty_new) == -1)) {
        return 0;
    }
# else
    if (is_a_tty) {
        tty_new = tty_orig;
        SetConsoleMode(GetStdHandle(STD_INPUT_HANDLE), tty_new);
    }
# endif
    return 1;
}

int openssl_console_write(const char *str) {
    assert(CRYPTO_STATIC_MUTEX_is_write_locked(&console_global_mutex) == 1);
    if (fputs(str, tty_out) < 0 || fflush(tty_out) != 0) {
        return 0;
    }

    return 1;
}

// returns 0 on success, -1 on error, -2 if interrupt signal received
int openssl_console_read(char *buf, int minsize, int maxsize, int echo) {
    int ok = 0;
    char *p = NULL;
    int echo_eol = !echo;

    intr_signal = 0;
    int phase = 0;

    assert(CRYPTO_STATIC_MUTEX_is_write_locked(&console_global_mutex) == 1);

    pushsig();
    phase = 1;

    if (!echo && !openssl_console_echo_disable()) {
        goto error;
    }
    phase = 2;

    buf[0] = '\0';
#  if defined(OPENSSL_WINDOWS)
    if (is_a_tty) {
        DWORD numread;
        // for now assuming UTF-8....
        WCHAR wresult[BUFSIZ];

        if (ReadConsoleW(GetStdHandle(STD_INPUT_HANDLE),
                     wresult, maxsize, &numread, NULL)) {
            if (numread >= 2 && wresult[numread-2] == L'\r' &&
                wresult[numread-1] == L'\n') {
                wresult[numread-2] = L'\n';
                numread--;
            }
            wresult[numread] = '\0';
            if (WideCharToMultiByte(CP_UTF8, 0, wresult, -1, buf, maxsize + 1, NULL, 0) > 0) {
                p = buf;
            }
            OPENSSL_cleanse(wresult, sizeof(wresult));
        }
    } else
#  endif
    p = fgets(buf, maxsize, tty_in);
    if (p == NULL || feof(tty_in) || ferror(tty_in)) {
      ok = -1;
      goto error;
    }

    // check if we see a new line, otherwise clear out remaining input buffer
    if ((p = strchr(buf, '\n')) != NULL) {
        *p = '\0';
    } else if (!discard_line_remainder(tty_in)) {
        ok = -1;
        goto error;
    }

    // Validate input length meets minimum requirement
    size_t input_len = strlen(buf);
    if (input_len < (size_t)minsize) {
        ok = -1;
    }

error:
    if (intr_signal == SIGINT) {
        ok = -2; // interrupted
    }
    if (echo_eol) {
        fprintf(tty_out, "\n");
    }
    if (phase >= 2 && !echo && !openssl_console_echo_enable()) {
        ok = -1; // general errors
    }
    if (phase >= 1) {
        popsig();
    }

    return ok;
}
