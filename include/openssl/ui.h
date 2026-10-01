// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef UI_H
#define UI_H

#include "openssl/base.h"

#if defined(__cplusplus)
extern "C" {
#endif

// UI compatibility stubs.
//
// AWS-LC does not support OpenSSL's UI APIs. These functions are provided so
// that code using them, such as passphrase shims copied from OpenSSL's
// applications, compiles. No user interaction is performed and every operation
// fails.
//
// Unlike OpenSSL, these types are declared only in this header, not in
// |base.h|. Some consumers, such as pyca/cryptography, declare their own
// |UI_METHOD| when building against AWS-LC without including this header, so
// declaring it in a widely-included header would break them.

struct ui_st {
  char _unused;
};

struct ui_method_st {
  char _unused;
};

typedef struct ui_st UI;
typedef struct ui_method_st UI_METHOD;
typedef struct ui_string_st UI_STRING;

// UI_new does nothing, always returns NULL.
OPENSSL_EXPORT OPENSSL_DEPRECATED UI *UI_new(void);

// UI_free invokes OPENSSL_free on its parameter.
OPENSSL_EXPORT OPENSSL_DEPRECATED void UI_free(UI *ui);

// UI_add_input_string does nothing, always returns -1 for failure.
OPENSSL_EXPORT OPENSSL_DEPRECATED int UI_add_input_string(UI *ui, const char *prompt, int flags,
        char *result_buf, int minsize, int maxsize);

// UI_add_verify_string does nothing, always returns -1 for failure.
OPENSSL_EXPORT OPENSSL_DEPRECATED int UI_add_verify_string(UI *ui, const char *prompt, int flags,
        char *result_buf, int minsize, int maxsize, const char *test_buf);

// UI_add_info_string does nothing, always returns -1 for failure.
OPENSSL_EXPORT OPENSSL_DEPRECATED int UI_add_info_string(UI *ui, const char *text);

// UI_process does nothing, always returns -1 for failure.
OPENSSL_EXPORT OPENSSL_DEPRECATED int UI_process(UI *ui);

// UI_OpenSSL returns a non-NULL pointer to a static dummy |UI_METHOD|. It is
// not a functioning console UI: the callbacks returned by the
// |UI_method_get_*| functions for it always fail.
OPENSSL_EXPORT OPENSSL_DEPRECATED UI_METHOD *UI_OpenSSL(void);

// UI_create_method ignores |name| and returns NULL. No memory is allocated.
OPENSSL_EXPORT OPENSSL_DEPRECATED UI_METHOD *UI_create_method(const char *name);

// UI_destroy_method does nothing. |ui_method| may be NULL or the result of
// |UI_OpenSSL|.
OPENSSL_EXPORT OPENSSL_DEPRECATED void UI_destroy_method(UI_METHOD *ui_method);

// UI_method_set_opener, |UI_method_set_writer|, |UI_method_set_reader|, and
// |UI_method_set_closer| ignore their arguments, which may be NULL, and return
// -1 for failure. The callback is neither stored nor invoked.
OPENSSL_EXPORT OPENSSL_DEPRECATED int UI_method_set_opener(
    UI_METHOD *method, int (*opener)(UI *ui));
OPENSSL_EXPORT OPENSSL_DEPRECATED int UI_method_set_writer(
    UI_METHOD *method, int (*writer)(UI *ui, UI_STRING *uis));
OPENSSL_EXPORT OPENSSL_DEPRECATED int UI_method_set_reader(
    UI_METHOD *method, int (*reader)(UI *ui, UI_STRING *uis));
OPENSSL_EXPORT OPENSSL_DEPRECATED int UI_method_set_closer(
    UI_METHOD *method, int (*closer)(UI *ui));

// UI_method_get_opener, |UI_method_get_writer|, |UI_method_get_reader|, and
// |UI_method_get_closer| ignore |method|, which may be NULL, and return a
// non-NULL callback. The callback ignores its arguments, which may be NULL, and
// returns zero for failure.
OPENSSL_EXPORT OPENSSL_DEPRECATED int (
    *UI_method_get_opener(const UI_METHOD *method))(UI *);
OPENSSL_EXPORT OPENSSL_DEPRECATED int (
    *UI_method_get_writer(const UI_METHOD *method))(UI *, UI_STRING *);
OPENSSL_EXPORT OPENSSL_DEPRECATED int (
    *UI_method_get_reader(const UI_METHOD *method))(UI *, UI_STRING *);
OPENSSL_EXPORT OPENSSL_DEPRECATED int (
    *UI_method_get_closer(const UI_METHOD *method))(UI *);

#if defined(__cplusplus)
}  // extern C
#endif

#endif //UI_H
