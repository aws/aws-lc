// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// AWS-LC does not support the UI APIs. These functions always fail at runtime.
// This file provides no-op implementations of several UI functions that return
// failure when called. This allows compilation to succeed for projects that use
// these functions for non-essential operations.

#include "openssl/ui.h"
#include "openssl/mem.h"

UI *UI_new(void) {
  return NULL;
}

void UI_free(UI *ui) {
  OPENSSL_free(ui);
}

int UI_add_input_string(UI *ui, const char *prompt, int flags,
        char *result_buf, int minsize, int maxsize) {
  return -1;
}
int UI_add_verify_string(UI *ui, const char *prompt, int flags,
        char *result_buf, int minsize, int maxsize, const char *test_buf) {
  return -1;
}

int UI_add_info_string(UI *ui, const char *text) {
  return -1;
}

int UI_process(UI *ui) {
  return -1;
}

UI_METHOD *UI_OpenSSL(void) {
  static UI_METHOD method = {0};
  return &method;
}

UI_METHOD *UI_create_method(const char *name) { return NULL; }

void UI_destroy_method(UI_METHOD *ui_method) {}

int UI_method_set_opener(UI_METHOD *method, int (*opener)(UI *ui)) {
  return -1;
}

int UI_method_set_writer(UI_METHOD *method,
                         int (*writer)(UI *ui, UI_STRING *uis)) {
  return -1;
}

int UI_method_set_reader(UI_METHOD *method,
                         int (*reader)(UI *ui, UI_STRING *uis)) {
  return -1;
}

int UI_method_set_closer(UI_METHOD *method, int (*closer)(UI *ui)) {
  return -1;
}

static int ui_session_stub(UI *ui) { return 0; }

static int ui_string_stub(UI *ui, UI_STRING *uis) { return 0; }

int (*UI_method_get_opener(const UI_METHOD *method))(UI *) {
  return ui_session_stub;
}

int (*UI_method_get_writer(const UI_METHOD *method))(UI *, UI_STRING *) {
  return ui_string_stub;
}

int (*UI_method_get_reader(const UI_METHOD *method))(UI *, UI_STRING *) {
  return ui_string_stub;
}

int (*UI_method_get_closer(const UI_METHOD *method))(UI *) {
  return ui_session_stub;
}
