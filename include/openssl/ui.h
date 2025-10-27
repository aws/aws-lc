// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef UI_H
#define UI_H

struct ui_st {
  // EMPTY
};

struct ui_method_st {
  // EMPTY
};

typedef struct ui_st UI;
typedef struct ui_method_st UI_METHOD;

UI *UI_new(void);
void UI_free(UI *ui);

int UI_add_input_string(UI *ui, const char *prompt, int flags,
        char *result_buf, int minsize, int maxsize);
int UI_add_verify_string(UI *ui, const char *prompt, int flags,
        char *result_buf, int minsize, int maxsize, const char *test_buf);
int UI_add_info_string(UI *ui, const char *text);

int UI_process(UI *ui);

#endif //UI_H

// Intentionally empty.

// Prevent compiler fall-through picking up "openssl/ui.h" from the system path.
