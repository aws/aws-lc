// Copyright (c) 2014, Google Inc.
// SPDX-License-Identifier: ISC

/* This header is provided in order to make compiling against code that expects
   OpenSSL easier. */

#include "pkcs8.h"

// Microsoft key usage constants.
#define KEY_EX 0x10
#define KEY_SIG 0x80
