/*
 * Copyright 1995-2017 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the Apache License 2.0 (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

#ifndef TOOL_OPENSSL_TXT_DB_H
#define TOOL_OPENSSL_TXT_DB_H

#include <openssl/bio.h>
#include <openssl/lhash.h>
#include <openssl/opensslconf.h>
#include <openssl/stack.h>

#include "../crypto/lhash/internal.h"

#define DB_ERROR_OK 0
#define DB_ERROR_MALLOC 1
#define DB_ERROR_INDEX_CLASH 2
#define DB_ERROR_INDEX_OUT_OF_RANGE 3
#define DB_ERROR_NO_INDEX 4
#define DB_ERROR_INSERT_INDEX_CLASH 5
#define DB_ERROR_WRONG_NUM_FIELDS 6

DEFINE_LHASH_OF(OPENSSL_STRING);

DEFINE_NAMED_STACK_OF(OPENSSL_PSTRING, OPENSSL_STRING);

typedef struct txt_db_st TXT_DB;

struct txt_db_st {
  int num_fields;
  STACK_OF(OPENSSL_PSTRING) *data;
  LHASH_OF(OPENSSL_STRING) **index;
  int (**qual)(OPENSSL_STRING *);
  long error;
  long arg1;
  long arg2;
  OPENSSL_STRING *arg_row;
};

bssl::UniquePtr<TXT_DB> TXT_DB_read(bssl::UniquePtr<BIO> &in, int num);
void TXT_DB_free(TXT_DB *db);
long TXT_DB_write(bssl::UniquePtr<BIO> &out, bssl::UniquePtr<TXT_DB> &db);
int TXT_DB_create_index(bssl::UniquePtr<TXT_DB> &db, int field,
                        int (*qual)(OPENSSL_STRING *),
                        lhash_OPENSSL_STRING_hash_func hash,
                        lhash_OPENSSL_STRING_cmp_func cmp);
OPENSSL_STRING *TXT_DB_get_by_index(bssl::UniquePtr<TXT_DB> &db, int idx,
                                    OPENSSL_STRING *value);
int TXT_DB_insert(bssl::UniquePtr<TXT_DB> &db, OPENSSL_STRING *value);

BSSL_NAMESPACE_BEGIN

BORINGSSL_MAKE_DELETER(TXT_DB, TXT_DB_free);
BORINGSSL_MAKE_DELETER(LHASH_OF(OPENSSL_STRING), lh_OPENSSL_STRING_free);

BSSL_NAMESPACE_END

#endif
