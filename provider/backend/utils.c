// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/bn.h>
#include <openssl/digest.h>
#include <openssl/mem.h>

#include <pthread.h>
#include <string.h>

#include "backend/utils.h"
#include "boundary/names.h"
#include "boundary/utils.h"

void *awslc_prov_bn_from_bytes(const AWSLC_PROV_BN_BYTES *in) {
  if (in == NULL || in->data == NULL) {
    return NULL;
  }
  if (in->is_signed && in->len > 0) {
#if defined(OPENSSL_BIG_ENDIAN)
    const unsigned char most_significant = in->data[0];
#else
    const unsigned char most_significant = in->data[in->len - 1];
#endif
    if ((most_significant & 0x80) != 0) {
      return NULL;
    }
  }
#if defined(OPENSSL_BIG_ENDIAN)
  return BN_bin2bn(in->data, in->len, NULL);
#else
  return BN_le2bn(in->data, in->len, NULL);
#endif
}

int awslc_prov_bn_to_bytes(const void *bn, int is_signed, unsigned char *out,
                           size_t out_size, size_t *out_len) {
  const BIGNUM *value = (const BIGNUM *)bn;
  size_t required = 0;

  if (value == NULL || out_len == NULL || BN_is_negative(value)) {
    return 0;
  }
  // A signed encoding needs room for a clear sign bit, and zero still takes a
  // byte.
  required = BN_num_bytes(value) + (is_signed ? 1 : 0);
  if (required == 0) {
    required = 1;
  }
  *out_len = required;
  if (out == NULL) {
    return 1;
  }
  if (out_size < required) {
    return 0;
  }
#if defined(OPENSSL_BIG_ENDIAN)
  if (!BN_bn2bin_padded(out, out_size, value)) {
    return 0;
  }
#else
  if (!BN_bn2le_padded(out, out_size, value)) {
    return 0;
  }
#endif
  *out_len = out_size;
  return 1;
}

int awslc_prov_bn_equal(const void *a, const void *b) {
  return a != NULL && b != NULL &&
         BN_cmp((const BIGNUM *)a, (const BIGNUM *)b) == 0;
}

// Name resolution for every AWS-LC digest.
static const struct {
  const char *names;
  const EVP_MD *(*md)(void);
} awslc_prov_digest_names[] = {
    {AWSLC_PROV_NAMES_MD4, EVP_md4},
    {AWSLC_PROV_NAMES_MD5, EVP_md5},
    {AWSLC_PROV_NAMES_MD5_SHA1, EVP_md5_sha1},
    {AWSLC_PROV_NAMES_RIPEMD_160, EVP_ripemd160},
    {AWSLC_PROV_NAMES_SHA1, EVP_sha1},
    {AWSLC_PROV_NAMES_SHA2_224, EVP_sha224},
    {AWSLC_PROV_NAMES_SHA2_256, EVP_sha256},
    {AWSLC_PROV_NAMES_SHA2_384, EVP_sha384},
    {AWSLC_PROV_NAMES_SHA2_512, EVP_sha512},
    {AWSLC_PROV_NAMES_SHA2_512_224, EVP_sha512_224},
    {AWSLC_PROV_NAMES_SHA2_512_256, EVP_sha512_256},
    {AWSLC_PROV_NAMES_SHA3_224, EVP_sha3_224},
    {AWSLC_PROV_NAMES_SHA3_256, EVP_sha3_256},
    {AWSLC_PROV_NAMES_SHA3_384, EVP_sha3_384},
    {AWSLC_PROV_NAMES_SHA3_512, EVP_sha3_512},
    {AWSLC_PROV_NAMES_SHAKE_128, EVP_shake128},
    {AWSLC_PROV_NAMES_SHAKE_256, EVP_shake256},
    {AWSLC_PROV_NAMES_KECCAK_256, EVP_keccak256},
};

#define AWSLC_PROV_DIGEST_NAME_COUNT \
  (sizeof(awslc_prov_digest_names) / sizeof(awslc_prov_digest_names[0]))

// Room for the longest canonical name in the table and its NUL.
#define AWSLC_PROV_DIGEST_CANONICAL_SIZE 16

// Each row's first alias, NULL-terminated. Read only after
// awslc_prov_digest_canonical_once; a row whose alias does not fit stays empty.
static char awslc_prov_digest_canonical[AWSLC_PROV_DIGEST_NAME_COUNT]
                                       [AWSLC_PROV_DIGEST_CANONICAL_SIZE];
static pthread_once_t awslc_prov_digest_canonical_once = PTHREAD_ONCE_INIT;

static void awslc_prov_digest_canonical_init(void) {
  for (size_t i = 0; i < AWSLC_PROV_DIGEST_NAME_COUNT; i++) {
    const char *names = awslc_prov_digest_names[i].names;
    const size_t len = strcspn(names, ":");

    if (len < AWSLC_PROV_DIGEST_CANONICAL_SIZE) {
      memcpy(awslc_prov_digest_canonical[i], names, len);
      awslc_prov_digest_canonical[i][len] = '\0';
    }
  }
}

static int awslc_prov_names_contain(const char *names, const char *name) {
  const size_t len = strlen(name);

  for (const char *alias = names; alias != NULL;) {
    const char *end = strchr(alias, ':');
    const size_t alias_len =
        end == NULL ? strlen(alias) : (size_t)(end - alias);

    if (alias_len == len && OPENSSL_strncasecmp(alias, name, len) == 0) {
      return 1;
    }
    alias = end == NULL ? NULL : end + 1;
  }
  return 0;
}

static size_t awslc_prov_digest_index(const char *name) {
  if (name != NULL) {
    for (size_t i = 0; i < AWSLC_PROV_DIGEST_NAME_COUNT; i++) {
      if (awslc_prov_names_contain(awslc_prov_digest_names[i].names, name)) {
        return i;
      }
    }
  }
  return AWSLC_PROV_DIGEST_NAME_COUNT;
}

const EVP_MD *awslc_prov_digest_md(const char *name) {
  const size_t i = awslc_prov_digest_index(name);

  return i < AWSLC_PROV_DIGEST_NAME_COUNT ? awslc_prov_digest_names[i].md()
                                          : NULL;
}

const char *awslc_prov_digest_canonical_name(const char *name) {
  const size_t i = awslc_prov_digest_index(name);

  if (i == AWSLC_PROV_DIGEST_NAME_COUNT ||
      pthread_once(&awslc_prov_digest_canonical_once,
                   awslc_prov_digest_canonical_init) != 0 ||
      awslc_prov_digest_canonical[i][0] == '\0') {
    return NULL;
  }
  return awslc_prov_digest_canonical[i];
}
