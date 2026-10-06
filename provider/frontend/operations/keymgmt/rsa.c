// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Front side: the RSA key manager's dispatch slots. Selection handling follows
// OpenSSL's default RSA key manager.

#include <openssl/core_dispatch.h>
#include <openssl/core_names.h>
#include <openssl/params.h>

#include "internal/backend.h"
#include "internal/backend/keymgmt.h"
#include "internal/frontend/keymgmt.h"
#include "internal/provider.h"

#define AWSLC_PROV_RSA_NAME "RSA"
// The digest a signer uses when the caller names none, such as certificates
// and CMS signed without -digest. SHA-256 is aligned with the OpenSSL default.
#define AWSLC_PROV_RSA_DEFAULT_DIGEST "SHA256"
// OTHER_PARAMETERS is non-key metadata, such as RSA-PSS limits.
#define AWSLC_PROV_RSA_POSSIBLE_SELECTIONS \
  (OSSL_KEYMGMT_SELECT_KEYPAIR | OSSL_KEYMGMT_SELECT_OTHER_PARAMETERS)

#define AWSLC_PROV_RSA_DEFAULT_BITS 2048
#define AWSLC_PROV_RSA_PRIMES 2
#define AWSLC_PROV_RSA_PUBLIC_EXPONENT 65537

typedef struct {
  AWSLC_PROV_CTX *provctx;
  // NULL until an import or generation fills it.
  void *rsa;
} AWSLC_PROV_RSA_KEY;

typedef struct {
  AWSLC_PROV_CTX *provctx;
  unsigned bits;
  int fips_approved;
} AWSLC_PROV_RSA_GEN_CTX;

static const char *const
    awslc_prov_rsa_component_keys[AWSLC_PROV_RSA_COMPONENT_COUNT] = {
        [AWSLC_PROV_RSA_N] = OSSL_PKEY_PARAM_RSA_N,
        [AWSLC_PROV_RSA_E] = OSSL_PKEY_PARAM_RSA_E,
        [AWSLC_PROV_RSA_D] = OSSL_PKEY_PARAM_RSA_D,
        [AWSLC_PROV_RSA_P] = OSSL_PKEY_PARAM_RSA_FACTOR1,
        [AWSLC_PROV_RSA_Q] = OSSL_PKEY_PARAM_RSA_FACTOR2,
        [AWSLC_PROV_RSA_DMP1] = OSSL_PKEY_PARAM_RSA_EXPONENT1,
        [AWSLC_PROV_RSA_DMQ1] = OSSL_PKEY_PARAM_RSA_EXPONENT2,
        [AWSLC_PROV_RSA_IQMP] = OSSL_PKEY_PARAM_RSA_COEFFICIENT1,
};

// Multi-prime components, which AWS-LC cannot represent.
static const char *const awslc_prov_rsa_multi_prime_keys[] = {
    OSSL_PKEY_PARAM_RSA_FACTOR3,      OSSL_PKEY_PARAM_RSA_FACTOR4,
    OSSL_PKEY_PARAM_RSA_FACTOR5,      OSSL_PKEY_PARAM_RSA_FACTOR6,
    OSSL_PKEY_PARAM_RSA_FACTOR7,      OSSL_PKEY_PARAM_RSA_FACTOR8,
    OSSL_PKEY_PARAM_RSA_FACTOR9,      OSSL_PKEY_PARAM_RSA_FACTOR10,
    OSSL_PKEY_PARAM_RSA_EXPONENT3,    OSSL_PKEY_PARAM_RSA_EXPONENT4,
    OSSL_PKEY_PARAM_RSA_EXPONENT5,    OSSL_PKEY_PARAM_RSA_EXPONENT6,
    OSSL_PKEY_PARAM_RSA_EXPONENT7,    OSSL_PKEY_PARAM_RSA_EXPONENT8,
    OSSL_PKEY_PARAM_RSA_EXPONENT9,    OSSL_PKEY_PARAM_RSA_EXPONENT10,
    OSSL_PKEY_PARAM_RSA_COEFFICIENT2, OSSL_PKEY_PARAM_RSA_COEFFICIENT3,
    OSSL_PKEY_PARAM_RSA_COEFFICIENT4, OSSL_PKEY_PARAM_RSA_COEFFICIENT5,
    OSSL_PKEY_PARAM_RSA_COEFFICIENT6, OSSL_PKEY_PARAM_RSA_COEFFICIENT7,
    OSSL_PKEY_PARAM_RSA_COEFFICIENT8, OSSL_PKEY_PARAM_RSA_COEFFICIENT9,
    NULL,
};

#define AWSLC_PROV_RSA_KEY_TYPES                             \
  OSSL_PARAM_BN(OSSL_PKEY_PARAM_RSA_N, NULL, 0),             \
      OSSL_PARAM_BN(OSSL_PKEY_PARAM_RSA_E, NULL, 0),         \
      OSSL_PARAM_BN(OSSL_PKEY_PARAM_RSA_D, NULL, 0),         \
      OSSL_PARAM_BN(OSSL_PKEY_PARAM_RSA_FACTOR1, NULL, 0),   \
      OSSL_PARAM_BN(OSSL_PKEY_PARAM_RSA_FACTOR2, NULL, 0),   \
      OSSL_PARAM_BN(OSSL_PKEY_PARAM_RSA_EXPONENT1, NULL, 0), \
      OSSL_PARAM_BN(OSSL_PKEY_PARAM_RSA_EXPONENT2, NULL, 0), \
      OSSL_PARAM_BN(OSSL_PKEY_PARAM_RSA_COEFFICIENT1, NULL, 0)

static const OSSL_PARAM awslc_prov_rsa_key_types[] = {AWSLC_PROV_RSA_KEY_TYPES,
                                                      OSSL_PARAM_END};

static const OSSL_PARAM awslc_prov_rsa_gettable[] = {
    OSSL_PARAM_int(OSSL_PKEY_PARAM_BITS, NULL),
    OSSL_PARAM_int(OSSL_PKEY_PARAM_SECURITY_BITS, NULL),
    OSSL_PARAM_int(OSSL_PKEY_PARAM_MAX_SIZE, NULL),
    OSSL_PARAM_utf8_string(OSSL_PKEY_PARAM_DEFAULT_DIGEST, NULL, 0),
    AWSLC_PROV_RSA_KEY_TYPES,
    OSSL_PARAM_END};

static const OSSL_PARAM awslc_prov_rsa_gen_settable[] = {
    OSSL_PARAM_size_t(OSSL_PKEY_PARAM_RSA_BITS, NULL),
    OSSL_PARAM_size_t(OSSL_PKEY_PARAM_RSA_PRIMES, NULL),
    OSSL_PARAM_BN(OSSL_PKEY_PARAM_RSA_E, NULL, 0),
    OSSL_PARAM_END};

static const OSSL_PARAM awslc_prov_rsa_gen_gettable[] = {
    OSSL_PARAM_int(OSSL_PKEY_PARAM_FIPS_APPROVED_INDICATOR, NULL),
    OSSL_PARAM_END};

static OSSL_FUNC_keymgmt_new_fn awslc_prov_rsa_newdata;
static OSSL_FUNC_keymgmt_free_fn awslc_prov_rsa_freedata;
static OSSL_FUNC_keymgmt_has_fn awslc_prov_rsa_has;
static OSSL_FUNC_keymgmt_match_fn awslc_prov_rsa_match;
static OSSL_FUNC_keymgmt_validate_fn awslc_prov_rsa_validate;
static OSSL_FUNC_keymgmt_import_fn awslc_prov_rsa_import;
static OSSL_FUNC_keymgmt_import_types_fn awslc_prov_rsa_import_types;
static OSSL_FUNC_keymgmt_export_fn awslc_prov_rsa_export;
static OSSL_FUNC_keymgmt_export_types_fn awslc_prov_rsa_export_types;
static OSSL_FUNC_keymgmt_get_params_fn awslc_prov_rsa_get_params;
static OSSL_FUNC_keymgmt_gettable_params_fn awslc_prov_rsa_gettable_params;
static OSSL_FUNC_keymgmt_dup_fn awslc_prov_rsa_dup;
static OSSL_FUNC_keymgmt_gen_init_fn awslc_prov_rsa_gen_init;
static OSSL_FUNC_keymgmt_gen_set_params_fn awslc_prov_rsa_gen_set_params;
static OSSL_FUNC_keymgmt_gen_settable_params_fn
    awslc_prov_rsa_gen_settable_params;
static OSSL_FUNC_keymgmt_gen_get_params_fn awslc_prov_rsa_gen_get_params;
static OSSL_FUNC_keymgmt_gen_gettable_params_fn
    awslc_prov_rsa_gen_gettable_params;
static OSSL_FUNC_keymgmt_gen_fn awslc_prov_rsa_gen;
static OSSL_FUNC_keymgmt_gen_cleanup_fn awslc_prov_rsa_gen_cleanup;

static AWSLC_PROV_RSA_KEY *awslc_prov_rsa_key_new(AWSLC_PROV_CTX *provctx) {
  AWSLC_PROV_RSA_KEY *key = NULL;

  awslc_prov_error_mark();
  key = awslc_prov_zalloc(sizeof(*key));
  if (!AWSLC_PROV_ERROR_SETTLE(provctx, key != NULL, AWSLC_PROV_R_BACKEND_ERROR,
                               AWSLC_PROV_RSA_NAME)) {
    return NULL;
  }
  key->provctx = provctx;
  return key;
}

static void *awslc_prov_rsa_newdata(void *provctx) {
  return awslc_prov_rsa_key_new((AWSLC_PROV_CTX *)provctx);
}

static void awslc_prov_rsa_freedata(void *keydata) {
  AWSLC_PROV_RSA_KEY *key = (AWSLC_PROV_RSA_KEY *)keydata;

  if (key == NULL) {
    return;
  }
  awslc_prov_rsa_free(key->rsa);
  awslc_prov_clear_free(key, sizeof(*key));
}

static const void *awslc_prov_rsa_component(const AWSLC_PROV_RSA_KEY *key,
                                            AWSLC_PROV_RSA_COMPONENT c) {
  return awslc_prov_rsa_get0(key->rsa, c);
}

static int awslc_prov_rsa_has(const void *keydata, int selection) {
  const AWSLC_PROV_RSA_KEY *key = (const AWSLC_PROV_RSA_KEY *)keydata;
  int ok = 1;

  if (key == NULL) {
    return 0;
  }
  if ((selection & AWSLC_PROV_RSA_POSSIBLE_SELECTIONS) == 0) {
    return 1;
  }
  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) != 0) {
    ok = ok && awslc_prov_rsa_component(key, AWSLC_PROV_RSA_N) != NULL;
  }
  if ((selection & OSSL_KEYMGMT_SELECT_PUBLIC_KEY) != 0) {
    ok = ok && awslc_prov_rsa_component(key, AWSLC_PROV_RSA_E) != NULL;
  }
  if ((selection & OSSL_KEYMGMT_SELECT_PRIVATE_KEY) != 0) {
    ok = ok && awslc_prov_rsa_component(key, AWSLC_PROV_RSA_D) != NULL;
  }
  return ok;
}

static int awslc_prov_rsa_match(const void *keydata1, const void *keydata2,
                                int selection) {
  const AWSLC_PROV_RSA_KEY *key1 = (const AWSLC_PROV_RSA_KEY *)keydata1;
  const AWSLC_PROV_RSA_KEY *key2 = (const AWSLC_PROV_RSA_KEY *)keydata2;
  const void *e1 = NULL;
  const void *e2 = NULL;
  int ok = 1;

  if (key1 == NULL || key2 == NULL) {
    return 0;
  }
  // e is compared whatever the selection, and two keys without one agree.
  e1 = awslc_prov_rsa_component(key1, AWSLC_PROV_RSA_E);
  e2 = awslc_prov_rsa_component(key2, AWSLC_PROV_RSA_E);
  ok = (e1 == NULL && e2 == NULL) || awslc_prov_bn_equal(e1, e2);

  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) != 0) {
    const AWSLC_PROV_RSA_COMPONENT compare_component =
        (selection & OSSL_KEYMGMT_SELECT_PUBLIC_KEY) != 0 ? AWSLC_PROV_RSA_N
                                                          : AWSLC_PROV_RSA_D;

    ok = ok && awslc_prov_bn_equal(awslc_prov_rsa_component(key1, compare_component),
                                   awslc_prov_rsa_component(key2, compare_component));
  }
  return ok;
}

static int awslc_prov_rsa_validate(const void *keydata, int selection,
                                   int checktype) {
  const AWSLC_PROV_RSA_KEY *key = (const AWSLC_PROV_RSA_KEY *)keydata;

  (void)checktype;
  if (key == NULL) {
    return 0;
  }
  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) == 0) {
    return 1;
  }
  if ((selection & OSSL_KEYMGMT_SELECT_PRIVATE_KEY) != 0 &&
      awslc_prov_rsa_component(key, AWSLC_PROV_RSA_D) == NULL) {
    AWSLC_PROV_ERROR_RAISE(key->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           OSSL_PKEY_PARAM_RSA_D);
    return 0;
  }

  awslc_prov_error_mark();
  int ok = awslc_prov_rsa_check(key->rsa);
  return AWSLC_PROV_ERROR_SETTLE(key->provctx, ok, AWSLC_PROV_R_BACKEND_ERROR,
                                 AWSLC_PROV_RSA_NAME);
}

// Fill |components| from |params|, refusing key shapes AWS-LC cannot
// represent.
static int awslc_prov_rsa_read_components(
    const AWSLC_PROV_CTX *provctx, const OSSL_PARAM params[],
    int include_private,
    AWSLC_PROV_BN_BYTES components[AWSLC_PROV_RSA_COMPONENT_COUNT]) {
  const OSSL_PARAM *p = NULL;
  int derive = 0;
  int crt = 0;

  for (int c = 0; c < AWSLC_PROV_RSA_COMPONENT_COUNT; c++) {
    components[c].data = NULL;
  }
  if (!awslc_prov_keymgmt_get_bn(provctx, params, OSSL_PKEY_PARAM_RSA_N,
                                 &components[AWSLC_PROV_RSA_N]) ||
      !awslc_prov_keymgmt_get_bn(provctx, params, OSSL_PKEY_PARAM_RSA_E,
                                 &components[AWSLC_PROV_RSA_E])) {
    return 0;
  }
  if (components[AWSLC_PROV_RSA_N].data == NULL ||
      components[AWSLC_PROV_RSA_E].data == NULL) {
    AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_NAME);
    return 0;
  }
  if (!include_private) {
    return 1;
  }
  if (!awslc_prov_keymgmt_get_bn(provctx, params, OSSL_PKEY_PARAM_RSA_D,
                                 &components[AWSLC_PROV_RSA_D])) {
    return 0;
  }
  // OpenSSL callers indicate "keypair" in their selection bits as a shorthand
  // for keep the "private key if it's there" not as a requirement to return both.
  if (components[AWSLC_PROV_RSA_D].data == NULL) {
    return 1;
  }

  // Reject any multi-prime RSA keys which AWS-LC does not support
  for (const char *const *name = awslc_prov_rsa_multi_prime_keys;
       *name != NULL; name++) {
    if (OSSL_PARAM_locate_const(params, *name) != NULL) {
      AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER, *name);
      return 0;
    }
  }

  for (int c = AWSLC_PROV_RSA_P; c < AWSLC_PROV_RSA_COMPONENT_COUNT; c++) {
    if (!awslc_prov_keymgmt_get_bn(provctx, params,
                                   awslc_prov_rsa_component_keys[c],
                                   &components[c])) {
      return 0;
    }
    crt += components[c].data != NULL;
  }
  // Deriving the CRT values from p and q matters only when they are missing.
  p = OSSL_PARAM_locate_const(params, OSSL_PKEY_PARAM_RSA_DERIVE_FROM_PQ);
  if (p != NULL && (!OSSL_PARAM_get_int(p, &derive) ||
                    (derive != 0 && crt != AWSLC_PROV_RSA_CRT_COUNT))) {
    AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           OSSL_PKEY_PARAM_RSA_DERIVE_FROM_PQ);
    return 0;
  }
  if (crt != 0 && crt != AWSLC_PROV_RSA_CRT_COUNT) {
    AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_NAME);
    return 0;
  }
  return 1;
}

static int awslc_prov_rsa_import(void *keydata, int selection,
                                 const OSSL_PARAM params[]) {
  AWSLC_PROV_RSA_KEY *key = (AWSLC_PROV_RSA_KEY *)keydata;
  AWSLC_PROV_BN_BYTES components[AWSLC_PROV_RSA_COMPONENT_COUNT];
  void *rsa = NULL;

  if (key == NULL) {
    return 0;
  }
  // OSSL_KEYMGMT_SELECT_OTHER_PARAMETERS carries nothing for a plain RSA key.
  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) == 0) {
    AWSLC_PROV_ERROR_RAISE(key->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_NAME);
    return 0;
  }
  if (!awslc_prov_rsa_read_components(
          key->provctx, params,
          (selection & OSSL_KEYMGMT_SELECT_PRIVATE_KEY) != 0, components)) {
    return 0;
  }

  awslc_prov_error_mark();
  rsa = awslc_prov_rsa_new(components);
  if (!AWSLC_PROV_ERROR_SETTLE(key->provctx, rsa != NULL,
                               AWSLC_PROV_R_BACKEND_ERROR,
                               AWSLC_PROV_RSA_NAME)) {
    return 0;
  }
  awslc_prov_rsa_free(key->rsa);
  key->rsa = rsa;
  return 1;
}

static const OSSL_PARAM *awslc_prov_rsa_import_types(int selection) {
  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) != 0) {
    return awslc_prov_rsa_key_types;
  }
  return NULL;
}

static int awslc_prov_rsa_export(void *keydata, int selection,
                                 OSSL_CALLBACK *callback, void *cbarg) {
  const AWSLC_PROV_RSA_KEY *key = (const AWSLC_PROV_RSA_KEY *)keydata;
  AWSLC_PROV_KEYMGMT_BN bns[AWSLC_PROV_RSA_COMPONENT_COUNT];
  size_t count = 0;

  if (key == NULL) {
    return 0;
  }
  if ((selection & AWSLC_PROV_RSA_POSSIBLE_SELECTIONS) == 0 ||
      key->rsa == NULL || callback == NULL) {
    AWSLC_PROV_ERROR_RAISE(key->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_NAME);
    return 0;
  }
  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) != 0) {
    const int last = (selection & OSSL_KEYMGMT_SELECT_PRIVATE_KEY) != 0
                         ? AWSLC_PROV_RSA_COMPONENT_COUNT
                         : AWSLC_PROV_RSA_D;

    for (int c = AWSLC_PROV_RSA_N; c < last; c++) {
      const void *bn = awslc_prov_rsa_component(key, c);

      if (bn != NULL) {
        bns[count].key = awslc_prov_rsa_component_keys[c];
        bns[count].bn = bn;
        count++;
      }
    }
  }

  OSSL_PARAM params[AWSLC_PROV_RSA_COMPONENT_COUNT + 1];
  unsigned char *buffer = NULL;
  size_t size = 0;
  int ok = awslc_prov_param_encode_bns(key->provctx, bns, count, params,
                                       &buffer, &size);

  params[count] = OSSL_PARAM_construct_end();
  ok = ok && callback(params, cbarg);
  awslc_prov_clear_free(buffer, size);
  return ok;
}

static const OSSL_PARAM *awslc_prov_rsa_export_types(int selection) {
  return awslc_prov_rsa_import_types(selection);
}

static int awslc_prov_rsa_get_params(void *keydata, OSSL_PARAM params[]) {
  const AWSLC_PROV_RSA_KEY *key = (const AWSLC_PROV_RSA_KEY *)keydata;

  if (key == NULL) {
    return 0;
  }
  if (key->rsa == NULL) {
    AWSLC_PROV_ERROR_RAISE(key->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_NAME);
    return 0;
  }
  if (!awslc_prov_param_set_int(key->provctx, params, OSSL_PKEY_PARAM_BITS,
                                (int)awslc_prov_rsa_bits(key->rsa)) ||
      !awslc_prov_param_set_int(key->provctx, params,
                                OSSL_PKEY_PARAM_SECURITY_BITS,
                                (int)awslc_prov_rsa_security_bits(key->rsa)) ||
      !awslc_prov_param_set_int(key->provctx, params, OSSL_PKEY_PARAM_MAX_SIZE,
                                (int)awslc_prov_rsa_size(key->rsa)) ||
      !awslc_prov_param_set_utf8_string(key->provctx, params,
                                        OSSL_PKEY_PARAM_DEFAULT_DIGEST,
                                        AWSLC_PROV_RSA_DEFAULT_DIGEST)) {
    return 0;
  }
  for (int c = AWSLC_PROV_RSA_N; c < AWSLC_PROV_RSA_COMPONENT_COUNT; c++) {
    const void *bn = awslc_prov_rsa_component(key, c);

    // A component the key lacks goes unanswered.
    if (bn == NULL) {
      continue;
    }
    if (!awslc_prov_param_set_bn(key->provctx, params,
                                 awslc_prov_rsa_component_keys[c], bn)) {
      return 0;
    }
  }
  return 1;
}

static const OSSL_PARAM *awslc_prov_rsa_gettable_params(void *provctx) {
  (void)provctx;
  return awslc_prov_rsa_gettable;
}

static void *awslc_prov_rsa_dup(const void *keydata, int selection) {
  const AWSLC_PROV_RSA_KEY *key = (const AWSLC_PROV_RSA_KEY *)keydata;
  AWSLC_PROV_RSA_KEY *duplicate = NULL;

  if (key == NULL) {
    return NULL;
  }
  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) == 0) {
    AWSLC_PROV_ERROR_RAISE(key->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_NAME);
    return NULL;
  }
  duplicate = awslc_prov_rsa_key_new(key->provctx);
  if (duplicate == NULL || key->rsa == NULL) {
    return duplicate;
  }

  awslc_prov_error_mark();
  // Keys are never mutated once built, so a private duplicate shares one.
  if ((selection & OSSL_KEYMGMT_SELECT_PRIVATE_KEY) != 0) {
    duplicate->rsa = awslc_prov_rsa_up_ref(key->rsa) ? key->rsa : NULL;
  } else {
    duplicate->rsa = awslc_prov_rsa_new_public(key->rsa);
  }
  if (!AWSLC_PROV_ERROR_SETTLE(key->provctx, duplicate->rsa != NULL,
                               AWSLC_PROV_R_BACKEND_ERROR,
                               AWSLC_PROV_RSA_NAME)) {
    awslc_prov_rsa_freedata(duplicate);
    return NULL;
  }
  return duplicate;
}

static int awslc_prov_rsa_gen_set_params(void *genctx,
                                         const OSSL_PARAM params[]) {
  AWSLC_PROV_RSA_GEN_CTX *gctx = (AWSLC_PROV_RSA_GEN_CTX *)genctx;
  const OSSL_PARAM *p = NULL;

  if (gctx == NULL) {
    return 0;
  }
  p = OSSL_PARAM_locate_const(params, OSSL_PKEY_PARAM_RSA_BITS);
  if (p != NULL) {
    unsigned bits = 0;

    if (!OSSL_PARAM_get_uint(p, &bits)) {
      AWSLC_PROV_ERROR_RAISE(gctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                             OSSL_PKEY_PARAM_RSA_BITS);
      return 0;
    }
    gctx->bits = bits;
  }

  p = OSSL_PARAM_locate_const(params, OSSL_PKEY_PARAM_RSA_PRIMES);
  if (p != NULL) {
    size_t primes = 0;

    if (!OSSL_PARAM_get_size_t(p, &primes) || primes != AWSLC_PROV_RSA_PRIMES) {
      AWSLC_PROV_ERROR_RAISE(gctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                             OSSL_PKEY_PARAM_RSA_PRIMES);
      return 0;
    }
  }

  // RSA_generate_key_fips takes no exponent and always uses 65537.
  p = OSSL_PARAM_locate_const(params, OSSL_PKEY_PARAM_RSA_E);
  if (p != NULL) {
    uint64_t e = 0;

    if ((p->data_type != OSSL_PARAM_UNSIGNED_INTEGER &&
         p->data_type != OSSL_PARAM_INTEGER) ||
        !OSSL_PARAM_get_uint64(p, &e) || e != AWSLC_PROV_RSA_PUBLIC_EXPONENT) {
      AWSLC_PROV_ERROR_RAISE(gctx->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                             OSSL_PKEY_PARAM_RSA_E);
      return 0;
    }
  }
  return 1;
}

static void awslc_prov_rsa_gen_cleanup(void *genctx) {
  AWSLC_PROV_RSA_GEN_CTX *gctx = (AWSLC_PROV_RSA_GEN_CTX *)genctx;

  if (gctx == NULL) {
    return;
  }
  awslc_prov_clear_free(gctx, sizeof(*gctx));
}

static void *awslc_prov_rsa_gen_init(void *provctx, int selection,
                                     const OSSL_PARAM params[]) {
  AWSLC_PROV_CTX *ctx = (AWSLC_PROV_CTX *)provctx;
  AWSLC_PROV_RSA_GEN_CTX *gctx = NULL;

  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) == 0) {
    AWSLC_PROV_ERROR_RAISE(ctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_NAME);
    return NULL;
  }
  awslc_prov_error_mark();
  gctx = awslc_prov_zalloc(sizeof(*gctx));
  if (!AWSLC_PROV_ERROR_SETTLE(ctx, gctx != NULL, AWSLC_PROV_R_BACKEND_ERROR,
                               AWSLC_PROV_RSA_NAME)) {
    return NULL;
  }
  gctx->provctx = ctx;
  gctx->bits = AWSLC_PROV_RSA_DEFAULT_BITS;
  gctx->fips_approved = awslc_prov_ctx_is_fips(ctx);
  if (!awslc_prov_rsa_gen_set_params(gctx, params)) {
    awslc_prov_rsa_gen_cleanup(gctx);
    return NULL;
  }
  return gctx;
}

static const OSSL_PARAM *awslc_prov_rsa_gen_settable_params(void *genctx,
                                                            void *provctx) {
  (void)genctx;
  (void)provctx;
  return awslc_prov_rsa_gen_settable;
}

static int awslc_prov_rsa_gen_get_params(void *genctx, OSSL_PARAM params[]) {
  const AWSLC_PROV_RSA_GEN_CTX *gctx = (const AWSLC_PROV_RSA_GEN_CTX *)genctx;

  if (gctx == NULL) {
    return 0;
  }
  return awslc_prov_param_set_int(gctx->provctx, params,
                                  OSSL_PKEY_PARAM_FIPS_APPROVED_INDICATOR,
                                  gctx->fips_approved);
}

static const OSSL_PARAM *awslc_prov_rsa_gen_gettable_params(void *genctx,
                                                            void *provctx) {
  (void)genctx;
  (void)provctx;
  return awslc_prov_rsa_gen_gettable;
}

static void *awslc_prov_rsa_gen(void *genctx, OSSL_CALLBACK *callback,
                                void *cbarg) {
  AWSLC_PROV_RSA_GEN_CTX *gctx = (AWSLC_PROV_RSA_GEN_CTX *)genctx;
  AWSLC_PROV_RSA_KEY *key = NULL;

  // This callback is used to report progress, we don't bother.
  (void)callback;
  (void)cbarg;
  if (gctx == NULL) {
    return NULL;
  }
  key = awslc_prov_rsa_key_new(gctx->provctx);
  if (key == NULL) {
    return NULL;
  }

  awslc_prov_error_mark();
  uint64_t before = awslc_prov_service_indicator_before_call();
  key->rsa = awslc_prov_rsa_generate(gctx->bits);
  gctx->fips_approved = awslc_prov_ctx_is_fips(gctx->provctx) &&
                        awslc_prov_service_indicator_after_call(before);
  if (!AWSLC_PROV_ERROR_SETTLE(gctx->provctx, key->rsa != NULL,
                               AWSLC_PROV_R_BACKEND_ERROR,
                               AWSLC_PROV_RSA_NAME)) {
    awslc_prov_rsa_freedata(key);
    return NULL;
  }
  return key;
}

const OSSL_DISPATCH awslc_prov_rsa_keymgmt_functions[] = {
    {OSSL_FUNC_KEYMGMT_NEW, (void (*)(void))awslc_prov_rsa_newdata},
    {OSSL_FUNC_KEYMGMT_FREE, (void (*)(void))awslc_prov_rsa_freedata},
    {OSSL_FUNC_KEYMGMT_HAS, (void (*)(void))awslc_prov_rsa_has},
    {OSSL_FUNC_KEYMGMT_MATCH, (void (*)(void))awslc_prov_rsa_match},
    {OSSL_FUNC_KEYMGMT_VALIDATE, (void (*)(void))awslc_prov_rsa_validate},
    {OSSL_FUNC_KEYMGMT_IMPORT, (void (*)(void))awslc_prov_rsa_import},
    {OSSL_FUNC_KEYMGMT_IMPORT_TYPES,
     (void (*)(void))awslc_prov_rsa_import_types},
    {OSSL_FUNC_KEYMGMT_EXPORT, (void (*)(void))awslc_prov_rsa_export},
    {OSSL_FUNC_KEYMGMT_EXPORT_TYPES,
     (void (*)(void))awslc_prov_rsa_export_types},
    {OSSL_FUNC_KEYMGMT_GET_PARAMS, (void (*)(void))awslc_prov_rsa_get_params},
    {OSSL_FUNC_KEYMGMT_GETTABLE_PARAMS,
     (void (*)(void))awslc_prov_rsa_gettable_params},
    {OSSL_FUNC_KEYMGMT_DUP, (void (*)(void))awslc_prov_rsa_dup},
    {OSSL_FUNC_KEYMGMT_GEN_INIT, (void (*)(void))awslc_prov_rsa_gen_init},
    {OSSL_FUNC_KEYMGMT_GEN_SET_PARAMS,
     (void (*)(void))awslc_prov_rsa_gen_set_params},
    {OSSL_FUNC_KEYMGMT_GEN_SETTABLE_PARAMS,
     (void (*)(void))awslc_prov_rsa_gen_settable_params},
    {OSSL_FUNC_KEYMGMT_GEN_GET_PARAMS,
     (void (*)(void))awslc_prov_rsa_gen_get_params},
    {OSSL_FUNC_KEYMGMT_GEN_GETTABLE_PARAMS,
     (void (*)(void))awslc_prov_rsa_gen_gettable_params},
    {OSSL_FUNC_KEYMGMT_GEN, (void (*)(void))awslc_prov_rsa_gen},
    {OSSL_FUNC_KEYMGMT_GEN_CLEANUP, (void (*)(void))awslc_prov_rsa_gen_cleanup},
    OSSL_DISPATCH_END};
