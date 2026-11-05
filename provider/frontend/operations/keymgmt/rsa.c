// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Front side: the RSA key manager's dispatch slots. Selection handling follows
// OpenSSL's default RSA key manager.

#include <openssl/core_dispatch.h>
#include <openssl/core_names.h>
#include <openssl/crypto.h>
#include <openssl/params.h>

#include <string.h>

#include "boundary.h"
#include "boundary/operations/rsa.h"
#include "boundary/utils.h"
#include "frontend/operations/keymgmt/keymgmt.h"
#include "frontend/operations/rsa.h"
#include "frontend/provider.h"
#include "frontend/utils.h"

#define AWSLC_PROV_RSA_NAME "RSA"
#define AWSLC_PROV_RSA_PSS_NAME "RSA-PSS"
// The only mask generation function RFC 4055 defines.
#define AWSLC_PROV_RSA_PSS_MGF "MGF1"
// The digest a signer uses when the caller names none, such as certificates
// and CMS signed without -digest. SHA-256 is aligned with the OpenSSL default.
#define AWSLC_PROV_RSA_DEFAULT_DIGEST "SHA256"
// OTHER_PARAMETERS is non-key metadata, such as RSA-PSS limits.
#define AWSLC_PROV_RSA_POSSIBLE_SELECTIONS \
  (OSSL_KEYMGMT_SELECT_KEYPAIR | OSSL_KEYMGMT_SELECT_OTHER_PARAMETERS)

#define AWSLC_PROV_RSA_DEFAULT_BITS 2048
#define AWSLC_PROV_RSA_PRIMES 2
#define AWSLC_PROV_RSA_PUBLIC_EXPONENT 65537

// The keydata of both RSA key managers.
typedef struct {
  AWSLC_PROV_CTX *provctx;
  // NULL until an import or generation fills it.
  void *rsa;
  // An RSA-PSS key, which signs with PSS padding only.
  int pss;
  // Whether AWS-LC enforces |restrictions| on |rsa|.
  int restricted;
  AWSLC_PROV_RSA_PSS_PARAMS restrictions;
} AWSLC_PROV_RSA_KEY;

typedef struct {
  AWSLC_PROV_CTX *provctx;
  unsigned bits;
  int fips_approved;
  int pss;
  int restricted;
  AWSLC_PROV_RSA_PSS_PARAMS restrictions;
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

#define AWSLC_PROV_RSA_PSS_RESTRICTION_TYPES                            \
  OSSL_PARAM_utf8_string(OSSL_PKEY_PARAM_RSA_DIGEST, NULL, 0),          \
      OSSL_PARAM_utf8_string(OSSL_PKEY_PARAM_RSA_MGF1_DIGEST, NULL, 0), \
      OSSL_PARAM_int(OSSL_PKEY_PARAM_RSA_PSS_SALTLEN, NULL)

static const OSSL_PARAM awslc_prov_rsa_pss_importable[] = {
    AWSLC_PROV_RSA_KEY_TYPES, AWSLC_PROV_RSA_PSS_RESTRICTION_TYPES,
    OSSL_PARAM_utf8_string(OSSL_PKEY_PARAM_RSA_MASKGENFUNC, NULL, 0),
    OSSL_PARAM_END};

static const OSSL_PARAM awslc_prov_rsa_pss_exportable[] = {
    AWSLC_PROV_RSA_KEY_TYPES, AWSLC_PROV_RSA_PSS_RESTRICTION_TYPES,
    OSSL_PARAM_END};

static const OSSL_PARAM awslc_prov_rsa_pss_restrictions[] = {
    AWSLC_PROV_RSA_PSS_RESTRICTION_TYPES, OSSL_PARAM_END};

// The restriction fields an RSA-PSS key exports, less the table's end.
#define AWSLC_PROV_RSA_PSS_RESTRICTION_COUNT        \
  (sizeof(awslc_prov_rsa_pss_restrictions) /        \
       sizeof(awslc_prov_rsa_pss_restrictions[0]) - \
   1)

#define AWSLC_PROV_RSA_GETTABLE                                        \
  OSSL_PARAM_int(OSSL_PKEY_PARAM_BITS, NULL),                          \
      OSSL_PARAM_int(OSSL_PKEY_PARAM_SECURITY_BITS, NULL),             \
      OSSL_PARAM_int(OSSL_PKEY_PARAM_MAX_SIZE, NULL),                  \
      OSSL_PARAM_utf8_string(OSSL_PKEY_PARAM_DEFAULT_DIGEST, NULL, 0), \
      AWSLC_PROV_RSA_KEY_TYPES

static const OSSL_PARAM awslc_prov_rsa_gettable[] = {AWSLC_PROV_RSA_GETTABLE,
                                                     OSSL_PARAM_END};

static const OSSL_PARAM awslc_prov_rsa_pss_gettable[] = {
    AWSLC_PROV_RSA_GETTABLE,
    OSSL_PARAM_utf8_string(OSSL_PKEY_PARAM_MANDATORY_DIGEST, NULL, 0),
    AWSLC_PROV_RSA_PSS_RESTRICTION_TYPES, OSSL_PARAM_END};

#define AWSLC_PROV_RSA_GEN_TYPES                           \
  OSSL_PARAM_size_t(OSSL_PKEY_PARAM_RSA_BITS, NULL),       \
      OSSL_PARAM_size_t(OSSL_PKEY_PARAM_RSA_PRIMES, NULL), \
      OSSL_PARAM_BN(OSSL_PKEY_PARAM_RSA_E, NULL, 0)

static const OSSL_PARAM awslc_prov_rsa_gen_settable[] = {
    AWSLC_PROV_RSA_GEN_TYPES, OSSL_PARAM_END};

static const OSSL_PARAM awslc_prov_rsa_pss_gen_settable[] = {
    AWSLC_PROV_RSA_GEN_TYPES,
    OSSL_PARAM_utf8_string(OSSL_PKEY_PARAM_RSA_DIGEST, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_PKEY_PARAM_RSA_DIGEST_PROPS, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_PKEY_PARAM_RSA_MASKGENFUNC, NULL, 0),
    OSSL_PARAM_utf8_string(OSSL_PKEY_PARAM_RSA_MGF1_DIGEST, NULL, 0),
    OSSL_PARAM_int(OSSL_PKEY_PARAM_RSA_PSS_SALTLEN, NULL),
    OSSL_PARAM_END};

static const OSSL_PARAM awslc_prov_rsa_gen_gettable[] = {
    OSSL_PARAM_int(OSSL_PKEY_PARAM_FIPS_APPROVED_INDICATOR, NULL),
    OSSL_PARAM_END};

static OSSL_FUNC_keymgmt_new_fn awslc_prov_rsa_newdata;
static OSSL_FUNC_keymgmt_new_fn awslc_prov_rsa_pss_newdata;
static OSSL_FUNC_keymgmt_free_fn awslc_prov_rsa_freedata;
static OSSL_FUNC_keymgmt_has_fn awslc_prov_rsa_has;
static OSSL_FUNC_keymgmt_match_fn awslc_prov_rsa_match;
static OSSL_FUNC_keymgmt_validate_fn awslc_prov_rsa_validate;
static OSSL_FUNC_keymgmt_import_fn awslc_prov_rsa_import;
static OSSL_FUNC_keymgmt_import_types_fn awslc_prov_rsa_base_types;
static OSSL_FUNC_keymgmt_export_fn awslc_prov_rsa_export;
static OSSL_FUNC_keymgmt_get_params_fn awslc_prov_rsa_get_params;
static OSSL_FUNC_keymgmt_gettable_params_fn awslc_prov_rsa_gettable_params;
static OSSL_FUNC_keymgmt_gettable_params_fn awslc_prov_rsa_pss_gettable_params;
static OSSL_FUNC_keymgmt_import_types_fn awslc_prov_rsa_pss_import_types;
static OSSL_FUNC_keymgmt_export_types_fn awslc_prov_rsa_pss_export_types;
static OSSL_FUNC_keymgmt_dup_fn awslc_prov_rsa_dup;
static OSSL_FUNC_keymgmt_gen_init_fn awslc_prov_rsa_gen_init;
static OSSL_FUNC_keymgmt_gen_init_fn awslc_prov_rsa_pss_gen_init;
static OSSL_FUNC_keymgmt_gen_set_params_fn awslc_prov_rsa_gen_set_params;
static OSSL_FUNC_keymgmt_gen_settable_params_fn
    awslc_prov_rsa_gen_settable_params;
static OSSL_FUNC_keymgmt_gen_settable_params_fn
    awslc_prov_rsa_pss_gen_settable_params;
static OSSL_FUNC_keymgmt_gen_get_params_fn awslc_prov_rsa_gen_get_params;
static OSSL_FUNC_keymgmt_gen_gettable_params_fn
    awslc_prov_rsa_gen_gettable_params;
static OSSL_FUNC_keymgmt_gen_fn awslc_prov_rsa_gen;
static OSSL_FUNC_keymgmt_gen_cleanup_fn awslc_prov_rsa_gen_cleanup;
static OSSL_FUNC_keymgmt_query_operation_name_fn
    awslc_prov_rsa_pss_query_operation_name;

static AWSLC_PROV_RSA_KEY *awslc_prov_rsa_key_new(AWSLC_PROV_CTX *provctx,
                                                  int pss) {
  AWSLC_PROV_RSA_KEY *key = NULL;
  AWSLC_PROV_CALL call;

  awslc_prov_call_begin(&call, provctx);
  key = awslc_prov_zalloc(sizeof(*key));
  if (!AWSLC_PROV_CALL_END(&call, key != NULL, AWSLC_PROV_RSA_NAME)) {
    return NULL;
  }
  key->provctx = provctx;
  key->pss = pss;
  return key;
}

static void *awslc_prov_rsa_newdata(void *provctx) {
  return awslc_prov_rsa_key_new((AWSLC_PROV_CTX *)provctx, 0);
}

static void *awslc_prov_rsa_pss_newdata(void *provctx) {
  return awslc_prov_rsa_key_new((AWSLC_PROV_CTX *)provctx, 1);
}

static const AWSLC_PROV_RSA_PSS_PARAMS *awslc_prov_rsa_key_restrictions(
    const AWSLC_PROV_RSA_KEY *key) {
  return key->restricted ? &key->restrictions : NULL;
}

static const char *awslc_prov_rsa_key_name(const AWSLC_PROV_RSA_KEY *key) {
  return key->pss ? AWSLC_PROV_RSA_PSS_NAME : AWSLC_PROV_RSA_NAME;
}

// Read the RSA-PSS restrictions in |params| over |*out|, refusing any AWS-LC
// cannot enforce. The first present one sets |*restricted| and starts every
// field from its RFC 4055 default.
static int awslc_prov_rsa_read_pss_params(const AWSLC_PROV_CTX *provctx,
                                          const OSSL_PARAM params[],
                                          int *restricted,
                                          AWSLC_PROV_RSA_PSS_PARAMS *out) {
  const OSSL_PARAM *digest =
      OSSL_PARAM_locate_const(params, OSSL_PKEY_PARAM_RSA_DIGEST);
  const OSSL_PARAM *mgf =
      OSSL_PARAM_locate_const(params, OSSL_PKEY_PARAM_RSA_MASKGENFUNC);
  const OSSL_PARAM *mgf1_digest =
      OSSL_PARAM_locate_const(params, OSSL_PKEY_PARAM_RSA_MGF1_DIGEST);
  const OSSL_PARAM *saltlen =
      OSSL_PARAM_locate_const(params, OSSL_PKEY_PARAM_RSA_PSS_SALTLEN);

  if (digest == NULL && mgf == NULL && mgf1_digest == NULL &&
      saltlen == NULL) {
    return 1;
  }
  if (!*restricted) {
    *restricted = 1;
    out->digest = AWSLC_PROV_RSA_PSS_DEFAULT_DIGEST;
    out->mgf1_digest = AWSLC_PROV_RSA_PSS_DEFAULT_DIGEST;
    out->saltlen = AWSLC_PROV_RSA_PSS_DEFAULT_SALTLEN;
  }
  if (mgf != NULL) {
    const char *name = NULL;

    if (!OSSL_PARAM_get_utf8_string_ptr(mgf, &name) ||
        OPENSSL_strcasecmp(name, AWSLC_PROV_RSA_PSS_MGF) != 0) {
      AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                             mgf->key);
      return 0;
    }
  }
  if (saltlen != NULL && !OSSL_PARAM_get_int(saltlen, &out->saltlen)) {
    AWSLC_PROV_ERROR_RAISE(provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           saltlen->key);
    return 0;
  }
  // OSSL_PKEY_PARAM_RSA_DIGEST_PROPS is accepted and ignored: a restriction
  // records which digest a key signs with, not the implementation computing it.
  if (!awslc_prov_param_get_digest(provctx, digest, &out->digest) ||
      !awslc_prov_param_get_digest(provctx, mgf1_digest, &out->mgf1_digest)) {
    return 0;
  }

  AWSLC_PROV_CALL call;

  awslc_prov_call_begin(&call, provctx);
  int ok = awslc_prov_rsa_pss_params_supported(out);
  return AWSLC_PROV_CALL_END(&call, ok, AWSLC_PROV_RSA_PSS_NAME);
}

static int awslc_prov_rsa_is_default_digest(const char *name) {
  return strcmp(name, AWSLC_PROV_RSA_PSS_DEFAULT_DIGEST) == 0;
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
  AWSLC_PROV_CALL call;

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

  awslc_prov_call_begin(&call, key->provctx);
  int ok = awslc_prov_rsa_check(key->rsa);
  return AWSLC_PROV_CALL_END(&call, ok, awslc_prov_rsa_key_name(key));
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
  if (!awslc_prov_param_get_bn(provctx, params, OSSL_PKEY_PARAM_RSA_N,
                               &components[AWSLC_PROV_RSA_N]) ||
      !awslc_prov_param_get_bn(provctx, params, OSSL_PKEY_PARAM_RSA_E,
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
  if (!awslc_prov_param_get_bn(provctx, params, OSSL_PKEY_PARAM_RSA_D,
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
    if (!awslc_prov_param_get_bn(provctx, params,
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
  AWSLC_PROV_RSA_PSS_PARAMS restrictions = {NULL, NULL, 0};
  int restricted = 0;
  AWSLC_PROV_CALL call;
  void *rsa = NULL;

  if (key == NULL) {
    return 0;
  }
  // Restrictions alone cannot make a key, and keys are never amended.
  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) == 0) {
    AWSLC_PROV_ERROR_RAISE(key->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           awslc_prov_rsa_key_name(key));
    return 0;
  }
  if ((selection & OSSL_KEYMGMT_SELECT_OTHER_PARAMETERS) != 0) {
    if (!awslc_prov_rsa_read_pss_params(key->provctx, params, &restricted,
                                        &restrictions)) {
      return 0;
    }
    if (restricted && !key->pss) {
      AWSLC_PROV_ERROR_RAISE(key->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                             AWSLC_PROV_RSA_NAME);
      return 0;
    }
  }
  if (!awslc_prov_rsa_read_components(
          key->provctx, params,
          (selection & OSSL_KEYMGMT_SELECT_PRIVATE_KEY) != 0, components)) {
    return 0;
  }

  awslc_prov_call_begin(&call, key->provctx);
  rsa = awslc_prov_rsa_new(components, restricted ? &restrictions : NULL);
  if (!AWSLC_PROV_CALL_END(&call, rsa != NULL, awslc_prov_rsa_key_name(key))) {
    return 0;
  }
  awslc_prov_rsa_free(key->rsa);
  key->rsa = rsa;
  key->restricted = restricted;
  key->restrictions = restrictions;
  return 1;
}

// The key pair types both key managers import and export.
static const OSSL_PARAM *awslc_prov_rsa_base_types(int selection) {
  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) != 0) {
    return awslc_prov_rsa_key_types;
  }
  return NULL;
}

static int awslc_prov_rsa_export(void *keydata, int selection,
                                 OSSL_CALLBACK *callback, void *cbarg) {
  const AWSLC_PROV_RSA_KEY *key = (const AWSLC_PROV_RSA_KEY *)keydata;
  AWSLC_PROV_PARAM_BN bns[AWSLC_PROV_RSA_COMPONENT_COUNT];
  size_t count = 0;

  if (key == NULL) {
    return 0;
  }
  if ((selection & AWSLC_PROV_RSA_POSSIBLE_SELECTIONS) == 0 ||
      key->rsa == NULL || callback == NULL) {
    AWSLC_PROV_ERROR_RAISE(key->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           awslc_prov_rsa_key_name(key));
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

  // The big numbers, then the restriction fields, then the end.
  OSSL_PARAM params[AWSLC_PROV_RSA_COMPONENT_COUNT +
                    AWSLC_PROV_RSA_PSS_RESTRICTION_COUNT + 1];
  unsigned char *buffer = NULL;
  size_t size = 0;
  int saltlen = key->restrictions.saltlen;
  int ok = awslc_prov_param_encode_bns(key->provctx, bns, count, params,
                                       &buffer, &size);

  if ((selection & OSSL_KEYMGMT_SELECT_OTHER_PARAMETERS) != 0 &&
      key->restricted) {
    if (!awslc_prov_rsa_is_default_digest(key->restrictions.digest)) {
      params[count++] = OSSL_PARAM_construct_utf8_string(
          OSSL_PKEY_PARAM_RSA_DIGEST, (char *)key->restrictions.digest, 0);
    }
    if (!awslc_prov_rsa_is_default_digest(key->restrictions.mgf1_digest)) {
      params[count++] = OSSL_PARAM_construct_utf8_string(
          OSSL_PKEY_PARAM_RSA_MGF1_DIGEST,
          (char *)key->restrictions.mgf1_digest, 0);
    }
    params[count++] =
        OSSL_PARAM_construct_int(OSSL_PKEY_PARAM_RSA_PSS_SALTLEN, &saltlen);
  }
  params[count] = OSSL_PARAM_construct_end();
  ok = ok && callback(params, cbarg);
  awslc_prov_clear_free(buffer, size);
  return ok;
}

// Import refuses a selection without the key pair, which export allows.
static const OSSL_PARAM *awslc_prov_rsa_pss_import_types(int selection) {
  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) != 0 &&
      (selection & OSSL_KEYMGMT_SELECT_OTHER_PARAMETERS) != 0) {
    return awslc_prov_rsa_pss_importable;
  }
  return awslc_prov_rsa_base_types(selection);
}

static const OSSL_PARAM *awslc_prov_rsa_pss_export_types(int selection) {
  if ((selection & OSSL_KEYMGMT_SELECT_OTHER_PARAMETERS) == 0) {
    return awslc_prov_rsa_base_types(selection);
  }
  return (selection & OSSL_KEYMGMT_SELECT_KEYPAIR) != 0
             ? awslc_prov_rsa_pss_exportable
             : awslc_prov_rsa_pss_restrictions;
}

static int awslc_prov_rsa_get_params(void *keydata, OSSL_PARAM params[]) {
  const AWSLC_PROV_RSA_KEY *key = (const AWSLC_PROV_RSA_KEY *)keydata;

  if (key == NULL) {
    return 0;
  }
  if (key->rsa == NULL) {
    AWSLC_PROV_ERROR_RAISE(key->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           awslc_prov_rsa_key_name(key));
    return 0;
  }
  if (!awslc_prov_param_set_int(key->provctx, params, OSSL_PKEY_PARAM_BITS,
                                (int)awslc_prov_rsa_bits(key->rsa)) ||
      !awslc_prov_param_set_int(key->provctx, params,
                                OSSL_PKEY_PARAM_SECURITY_BITS,
                                (int)awslc_prov_rsa_security_bits(key->rsa)) ||
      !awslc_prov_param_set_int(key->provctx, params, OSSL_PKEY_PARAM_MAX_SIZE,
                                (int)awslc_prov_rsa_size(key->rsa))) {
    return 0;
  }
  // A restricted key names the one digest it signs with, in place of a default,
  // and leaves a default digest out of its restrictions as OpenSSL's export
  // does.
  if (key->restricted) {
    const AWSLC_PROV_RSA_PSS_PARAMS *pss = &key->restrictions;

    if (!awslc_prov_param_set_utf8_string(key->provctx, params,
                                          OSSL_PKEY_PARAM_MANDATORY_DIGEST,
                                          pss->digest) ||
        (!awslc_prov_rsa_is_default_digest(pss->digest) &&
         !awslc_prov_param_set_utf8_string(key->provctx, params,
                                           OSSL_PKEY_PARAM_RSA_DIGEST,
                                           pss->digest)) ||
        (!awslc_prov_rsa_is_default_digest(pss->mgf1_digest) &&
         !awslc_prov_param_set_utf8_string(key->provctx, params,
                                           OSSL_PKEY_PARAM_RSA_MGF1_DIGEST,
                                           pss->mgf1_digest)) ||
        !awslc_prov_param_set_int(key->provctx, params,
                                  OSSL_PKEY_PARAM_RSA_PSS_SALTLEN,
                                  pss->saltlen)) {
      return 0;
    }
  } else if (!awslc_prov_param_set_utf8_string(key->provctx, params,
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

static const OSSL_PARAM *awslc_prov_rsa_pss_gettable_params(void *provctx) {
  (void)provctx;
  return awslc_prov_rsa_pss_gettable;
}

static void *awslc_prov_rsa_dup(const void *keydata, int selection) {
  const AWSLC_PROV_RSA_KEY *key = (const AWSLC_PROV_RSA_KEY *)keydata;
  AWSLC_PROV_RSA_KEY *duplicate = NULL;
  AWSLC_PROV_CALL call;

  if (key == NULL) {
    return NULL;
  }
  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) == 0) {
    AWSLC_PROV_ERROR_RAISE(key->provctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           awslc_prov_rsa_key_name(key));
    return NULL;
  }
  duplicate = awslc_prov_rsa_key_new(key->provctx, key->pss);
  if (duplicate == NULL || key->rsa == NULL) {
    return duplicate;
  }
  duplicate->restricted = key->restricted;
  duplicate->restrictions = key->restrictions;

  awslc_prov_call_begin(&call, key->provctx);
  // Keys are never mutated once built, so a private duplicate shares one.
  if ((selection & OSSL_KEYMGMT_SELECT_PRIVATE_KEY) != 0) {
    duplicate->rsa = awslc_prov_rsa_up_ref(key->rsa) ? key->rsa : NULL;
  } else {
    duplicate->rsa = awslc_prov_rsa_new_public(
        key->rsa, awslc_prov_rsa_key_restrictions(key));
  }
  if (!AWSLC_PROV_CALL_END(&call, duplicate->rsa != NULL,
                           awslc_prov_rsa_key_name(key))) {
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
  return !gctx->pss ||
         awslc_prov_rsa_read_pss_params(gctx->provctx, params,
                                        &gctx->restricted,
                                        &gctx->restrictions);
}

static void awslc_prov_rsa_gen_cleanup(void *genctx) {
  AWSLC_PROV_RSA_GEN_CTX *gctx = (AWSLC_PROV_RSA_GEN_CTX *)genctx;

  if (gctx == NULL) {
    return;
  }
  awslc_prov_clear_free(gctx, sizeof(*gctx));
}

static void *awslc_prov_rsa_gen_init_type(void *provctx, int selection,
                                          const OSSL_PARAM params[], int pss) {
  AWSLC_PROV_CTX *ctx = (AWSLC_PROV_CTX *)provctx;
  AWSLC_PROV_RSA_GEN_CTX *gctx = NULL;
  AWSLC_PROV_CALL call;

  if ((selection & OSSL_KEYMGMT_SELECT_KEYPAIR) == 0) {
    AWSLC_PROV_ERROR_RAISE(ctx, AWSLC_PROV_R_INVALID_PARAMETER,
                           AWSLC_PROV_RSA_NAME);
    return NULL;
  }
  awslc_prov_call_begin(&call, ctx);
  gctx = awslc_prov_zalloc(sizeof(*gctx));
  if (!AWSLC_PROV_CALL_END(&call, gctx != NULL, AWSLC_PROV_RSA_NAME)) {
    return NULL;
  }
  gctx->provctx = ctx;
  gctx->bits = AWSLC_PROV_RSA_DEFAULT_BITS;
  gctx->fips_approved = awslc_prov_ctx_is_fips(ctx);
  gctx->pss = pss;
  if (!awslc_prov_rsa_gen_set_params(gctx, params)) {
    awslc_prov_rsa_gen_cleanup(gctx);
    return NULL;
  }
  return gctx;
}

static void *awslc_prov_rsa_gen_init(void *provctx, int selection,
                                     const OSSL_PARAM params[]) {
  return awslc_prov_rsa_gen_init_type(provctx, selection, params, 0);
}

static void *awslc_prov_rsa_pss_gen_init(void *provctx, int selection,
                                         const OSSL_PARAM params[]) {
  return awslc_prov_rsa_gen_init_type(provctx, selection, params, 1);
}

static const OSSL_PARAM *awslc_prov_rsa_gen_settable_params(void *genctx,
                                                            void *provctx) {
  (void)genctx;
  (void)provctx;
  return awslc_prov_rsa_gen_settable;
}

static const OSSL_PARAM *awslc_prov_rsa_pss_gen_settable_params(
    void *genctx, void *provctx) {
  (void)genctx;
  (void)provctx;
  return awslc_prov_rsa_pss_gen_settable;
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
  AWSLC_PROV_CALL call;

  // This callback is used to report progress, we don't bother.
  (void)callback;
  (void)cbarg;
  if (gctx == NULL) {
    return NULL;
  }
  key = awslc_prov_rsa_key_new(gctx->provctx, gctx->pss);
  if (key == NULL) {
    return NULL;
  }
  key->restricted = gctx->restricted;
  key->restrictions = gctx->restrictions;

  awslc_prov_call_begin(&call, gctx->provctx);
  key->rsa =
      awslc_prov_rsa_generate(gctx->bits, awslc_prov_rsa_key_restrictions(key));
  gctx->fips_approved =
      key->rsa != NULL && awslc_prov_ctx_is_fips(gctx->provctx);
  if (!AWSLC_PROV_CALL_END_CHECK_APPROVED(
          &call, key->rsa != NULL, awslc_prov_rsa_key_name(key),
          AWSLC_PROV_KEYGEN_OPERATION_DESCRIPTION, &gctx->fips_approved)) {
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
    {OSSL_FUNC_KEYMGMT_IMPORT_TYPES, (void (*)(void))awslc_prov_rsa_base_types},
    {OSSL_FUNC_KEYMGMT_EXPORT, (void (*)(void))awslc_prov_rsa_export},
    {OSSL_FUNC_KEYMGMT_EXPORT_TYPES, (void (*)(void))awslc_prov_rsa_base_types},
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

// Every RSA key type signs with the "RSA" signature.
static const char *awslc_prov_rsa_pss_query_operation_name(int operation_id) {
  (void)operation_id;
  return AWSLC_PROV_RSA_NAME;
}

const OSSL_DISPATCH awslc_prov_rsa_pss_keymgmt_functions[] = {
    {OSSL_FUNC_KEYMGMT_NEW, (void (*)(void))awslc_prov_rsa_pss_newdata},
    {OSSL_FUNC_KEYMGMT_FREE, (void (*)(void))awslc_prov_rsa_freedata},
    {OSSL_FUNC_KEYMGMT_HAS, (void (*)(void))awslc_prov_rsa_has},
    {OSSL_FUNC_KEYMGMT_MATCH, (void (*)(void))awslc_prov_rsa_match},
    {OSSL_FUNC_KEYMGMT_VALIDATE, (void (*)(void))awslc_prov_rsa_validate},
    {OSSL_FUNC_KEYMGMT_IMPORT, (void (*)(void))awslc_prov_rsa_import},
    {OSSL_FUNC_KEYMGMT_IMPORT_TYPES,
     (void (*)(void))awslc_prov_rsa_pss_import_types},
    {OSSL_FUNC_KEYMGMT_EXPORT, (void (*)(void))awslc_prov_rsa_export},
    {OSSL_FUNC_KEYMGMT_EXPORT_TYPES,
     (void (*)(void))awslc_prov_rsa_pss_export_types},
    {OSSL_FUNC_KEYMGMT_GET_PARAMS, (void (*)(void))awslc_prov_rsa_get_params},
    {OSSL_FUNC_KEYMGMT_GETTABLE_PARAMS,
     (void (*)(void))awslc_prov_rsa_pss_gettable_params},
    {OSSL_FUNC_KEYMGMT_DUP, (void (*)(void))awslc_prov_rsa_dup},
    {OSSL_FUNC_KEYMGMT_GEN_INIT, (void (*)(void))awslc_prov_rsa_pss_gen_init},
    {OSSL_FUNC_KEYMGMT_GEN_SET_PARAMS,
     (void (*)(void))awslc_prov_rsa_gen_set_params},
    {OSSL_FUNC_KEYMGMT_GEN_SETTABLE_PARAMS,
     (void (*)(void))awslc_prov_rsa_pss_gen_settable_params},
    {OSSL_FUNC_KEYMGMT_GEN_GET_PARAMS,
     (void (*)(void))awslc_prov_rsa_gen_get_params},
    {OSSL_FUNC_KEYMGMT_GEN_GETTABLE_PARAMS,
     (void (*)(void))awslc_prov_rsa_gen_gettable_params},
    {OSSL_FUNC_KEYMGMT_GEN, (void (*)(void))awslc_prov_rsa_gen},
    {OSSL_FUNC_KEYMGMT_GEN_CLEANUP, (void (*)(void))awslc_prov_rsa_gen_cleanup},
    {OSSL_FUNC_KEYMGMT_QUERY_OPERATION_NAME,
     (void (*)(void))awslc_prov_rsa_pss_query_operation_name},
    OSSL_DISPATCH_END};
