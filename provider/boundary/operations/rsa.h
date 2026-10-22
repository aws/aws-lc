// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_BOUNDARY_OPERATIONS_RSA_H
#define AWSLC_PROVIDER_BOUNDARY_OPERATIONS_RSA_H

// The RSA entry points the back side implements.

#include "boundary/utils.h"

#if defined(__cplusplus)
extern "C" {
#endif

// RSA key components, in the order OpenSSL exports them.
typedef enum {
  AWSLC_PROV_RSA_N = 0,
  AWSLC_PROV_RSA_E,
  AWSLC_PROV_RSA_D,
  AWSLC_PROV_RSA_P,
  AWSLC_PROV_RSA_Q,
  AWSLC_PROV_RSA_DMP1,
  AWSLC_PROV_RSA_DMQ1,
  AWSLC_PROV_RSA_IQMP,
  AWSLC_PROV_RSA_COMPONENT_COUNT
} AWSLC_PROV_RSA_COMPONENT;

#define AWSLC_PROV_RSA_CRT_COUNT \
  (AWSLC_PROV_RSA_COMPONENT_COUNT - AWSLC_PROV_RSA_P)

// An RSA-PSS key's restrictions, RFC 4055 RSASSA-PSS-params: the only digest
// and MGF1 digest it signs with, by any name awslc_prov_digest_canonical_name
// accepts, and its minimum salt length.
typedef struct {
  const char *digest;
  const char *mgf1_digest;
  int saltlen;
} AWSLC_PROV_RSA_PSS_PARAMS;

// RFC 4055 RSASSA-PSS-params defaults, which a restriction takes for each field
// it omits. The digest default applies to the MGF1 digest too.
#define AWSLC_PROV_RSA_PSS_DEFAULT_DIGEST "SHA1"
#define AWSLC_PROV_RSA_PSS_DEFAULT_SALTLEN 20

// Whether AWS-LC accepts |pss| as an RSA-PSS key's restrictions.
int awslc_prov_rsa_pss_params_supported(const AWSLC_PROV_RSA_PSS_PARAMS *pss);

// A new RSA key from |components|, where a NULL |data| is an absent component.
// The present set must be n and e; n, e, and d; or all eight. Any other set,
// or values AWS-LC rejects, return NULL. A non-NULL |pss| makes AWS-LC enforce
// those restrictions on every signature the key makes, and requires n and e
// or all eight components.
void *awslc_prov_rsa_new(
    const AWSLC_PROV_BN_BYTES components[AWSLC_PROV_RSA_COMPONENT_COUNT],
    const AWSLC_PROV_RSA_PSS_PARAMS *pss);

// A new RSA key holding only |rsa|'s n and e, restricted by |pss| as
// awslc_prov_rsa_new is.
void *awslc_prov_rsa_new_public(const void *rsa,
                                const AWSLC_PROV_RSA_PSS_PARAMS *pss);

void awslc_prov_rsa_free(void *rsa);
int awslc_prov_rsa_up_ref(void *rsa);

// |rsa|'s |component| as a BIGNUM that lives as long as |rsa|, or NULL when
// the key lacks it.
const void *awslc_prov_rsa_get0(const void *rsa,
                                AWSLC_PROV_RSA_COMPONENT component);

// Zero for a NULL |rsa|.
unsigned awslc_prov_rsa_bits(const void *rsa);
unsigned awslc_prov_rsa_size(const void *rsa);
unsigned awslc_prov_rsa_security_bits(const void *rsa);

int awslc_prov_rsa_check(const void *rsa);

// A new two-prime key with e = 65537 by FIPS 186-5 key generation, restricted
// by |pss| as awslc_prov_rsa_new is, or NULL. AWS-LC refuses a |bits| under
// 2048 or not a multiple of 128.
void *awslc_prov_rsa_generate(unsigned bits,
                              const AWSLC_PROV_RSA_PSS_PARAMS *pss);

typedef enum {
  AWSLC_PROV_RSA_PADDING_PKCS1 = 1,
  AWSLC_PROV_RSA_PADDING_NONE,
  AWSLC_PROV_RSA_PADDING_PSS,
} AWSLC_PROV_RSA_PADDING;

// The special PSS salt lengths. Any non-negative value is an exact length.
//
//   DIGEST           the digest's length
//   AUTO             signing: the maximum; verifying: whatever was used
//   MAX              the maximum, and on verify exactly the maximum
//   AUTO_DIGEST_MAX  signing: the digest's length, or the maximum if smaller;
//                    verifying: whatever was used
#define AWSLC_PROV_RSA_PSS_SALTLEN_DIGEST (-1)
#define AWSLC_PROV_RSA_PSS_SALTLEN_AUTO (-2)
#define AWSLC_PROV_RSA_PSS_SALTLEN_MAX (-3)
#define AWSLC_PROV_RSA_PSS_SALTLEN_AUTO_DIGEST_MAX (-4)

typedef enum {
  // Over a caller's digest, or raw input when no digest is set.
  AWSLC_PROV_RSA_SIG_SIGN = 0,
  AWSLC_PROV_RSA_SIG_VERIFY,
  AWSLC_PROV_RSA_SIG_VERIFY_RECOVER,
  // Hash-then-sign through AWS-LC's EVP_DigestSign* and EVP_DigestVerify*,
  // the only RSA entry points that credit the FIPS service indicator.
  AWSLC_PROV_RSA_SIG_DIGEST_SIGN,
  AWSLC_PROV_RSA_SIG_DIGEST_VERIFY,
} AWSLC_PROV_RSA_SIG_OPERATION;

// A new |operation| over |rsa|, holding its own reference to it. |pss_key|
// gives the key RSA-PSS semantics: PSS padding only, and, when |restricted|,
// the restrictions AWS-LC attached to |rsa|. |digest| is required for the
// digest operations and optional for the others. Salt length starts at
// AUTO_DIGEST_MAX, or at the key's minimum when |restricted|.
void *awslc_prov_rsa_sig_new(void *rsa, int pss_key, int restricted,
                             AWSLC_PROV_RSA_SIG_OPERATION operation,
                             const char *digest);
void *awslc_prov_rsa_sig_dup(const void *sig);
void awslc_prov_rsa_sig_free(void *sig);

int awslc_prov_rsa_sig_set_padding(void *sig, AWSLC_PROV_RSA_PADDING padding);
// Fails in a digest operation, whose digest is fixed at creation.
int awslc_prov_rsa_sig_set_digest(void *sig, const char *digest);
int awslc_prov_rsa_sig_set_mgf1_digest(void *sig, const char *digest);
int awslc_prov_rsa_sig_set_pss_saltlen(void *sig, int saltlen);

// Zero when AWS-LC reports a padding mode not in AWSLC_PROV_RSA_PADDING.
int awslc_prov_rsa_sig_padding(const void *sig);
// OpenSSL canonical names, or NULL when there is no digest.
const char *awslc_prov_rsa_sig_digest(const void *sig);
const char *awslc_prov_rsa_sig_mgf1_digest(const void *sig);
// The salt length as last set, special values unresolved.
int awslc_prov_rsa_sig_pss_saltlen(const void *sig);

// The DER AlgorithmIdentifier of the signature the current parameters make,
// into |out_size| bytes at |out|.
int awslc_prov_rsa_sig_algorithm_id(const void *sig, unsigned char *out,
                                    size_t out_size, size_t *out_len);

// For the digest operations.
int awslc_prov_rsa_sig_update(void *sig, const unsigned char *data, size_t len);
// A NULL |out| sets |*out_len| to the signature size.
int awslc_prov_rsa_sig_sign_final(void *sig, unsigned char *out,
                                  size_t *out_len, size_t out_size);
int awslc_prov_rsa_sig_verify_final(void *sig, const unsigned char *in,
                                    size_t in_len);

// For the others. A NULL |out| sets |*out_len| to the output size.
int awslc_prov_rsa_sig_sign(void *sig, unsigned char *out, size_t *out_len,
                            size_t out_size, const unsigned char *tbs,
                            size_t tbs_len);
int awslc_prov_rsa_sig_verify(void *sig, const unsigned char *in, size_t in_len,
                              const unsigned char *tbs, size_t tbs_len);
int awslc_prov_rsa_sig_verify_recover(void *sig, unsigned char *out,
                                      size_t *out_len, size_t out_size,
                                      const unsigned char *in, size_t in_len);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_BOUNDARY_OPERATIONS_RSA_H
