// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef AWSLC_CRYPTO_X509_VIEW_H
#define AWSLC_CRYPTO_X509_VIEW_H

#include <stddef.h>
#include <stdint.h>

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif

typedef struct {
  uint32_t offset;
  uint32_t length;
} AWSLC_X509_DER_RANGE;

typedef struct {
  uint8_t version;
  uint8_t flags;
  uint8_t reserved[2];
  uint32_t extension_flags;
  AWSLC_X509_DER_RANGE certificate;
  AWSLC_X509_DER_RANGE tbs_certificate;
  AWSLC_X509_DER_RANGE serial;
  AWSLC_X509_DER_RANGE tbs_signature_algorithm;
  AWSLC_X509_DER_RANGE issuer;
  AWSLC_X509_DER_RANGE validity;
  AWSLC_X509_DER_RANGE subject;
  AWSLC_X509_DER_RANGE spki;
  AWSLC_X509_DER_RANGE issuer_uid;
  AWSLC_X509_DER_RANGE subject_uid;
  AWSLC_X509_DER_RANGE extensions;
  AWSLC_X509_DER_RANGE signature_algorithm;
  AWSLC_X509_DER_RANGE signature;
  AWSLC_X509_DER_RANGE extension_values[9];
} AWSLC_X509_CERTIFICATE_VIEW;

enum {
  AWSLC_X509_FLAG_ISSUER_UID = 1 << 0,
  AWSLC_X509_FLAG_SUBJECT_UID = 1 << 1,
  AWSLC_X509_FLAG_EXTENSIONS = 1 << 2,
};

enum {
  AWSLC_X509_EXTENSION_BASIC_CONSTRAINTS = 0,
  AWSLC_X509_EXTENSION_KEY_USAGE = 1,
  AWSLC_X509_EXTENSION_EXTENDED_KEY_USAGE = 2,
  AWSLC_X509_EXTENSION_NETSCAPE_CERT_TYPE = 3,
  AWSLC_X509_EXTENSION_SUBJECT_KEY_IDENTIFIER = 4,
  AWSLC_X509_EXTENSION_AUTHORITY_KEY_IDENTIFIER = 5,
  AWSLC_X509_EXTENSION_SUBJECT_ALT_NAME = 6,
  AWSLC_X509_EXTENSION_NAME_CONSTRAINTS = 7,
  AWSLC_X509_EXTENSION_CRL_DISTRIBUTION_POINTS = 8,
  AWSLC_X509_EXTENSION_SLOT_COUNT = 9,
  AWSLC_X509_EXTENSION_DUPLICATE_SHIFT = 9,
  AWSLC_X509_EXTENSION_UNSUPPORTED_CRITICAL = 1 << 18,
  AWSLC_X509_EXTENSION_CRITICAL_SHIFT = 19,
};

enum {
  AWSLC_X509_PARSE_OK = 0,
  AWSLC_X509_PARSE_TRUNCATED = 1,
  AWSLC_X509_PARSE_INVALID_TAG = 2,
  AWSLC_X509_PARSE_INVALID_LENGTH = 3,
  AWSLC_X509_PARSE_TRAILING_DATA = 4,
  AWSLC_X509_PARSE_INVALID_VALUE = 5,
  AWSLC_X509_PARSE_INVALID_VERSION = 6,
  AWSLC_X509_PARSE_INVALID_FIELD_FOR_VERSION = 7,
  AWSLC_X509_PARSE_INVALID_NAME = 8,
  AWSLC_X509_PARSE_INVALID_TIME = 9,
  AWSLC_X509_PARSE_INVALID_ALGORITHM = 10,
  AWSLC_X509_PARSE_INVALID_EXTENSIONS = 11,
  AWSLC_X509_PARSE_INPUT_TOO_LARGE = 12,
  AWSLC_X509_PARSE_NULL_POINTER = 0x100,
};

#if defined(BORINGSSL_PREFIX)
#define AWSLC_X509_VIEW_ADD_PREFIX_INNER(prefix, symbol) prefix##_##symbol
#define AWSLC_X509_VIEW_ADD_PREFIX(prefix, symbol) \
  AWSLC_X509_VIEW_ADD_PREFIX_INNER(prefix, symbol)
#endif

#if defined(BORINGSSL_PREFIX) && !defined(x509_parse_der_view)
#define x509_parse_der_view \
  AWSLC_X509_VIEW_ADD_PREFIX(BORINGSSL_PREFIX, x509_parse_der_view)
#endif

#if defined(BORINGSSL_PREFIX) && !defined(x509_view_fallback_count_for_testing)
#define x509_view_fallback_count_for_testing   \
  AWSLC_X509_VIEW_ADD_PREFIX(BORINGSSL_PREFIX, \
                             x509_view_fallback_count_for_testing)
#endif

#if defined(BORINGSSL_PREFIX) && \
    !defined(x509_view_reset_fallback_counts_for_testing)
#define x509_view_reset_fallback_counts_for_testing \
  AWSLC_X509_VIEW_ADD_PREFIX(BORINGSSL_PREFIX,      \
                             x509_view_reset_fallback_counts_for_testing)
#endif

// Parses one DER certificate into a pointer-free view. If |exact| is non-zero,
// trailing bytes are rejected. The parser performs no allocation and leaves
// |out| unchanged on failure.
OPENSSL_EXPORT uint32_t
x509_parse_der_view(const uint8_t *der, size_t der_len, uint8_t exact,
                    AWSLC_X509_CERTIFICATE_VIEW *out);

OPENSSL_STATIC_ASSERT(sizeof(AWSLC_X509_DER_RANGE) == 8,
                      x509_der_range_size_mismatch)
OPENSSL_STATIC_ASSERT(sizeof(AWSLC_X509_CERTIFICATE_VIEW) == 184,
                      x509_certificate_view_size_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, version) == 0,
                      x509_certificate_version_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, flags) == 1,
                      x509_certificate_flags_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, reserved) == 2,
                      x509_certificate_reserved_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, extension_flags) ==
                          4,
                      x509_certificate_extension_flags_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, certificate) == 8,
                      x509_certificate_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, tbs_certificate) ==
                          16,
                      x509_tbs_certificate_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, serial) == 24,
                      x509_serial_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW,
                               tbs_signature_algorithm) == 32,
                      x509_tbs_signature_algorithm_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, issuer) == 40,
                      x509_issuer_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, validity) == 48,
                      x509_validity_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, subject) == 56,
                      x509_subject_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, spki) == 64,
                      x509_spki_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, issuer_uid) == 72,
                      x509_issuer_uid_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, subject_uid) == 80,
                      x509_subject_uid_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, extensions) == 88,
                      x509_extensions_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW,
                               signature_algorithm) == 96,
                      x509_signature_algorithm_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, signature) == 104,
                      x509_signature_range_offset_mismatch)
OPENSSL_STATIC_ASSERT(offsetof(AWSLC_X509_CERTIFICATE_VIEW, extension_values) ==
                          112,
                      x509_extension_values_offset_mismatch)

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // AWSLC_CRYPTO_X509_VIEW_H
