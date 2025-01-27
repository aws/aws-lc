// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_CURVE25519_EXTRA_INTERNAL_H
#define OPENSSL_HEADER_CURVE25519_EXTRA_INTERNAL_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <openssl/base.h>
#include <openssl/curve25519.h>

int ED25519ctx_sign_no_self_test(
    uint8_t out_sig[ED25519_SIGNATURE_LEN],
    const uint8_t *message, size_t message_len,
    const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len);

int ED25519ctx_verify_no_self_test(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
    const uint8_t *context, size_t context_len);

int ED25519ph_sign_no_self_test(
    uint8_t out_sig[ED25519_SIGNATURE_LEN],
    const uint8_t *message, size_t message_len,
    const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len);

int ED25519ph_sign_digest_no_self_test(
    uint8_t out_sig[ED25519_SIGNATURE_LEN],
    const uint8_t digest[SHA512_DIGEST_LENGTH],
    const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len);

int ED25519ph_verify_no_self_test(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
    const uint8_t *context, size_t context_len);

int ED25519ph_verify_digest_no_self_test(
    const uint8_t digest[SHA512_DIGEST_LENGTH],
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
    const uint8_t *context, size_t context_len);

#if defined(__cplusplus)
}
#endif

#endif  // OPENSSL_HEADER_CURVE25519_EXTRA_INTERNAL_H
