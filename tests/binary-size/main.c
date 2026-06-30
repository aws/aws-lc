// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
//
// Minimal AWS-LC consumer used by the OPENSSL_SMALL binary-size CI check
// (.github/workflows/openssl-small.yml). It links libcrypto statically and
// exercises a representative TLS-ish crypto surface (SHA-256, AES-256-GCM,
// ECDSA P-256, X25519, Ed25519) so the linker pulls in real code paths. The
// workflow builds this twice -- against a default libcrypto and against one
// built with OPENSSL_SMALL -- and compares the resulting binary sizes.
//
// It is intentionally small and standalone (compiled directly by the workflow,
// not part of the main CMake build).

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <openssl/aead.h>
#include <openssl/curve25519.h>
#include <openssl/ec_key.h>
#include <openssl/ecdsa.h>
#include <openssl/nid.h>
#include <openssl/sha.h>

static int do_sha256(void) {
  uint8_t in[64], out[SHA256_DIGEST_LENGTH];
  memset(in, 7, sizeof(in));
  return SHA256(in, sizeof(in), out) != NULL;
}

static int do_aes_256_gcm(void) {
  uint8_t key[32] = {0}, nonce[12] = {0}, in[32] = {0}, out[64];
  size_t out_len = 0;
  EVP_AEAD_CTX *ctx = EVP_AEAD_CTX_new(EVP_aead_aes_256_gcm(), key, sizeof(key),
                                       EVP_AEAD_DEFAULT_TAG_LENGTH);
  if (ctx == NULL) {
    return 0;
  }
  int ok = EVP_AEAD_CTX_seal(ctx, out, &out_len, sizeof(out), nonce,
                             sizeof(nonce), in, sizeof(in), NULL, 0);
  EVP_AEAD_CTX_free(ctx);
  return ok && out_len > 0;
}

static int do_ecdsa_p256(void) {
  EC_KEY *key = EC_KEY_new_by_curve_name(NID_X9_62_prime256v1);
  if (key == NULL) {
    return 0;
  }
  uint8_t digest[32] = {1}, sig[256];
  unsigned int sig_len = sizeof(sig);
  int ok = EC_KEY_generate_key(key) &&
           ECDSA_sign(0, digest, sizeof(digest), sig, &sig_len, key) &&
           ECDSA_verify(0, digest, sizeof(digest), sig, sig_len, key);
  EC_KEY_free(key);
  return ok;
}

static int do_x25519(void) {
  uint8_t our_public[32], our_private[32], peer_public[32] = {9}, shared[32];
  X25519_keypair(our_public, our_private);
  return X25519(shared, our_private, peer_public);
}

static int do_ed25519(void) {
  uint8_t public_key[32], private_key[64], sig[64];
  static const uint8_t msg[] = "aws-lc OPENSSL_SMALL binary-size check";
  ED25519_keypair(public_key, private_key);
  ED25519_sign(sig, msg, sizeof(msg), private_key);
  return ED25519_verify(msg, sizeof(msg), sig, public_key);
}

int main(void) {
  if (!do_sha256() || !do_aes_256_gcm() || !do_ecdsa_p256() || !do_x25519() ||
      !do_ed25519()) {
    fprintf(stderr, "crypto self-check failed\n");
    return 1;
  }
  printf("ok\n");
  return 0;
}
