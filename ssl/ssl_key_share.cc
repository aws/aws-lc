/* Copyright (c) 2015, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include <openssl/ssl.h>

#include <assert.h>
#include <string.h>

#include <utility>

#include <openssl/bn.h>
#include <openssl/bytestring.h>
#include <openssl/curve25519.h>
#include <openssl/ec.h>
#include <openssl/err.h>
#include <openssl/hrss.h>
#include <openssl/mem.h>
#include <openssl/nid.h>
#include <openssl/rand.h>

#include "internal.h"
#include "../crypto/internal.h"
#include "../crypto/kem/internal.h"

BSSL_NAMESPACE_BEGIN

namespace {

class ECKeyShare : public SSLKeyShare {
 public:
  ECKeyShare(int nid, uint16_t group_id) : nid_(nid), group_id_(group_id) {}

  uint16_t GroupID() const override { return group_id_; }

  bool Offer(CBB *out) override {
    assert(!private_key_);
    // Set up a shared |BN_CTX| for all operations.
    UniquePtr<BN_CTX> bn_ctx(BN_CTX_new());
    if (!bn_ctx) {
      return false;
    }
    BN_CTXScope scope(bn_ctx.get());

    // Generate a private key.
    UniquePtr<EC_GROUP> group(EC_GROUP_new_by_curve_name(nid_));
    private_key_.reset(BN_new());
    if (!group || !private_key_ ||
        !BN_rand_range_ex(private_key_.get(), 1,
                          EC_GROUP_get0_order(group.get()))) {
      return false;
    }

    // Compute the corresponding public key and serialize it.
    UniquePtr<EC_POINT> public_key(EC_POINT_new(group.get()));
    if (!public_key ||
        !EC_POINT_mul(group.get(), public_key.get(), private_key_.get(), NULL,
                      NULL, bn_ctx.get()) ||
        !EC_POINT_point2cbb(out, group.get(), public_key.get(),
                            POINT_CONVERSION_UNCOMPRESSED, bn_ctx.get())) {
      return false;
    }

    return true;
  }

  bool Finish(Array<uint8_t> *out_secret, uint8_t *out_alert,
              Span<const uint8_t> peer_key) override {
    assert(private_key_);
    *out_alert = SSL_AD_INTERNAL_ERROR;

    // Set up a shared |BN_CTX| for all operations.
    UniquePtr<BN_CTX> bn_ctx(BN_CTX_new());
    if (!bn_ctx) {
      return false;
    }
    BN_CTXScope scope(bn_ctx.get());

    UniquePtr<EC_GROUP> group(EC_GROUP_new_by_curve_name(nid_));
    if (!group) {
      return false;
    }

    UniquePtr<EC_POINT> peer_point(EC_POINT_new(group.get()));
    UniquePtr<EC_POINT> result(EC_POINT_new(group.get()));
    BIGNUM *x = BN_CTX_get(bn_ctx.get());
    if (!peer_point || !result || !x) {
      return false;
    }

    if (peer_key.empty() || peer_key[0] != POINT_CONVERSION_UNCOMPRESSED ||
        !EC_POINT_oct2point(group.get(), peer_point.get(), peer_key.data(),
                            peer_key.size(), bn_ctx.get())) {
      OPENSSL_PUT_ERROR(SSL, SSL_R_BAD_ECPOINT);
      *out_alert = SSL_AD_DECODE_ERROR;
      return false;
    }

    // Compute the x-coordinate of |peer_key| * |private_key_|.
    if (!EC_POINT_mul(group.get(), result.get(), NULL, peer_point.get(),
                      private_key_.get(), bn_ctx.get()) ||
        !EC_POINT_get_affine_coordinates_GFp(group.get(), result.get(), x, NULL,
                                             bn_ctx.get())) {
      return false;
    }

    // Encode the x-coordinate left-padded with zeros.
    Array<uint8_t> secret;
    if (!secret.Init((EC_GROUP_get_degree(group.get()) + 7) / 8) ||
        !BN_bn2bin_padded(secret.data(), secret.size(), x)) {
      return false;
    }

    *out_secret = std::move(secret);
    return true;
  }

  bool SerializePrivateKey(CBB *out) override {
    assert(private_key_);
    UniquePtr<EC_GROUP> group(EC_GROUP_new_by_curve_name(nid_));
    // Padding is added to avoid leaking the length.
    size_t len = BN_num_bytes(EC_GROUP_get0_order(group.get()));
    return BN_bn2cbb_padded(out, len, private_key_.get());
  }

  bool DeserializePrivateKey(CBS *in) override {
    assert(!private_key_);
    private_key_.reset(BN_bin2bn(CBS_data(in), CBS_len(in), nullptr));
    return private_key_ != nullptr;
  }

 private:
  UniquePtr<BIGNUM> private_key_;
  int nid_;
  uint16_t group_id_;
};

class X25519KeyShare : public SSLKeyShare {
 public:
  X25519KeyShare() {}

  uint16_t GroupID() const override { return SSL_CURVE_X25519; }

  bool Offer(CBB *out) override {
    uint8_t public_key[32];
    X25519_keypair(public_key, private_key_);
    return !!CBB_add_bytes(out, public_key, sizeof(public_key));
  }

  bool Finish(Array<uint8_t> *out_secret, uint8_t *out_alert,
              Span<const uint8_t> peer_key) override {
    *out_alert = SSL_AD_INTERNAL_ERROR;

    Array<uint8_t> secret;
    if (!secret.Init(32)) {
      return false;
    }

    if (peer_key.size() != 32 ||
        !X25519(secret.data(), private_key_, peer_key.data())) {
      *out_alert = SSL_AD_DECODE_ERROR;
      OPENSSL_PUT_ERROR(SSL, SSL_R_BAD_ECPOINT);
      return false;
    }

    *out_secret = std::move(secret);
    return true;
  }

  bool SerializePrivateKey(CBB *out) override {
    return CBB_add_bytes(out, private_key_, sizeof(private_key_));
  }

  bool DeserializePrivateKey(CBS *in) override {
    if (CBS_len(in) != sizeof(private_key_) ||
        !CBS_copy_bytes(in, private_key_, sizeof(private_key_))) {
      return false;
    }
    return true;
  }

 private:
  uint8_t private_key_[32];
};

class CECPQ2KeyShare : public SSLKeyShare {
 public:
  CECPQ2KeyShare() {}

  uint16_t GroupID() const override { return SSL_CURVE_CECPQ2; }

  bool Offer(CBB *out) override {
    uint8_t x25519_public_key[32];
    X25519_keypair(x25519_public_key, x25519_private_key_);

    Array<uint8_t> hrss_entropy;
    if (!hrss_entropy.Init(HRSS_GENERATE_KEY_BYTES)) {
      return false;
    }

    HRSS_public_key hrss_public_key;
    RAND_bytes(hrss_entropy.data(), hrss_entropy.size());
    if (!HRSS_generate_key(&hrss_public_key, &hrss_private_key_,
                           hrss_entropy.data())) {
      return false;
    }

    uint8_t hrss_public_key_bytes[HRSS_PUBLIC_KEY_BYTES];
    HRSS_marshal_public_key(hrss_public_key_bytes, &hrss_public_key);

    if (!CBB_add_bytes(out, x25519_public_key, sizeof(x25519_public_key)) ||
        !CBB_add_bytes(out, hrss_public_key_bytes,
                       sizeof(hrss_public_key_bytes))) {
      return false;
    }

    return true;
  }

  bool Accept(CBB *out_public_key, Array<uint8_t> *out_secret,
              uint8_t *out_alert, Span<const uint8_t> peer_key) override {
    Array<uint8_t> secret;
    if (!secret.Init(32 + HRSS_KEY_BYTES)) {
      return false;
    }

    uint8_t x25519_public_key[32];
    X25519_keypair(x25519_public_key, x25519_private_key_);

    HRSS_public_key peer_public_key;
    if (peer_key.size() != 32 + HRSS_PUBLIC_KEY_BYTES ||
        !HRSS_parse_public_key(&peer_public_key, peer_key.data() + 32) ||
        !X25519(secret.data(), x25519_private_key_, peer_key.data())) {
      *out_alert = SSL_AD_DECODE_ERROR;
      OPENSSL_PUT_ERROR(SSL, SSL_R_BAD_ECPOINT);
      return false;
    }

    Array<uint8_t> entropy;
    if (!entropy.Init(HRSS_ENCAP_BYTES)) {
      return false;
    }

    uint8_t ciphertext[HRSS_CIPHERTEXT_BYTES];
    RAND_bytes(entropy.data(), entropy.size());
    if (!HRSS_encap(ciphertext, secret.data() + 32, &peer_public_key,
                    entropy.data()) ||
        !CBB_add_bytes(out_public_key, x25519_public_key,
                       sizeof(x25519_public_key)) ||
        !CBB_add_bytes(out_public_key, ciphertext, sizeof(ciphertext))) {
      return false;
    }

    *out_secret = std::move(secret);
    return true;
  }

  bool Finish(Array<uint8_t> *out_secret, uint8_t *out_alert,
              Span<const uint8_t> peer_key) override {
    *out_alert = SSL_AD_INTERNAL_ERROR;

    Array<uint8_t> secret;
    if (!secret.Init(32 + HRSS_KEY_BYTES)) {
      return false;
    }

    if (peer_key.size() != 32 + HRSS_CIPHERTEXT_BYTES ||
        !X25519(secret.data(), x25519_private_key_, peer_key.data())) {
      *out_alert = SSL_AD_DECODE_ERROR;
      OPENSSL_PUT_ERROR(SSL, SSL_R_BAD_ECPOINT);
      return false;
    }

    if (!HRSS_decap(secret.data() + 32, &hrss_private_key_,
                    peer_key.data() + 32, peer_key.size() - 32)) {
      return false;
    }

    *out_secret = std::move(secret);
    return true;
  }

 private:
  uint8_t x25519_private_key_[32];
  HRSS_private_key hrss_private_key_;
};

class KEMKeyShare : public SSLKeyShare {
 public:
  KEMKeyShare(int nid, uint16_t group_id) : nid_(nid), group_id_(group_id) {}

  uint16_t GroupID() const override { return group_id_; }

  bool Offer(CBB *out) override {
    // Ensure |out| is valid, has no children, and has been initialized.
    // We check that |out| has no children because otherwise CBB_data()
    // will produce a fatal error by way of assert(cbb->child == NULL).
    if (!out || out->child || !CBB_data(out)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_PASSED_NULL_PARAMETER);
      return false;
    }

    // ctx_ should not have been initialized (by e.g. a previous call
    // to Offer()).
    if (ctx_) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_SHOULD_NOT_HAVE_BEEN_CALLED);
      return false;
    }

    // Initialize the KEM ctx
    ctx_.reset(EVP_PKEY_CTX_new_id(EVP_PKEY_KEM, nullptr));
    if (!ctx_ || !EVP_PKEY_CTX_kem_set_params(ctx_.get(), nid_)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    // Generate a KEM keypair and retrieve the length of the public key
    EVP_PKEY *raw_key = nullptr;
    if (!EVP_PKEY_keygen_init(ctx_.get()) ||
        !EVP_PKEY_keygen(ctx_.get(), &raw_key) ||
        !raw_key ||
        !EVP_PKEY_get_raw_public_key(raw_key, nullptr, &public_key_len_)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    // Retain the private key for decapsulation
    UniquePtr<EVP_PKEY> pkey(raw_key);
    ctx_.reset(EVP_PKEY_CTX_new(pkey.get(), nullptr));
    if (!ctx_) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    // Write the public key to |out|
    Array<uint8_t> public_key;
    if (!public_key.Init(public_key_len_)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return false;
    }

    size_t public_key_bytes_written = public_key_len_;
    if (!EVP_PKEY_get_raw_public_key(pkey.get(), public_key.data(),
                                     &public_key_bytes_written) ||
                                     public_key_bytes_written != public_key_len_ ||
                                     !CBB_add_bytes(out, public_key.data(), public_key_len_)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    return true;
  }

  bool Accept(CBB *out_public_key, Array<uint8_t> *out_secret,
              uint8_t *out_alert, Span<const uint8_t> peer_key) override {
    // Basic nullptr checks
    if (!out_alert) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_PASSED_NULL_PARAMETER);
      return false;
    }

    // Set alert to internal error by default
    *out_alert = SSL_AD_INTERNAL_ERROR;

    if (!out_secret) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_PASSED_NULL_PARAMETER);
      return false;
    }

    // Ensure |out_public_key| is valid, has no children, and has been
    // initialized. We check that |out_public_key| has no children because
    // otherwise CBB_data() will produce a fatal error by way of
    // assert(cbb->child == NULL).
    if (!out_public_key || out_public_key->child || !CBB_data(out_public_key)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_PASSED_NULL_PARAMETER);
      return false;
    }

    // ctx_ should not have been initialized (by e.g. a call to Offer()).
    if (ctx_) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_SHOULD_NOT_HAVE_BEEN_CALLED);
      return false;
    }

    // Ensure that peer_key is valid
    if (!peer_key.data() || peer_key.empty()) {
      *out_alert = SSL_AD_DECODE_ERROR;
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    // Initialize pkey from the received public key
    UniquePtr<EVP_PKEY> pkey(
      EVP_PKEY_kem_new_raw_public_key(nid_, peer_key.begin(), peer_key.size()));

    if (!pkey) {
      *out_alert = SSL_AD_DECODE_ERROR;
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    // Initialize the context with the pkey
    ctx_.reset(EVP_PKEY_CTX_new(pkey.get(), nullptr));
    if (!ctx_) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    // Retrieve the lengths of the ciphertext and shared secret
    if (!EVP_PKEY_encapsulate(ctx_.get(), nullptr, &ciphertext_len_,
                              nullptr, &secret_len_)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    // EVP_PKEY_encapsulate() will generate a shared secret, then encrypt it
    // with the peer's public key. We send the resultant ciphertext to the
    // peer by writing it to |out_public_key|, then...
    Array<uint8_t> ciphertext;
    Array<uint8_t> shared_secret;
    if (!ciphertext.Init(ciphertext_len_) || !shared_secret.Init(secret_len_)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return false;
    }

    size_t ciphertext_bytes_written = ciphertext_len_;
    size_t secret_bytes_written = secret_len_;
    if (!EVP_PKEY_encapsulate(ctx_.get(), ciphertext.data(),
                              &ciphertext_bytes_written, shared_secret.data(),
                              &secret_bytes_written) ||
                              ciphertext_bytes_written != ciphertext_len_ ||
                              secret_bytes_written != secret_len_ ||
                              !CBB_add_bytes(out_public_key, ciphertext.data(), ciphertext_len_)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    // ...we retain the shared secret for our own use.
    *out_secret = std::move(shared_secret);

    // Success; clear the alert
    *out_alert = 0;
    return true;
  }

  bool Finish(Array<uint8_t> *out_secret, uint8_t *out_alert,
              Span<const uint8_t> peer_key) override {
    // Basic nullptr checks
    if (!out_alert) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_PASSED_NULL_PARAMETER);
      return false;
    }

    // Set alert to internal error by default
    *out_alert = SSL_AD_INTERNAL_ERROR;

    if (!out_secret) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_PASSED_NULL_PARAMETER);
      return false;
    }

    // ctx_ should have been initialized by a previous call to Offer()
    if (!ctx_) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_SHOULD_NOT_HAVE_BEEN_CALLED);
      return false;
    }

    // Retrieve the lengths of the ciphertext and shared secret
    if (!EVP_PKEY_encapsulate(ctx_.get(), nullptr, &ciphertext_len_, nullptr,
                              &secret_len_)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    // Ensure that peer_key is valid
    if (!peer_key.data() || peer_key.size() != ciphertext_len_) {
      *out_alert = SSL_AD_DECODE_ERROR;
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    // |peer_key| is the ciphertext, encapsulating the shared secret,
    // that the peer generated using our public key. We use our private
    // key to decapsulate it, and retain the shared secret by writing
    // it to |out_secret|.
    uint8_t *ciphertext = (uint8_t *)peer_key.begin();
    if (!out_secret->Init(secret_len_)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return false;
    }

    size_t secret_bytes_written = secret_len_;
    if (!EVP_PKEY_decapsulate(ctx_.get(), out_secret->data(),
                              &secret_bytes_written, ciphertext,
                              ciphertext_len_) ||
                              secret_bytes_written != secret_len_) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_INTERNAL_ERROR);
      return false;
    }

    // Success; clear the alert
    *out_alert = 0;
    return true;
  }

 private:
  int nid_;
  uint16_t group_id_;
  UniquePtr<EVP_PKEY_CTX> ctx_;
  size_t public_key_len_;
  size_t ciphertext_len_;
  size_t secret_len_;
};

CONSTEXPR_ARRAY NamedGroup kNamedGroups[] = {
    {NID_secp224r1, SSL_CURVE_SECP224R1, "P-224", "secp224r1"},
    {NID_X9_62_prime256v1, SSL_CURVE_SECP256R1, "P-256", "prime256v1"},
    {NID_secp384r1, SSL_CURVE_SECP384R1, "P-384", "secp384r1"},
    {NID_secp521r1, SSL_CURVE_SECP521R1, "P-521", "secp521r1"},
    {NID_X25519, SSL_CURVE_X25519, "X25519", "x25519"},
    {NID_CECPQ2, SSL_CURVE_CECPQ2, "CECPQ2", "CECPQ2"},
};

CONSTEXPR_ARRAY uint16_t kPQGroups[] = {
    SSL_CURVE_CECPQ2,
    SSL_CURVE_KYBER512_R3,
};

}  // namespace

Span<const NamedGroup> NamedGroups() {
  return MakeConstSpan(kNamedGroups, OPENSSL_ARRAY_SIZE(kNamedGroups));
}

Span<const uint16_t> PQGroups() {
  return MakeConstSpan(kPQGroups, OPENSSL_ARRAY_SIZE(kPQGroups));
}

UniquePtr<SSLKeyShare> SSLKeyShare::Create(uint16_t group_id) {
  switch (group_id) {
    case SSL_CURVE_SECP224R1:
      return MakeUnique<ECKeyShare>(NID_secp224r1, SSL_CURVE_SECP224R1);
    case SSL_CURVE_SECP256R1:
      return MakeUnique<ECKeyShare>(NID_X9_62_prime256v1, SSL_CURVE_SECP256R1);
    case SSL_CURVE_SECP384R1:
      return MakeUnique<ECKeyShare>(NID_secp384r1, SSL_CURVE_SECP384R1);
    case SSL_CURVE_SECP521R1:
      return MakeUnique<ECKeyShare>(NID_secp521r1, SSL_CURVE_SECP521R1);
    case SSL_CURVE_X25519:
      return MakeUnique<X25519KeyShare>();
    case SSL_CURVE_CECPQ2:
      return MakeUnique<CECPQ2KeyShare>();
    case SSL_CURVE_KYBER512_R3:
      // Kyber, as a standalone group, is not a NamedGroup; however, we
      // need to create Kyber key shares as part of hybrid groups.
      return MakeUnique<KEMKeyShare>(NID_KYBER512_R3, SSL_CURVE_KYBER512_R3);
    default:
      return nullptr;
  }
}

UniquePtr<SSLKeyShare> SSLKeyShare::Create(CBS *in) {
  uint64_t group;
  CBS private_key;
  if (!CBS_get_asn1_uint64(in, &group) || group > 0xffff ||
      !CBS_get_asn1(in, &private_key, CBS_ASN1_OCTETSTRING)) {
    return nullptr;
  }
  UniquePtr<SSLKeyShare> key_share = Create(static_cast<uint16_t>(group));
  if (!key_share || !key_share->DeserializePrivateKey(&private_key)) {
    return nullptr;
  }
  return key_share;
}

bool SSLKeyShare::Serialize(CBB *out) {
  CBB private_key;
  if (!CBB_add_asn1_uint64(out, GroupID()) ||
      !CBB_add_asn1(out, &private_key, CBS_ASN1_OCTETSTRING) ||
      !SerializePrivateKey(&private_key) ||  //
      !CBB_flush(out)) {
    return false;
  }
  return true;
}

bool SSLKeyShare::Accept(CBB *out_public_key, Array<uint8_t> *out_secret,
                         uint8_t *out_alert, Span<const uint8_t> peer_key) {
  *out_alert = SSL_AD_INTERNAL_ERROR;
  return Offer(out_public_key) &&
         Finish(out_secret, out_alert, peer_key);
}

bool ssl_nid_to_group_id(uint16_t *out_group_id, int nid) {
  for (const auto &group : kNamedGroups) {
    if (group.nid == nid) {
      *out_group_id = group.group_id;
      return true;
    }
  }
  return false;
}

bool ssl_name_to_group_id(uint16_t *out_group_id, const char *name, size_t len) {
  for (const auto &group : kNamedGroups) {
    if (len == strlen(group.name) &&
        !strncmp(group.name, name, len)) {
      *out_group_id = group.group_id;
      return true;
    }
    if (len == strlen(group.alias) &&
        !strncmp(group.alias, name, len)) {
      *out_group_id = group.group_id;
      return true;
    }
  }
  return false;
}

BSSL_NAMESPACE_END

using namespace bssl;

const char* SSL_get_curve_name(uint16_t group_id) {
  for (const auto &group : kNamedGroups) {
    if (group.group_id == group_id) {
      return group.name;
    }
  }
  return nullptr;
}
