/* Copyright (c) 2015, Google Inc.
 *fkdnjlirvnrgbhenftuggfeuvtketg
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
#include <openssl/pq_kem.h>
#include <openssl/mem.h>
#include <openssl/nid.h>
#include <openssl/rand.h>
#include <openssl/pq_kem.h>

#include "internal.h"
#include "../crypto/internal.h"
#include "../crypto/fipsmodule/ec/internal.h"

BSSL_NAMESPACE_BEGIN

namespace {

class ECKeyShare : public SSLKeyShare {
 public:
  ECKeyShare(int nid, uint16_t group_id) : nid_(nid), group_id_(group_id) {}

  uint16_t GroupID() const override { return group_id_; }

  bool KeyShareSizes(uint16_t *out_offer_key_share_size, uint16_t *out_accept_key_share_size) override {
    const struct built_in_curves *const curves = OPENSSL_built_in_curves();
    for (size_t i = 0; i < OPENSSL_NUM_BUILT_IN_CURVES; i++) {
      const struct built_in_curve *curve = &curves->curves[i];
      if (nid_ == curve->nid) {
        // As per https://datatracker.ietf.org/doc/html/rfc8446#section-4.2.8.2, an EC share has the form:
        // uint8 legacy_form
        // uint8_t x_coordinate[param_len]
        // uint8_t y_coordinate[param_len]
        *out_offer_key_share_size = ((2 * curve->param_len) + 1);
        *out_accept_key_share_size = ((2 * curve->param_len) + 1);
        return true;
      }
    }
    return false;
  }

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

  bool KeyShareSizes(uint16_t *out_offer_key_share_size, uint16_t *out_accept_key_share_size) override {
    *out_offer_key_share_size = 32;
    *out_accept_key_share_size = 32;
    return true;
  }

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
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
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

  bool KeyShareSizes(uint16_t *out_offer_key_share_size, uint16_t *out_accept_key_share_size) override {
    // X25519's share size is 32 bytes
    *out_offer_key_share_size = 32 + HRSS_PUBLIC_KEY_BYTES;
    *out_accept_key_share_size = 32 + HRSS_CIPHERTEXT_BYTES;
    return true;
  }

  bool Offer(CBB *out) override {
    uint8_t x25519_public_key[32];
    X25519_keypair(x25519_public_key, x25519_private_key_);

    uint8_t hrss_entropy[HRSS_GENERATE_KEY_BYTES];
    HRSS_public_key hrss_public_key;
    RAND_bytes(hrss_entropy, sizeof(hrss_entropy));
    if (!HRSS_generate_key(&hrss_public_key, &hrss_private_key_,
                           hrss_entropy)) {
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
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
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

    uint8_t ciphertext[HRSS_CIPHERTEXT_BYTES];
    uint8_t entropy[HRSS_ENCAP_BYTES];
    RAND_bytes(entropy, sizeof(entropy));

    if (!HRSS_encap(ciphertext, secret.data() + 32, &peer_public_key,
                    entropy) ||
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
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
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

class PQKeyShare : public SSLKeyShare {
 public:
  PQKeyShare(int nid, uint16_t group_id) : nid_(nid), group_id_(group_id) {}

  uint16_t GroupID() const override { return group_id_; }

  bool KeyShareSizes(uint16_t *out_offer_key_share_size, uint16_t *out_accept_key_share_size) override {
    EVP_PQ_KEM_CTX *kem_ctx = EVP_PQ_KEM_CTX_new();
    if (!EVP_PQ_KEM_CTX_init_by_nid(kem_ctx, nid_)) {
      return false;
    }
    *out_offer_key_share_size = kem_ctx->kem->public_key_length;
    *out_accept_key_share_size = kem_ctx->kem->ciphertext_length;
    EVP_PQ_KEM_CTX_free(kem_ctx);
    return true;
  }

  bool Offer(CBB *out) override {
    assert(!pq_kem_ctx_);
    pq_kem_ctx_ = EVP_PQ_KEM_CTX_new();
    if (!EVP_PQ_KEM_CTX_init_by_nid(pq_kem_ctx_, nid_) ||
        !EVP_PQ_KEM_generate_keypair(pq_kem_ctx_) ||
        !CBB_add_bytes(out, pq_kem_ctx_->public_key, pq_kem_ctx_->kem->public_key_length)) {
      return false;
    }

    return true;
  }

  bool Accept(CBB *out_public_key, Array<uint8_t> *out_secret, uint8_t *out_alert, Span<const uint8_t> peer_key) override {
    assert(!pq_kem_ctx_);
    pq_kem_ctx_ = EVP_PQ_KEM_CTX_new();
    if (!EVP_PQ_KEM_CTX_init_by_nid(pq_kem_ctx_, nid_)) {
      return false;
    }

    // EVP_PQ_KEM_encapsulate() expects the public key to be written in pq_kem_ctx_;
    // copy it, perform the encapsulation, and write the ciphertext to *out_public_key
    if (peer_key.size() != pq_kem_ctx_->kem->public_key_length) {
      return false;
    }
    OPENSSL_memcpy(pq_kem_ctx_->public_key, peer_key.data(), pq_kem_ctx_->kem->public_key_length);
    if (!EVP_PQ_KEM_encapsulate(pq_kem_ctx_) ||
        !CBB_add_bytes(out_public_key, pq_kem_ctx_->ciphertext, pq_kem_ctx_->kem->ciphertext_length)) {
      return false;
    }

    // Copy the shared secret to *out_secret and free the PQ KEM context since it's no longer needed
    if (!out_secret ||
        !out_secret->Init(pq_kem_ctx_->kem->shared_secret_length)) {
      return false;
    }
    OPENSSL_memcpy(out_secret->data(), pq_kem_ctx_->shared_secret, pq_kem_ctx_->kem->shared_secret_length);
    EVP_PQ_KEM_CTX_free(pq_kem_ctx_);

    return true;
  }

  bool Finish(Array<uint8_t> *out_secret, uint8_t *out_alert, Span<const uint8_t> peer_key) override {
    assert(pq_kem_ctx_);

    // EVP_PQ_KEM_decapsulate() expects the ciphertext to be written in pq_kem_ctx_;
    // copy it, perform the decapsulation, and write the shared secret to *out_secret
    if (peer_key.size() != pq_kem_ctx_->kem->ciphertext_length) {
      return false;
    }
    OPENSSL_memcpy(pq_kem_ctx_->ciphertext, peer_key.data(),pq_kem_ctx_->kem->ciphertext_length);

    if (!out_secret ||
        !out_secret->Init(pq_kem_ctx_->kem->shared_secret_length)) {
      return false;
    }
    OPENSSL_memcpy(out_secret->data(), pq_kem_ctx_->shared_secret, pq_kem_ctx_->kem->shared_secret_length);
    EVP_PQ_KEM_CTX_free(pq_kem_ctx_);

    return true;
  }

 private:
  int nid_;
  uint16_t group_id_;
  EVP_PQ_KEM_CTX *pq_kem_ctx_;
};

// HybridKeyShare is implemented according to:
// https://datatracker.ietf.org/doc/html/draft-ietf-tls-hybrid-design.
class HybridKeyShare : public SSLKeyShare {
 public:
  HybridKeyShare(uint16_t group_id) : group_id_(group_id) {
    for (size_t i = 0; i < NUM_HYBRID_COMPONENTS; i++) {
      key_shares_[i] = nullptr;
    }
  }

  uint16_t GroupID() const override { return group_id_; }

  bool KeyShareSizes(uint16_t *out_offer_key_share_size, uint16_t *out_accept_key_share_size) override {
    *out_offer_key_share_size = 0;
    *out_accept_key_share_size = 0;

    for (size_t i = 0; i < NUM_HYBRID_COMPONENTS; i++) {
      if (!key_shares_[i]) {
        return false;
      }

      uint16_t component_offer_size;
      uint16_t component_accept_size;
      if (!key_shares_[i]->KeyShareSizes(&component_offer_size, &component_accept_size)) {
        return false;
      }
      *out_offer_key_share_size += component_offer_size;
      *out_accept_key_share_size += component_accept_size;
    }

    return true;
  }

  bool Offer(CBB *out) override {
    // TODO INIT()

    // Perform each key exchange's Offer() and concatenate each public key
    for (size_t i = 0; i < NUM_HYBRID_COMPONENTS; i++) {
      if (!key_shares_[i]->Offer(out)) {
        return false;
      }
    }

    return true;
  }

  bool Accept(CBB *out_public_key, Array<uint8_t> *out_secret, uint8_t *out_alert, Span<const uint8_t> peer_key) override {
    // TODO INIT()

    Array<uint8_t> *component_secrets[NUM_HYBRID_COMPONENTS];
    size_t span_index = 0;
    size_t total_secret_size = 0;

    for (size_t i = 0; i < NUM_HYBRID_COMPONENTS; i++) {
      // |peer_key| is the concatenation of all key shares produced by the peer's Offer function.
      // We split |peer_key| into each key share and perform that key exchange's Accept.
      uint16_t component_offer_size;
      uint16_t component_accept_size;
      if (!key_shares_[i]->KeyShareSizes(&component_offer_size, &component_accept_size)) {
        return false;
      }

      Span<const uint8_t> component_peer_key = peer_key.subspan(span_index, component_offer_size);
      span_index += component_offer_size;
      if (!key_shares_[i]->Accept(out_public_key, component_secrets[i], out_alert, component_peer_key)) {
        return false;
      }

      total_secret_size += component_secrets[i]->size();
    }

    // Concatenate + copy the component secrets to |out_secret| to form the hybrid shared secret
    if (!out_secret ||
        !out_secret->Init(total_secret_size)) {
      return false;
    }

    size_t secret_index = 0;
    for (size_t i = 0; i < NUM_HYBRID_COMPONENTS; i++) {
      OPENSSL_memcpy(out_secret->data() + secret_index, component_secrets[i]->data(), component_secrets[i]->size());
      secret_index += component_secrets[i]->size();
    }

    return true;
  }

  bool Finish(Array<uint8_t> *out_secret, uint8_t *out_alert, Span<const uint8_t> peer_key) override {
    // key_shares_ must have been initialized by a previous call to Offer()
    for (size_t i = 0; i < NUM_HYBRID_COMPONENTS; i++) {
      if (!key_shares_[i]) {
        return false;
      }
    }

    Array<uint8_t> *component_secrets[NUM_HYBRID_COMPONENTS];
    size_t span_index = 0;
    size_t total_secret_size = 0;

    for (size_t i = 0; i < NUM_HYBRID_COMPONENTS; i++) {
      // |peer_key| is the concatenation of all key shares produced by the peer's Accept function.
      // We split |peer_key| into each key share and perform that key exchange's Finish.
      uint16_t component_offer_size;
      uint16_t component_accept_size;
      if (!key_shares_[i]->KeyShareSizes(&component_offer_size, &component_accept_size)) {
        return false;
      }

      Span<const uint8_t> component_peer_key = peer_key.subspan(span_index, component_accept_size);
      span_index += component_accept_size;
      if (!key_shares_[i]->Finish(component_secrets[i], out_alert, component_peer_key)) {
        return false;
      }

      total_secret_size += component_secrets[i]->size();
    }

    // Concatenate + copy the component secrets to |out_secret| to form the hybrid shared secret
    if (!out_secret ||
        !out_secret->Init(total_secret_size)) {
      return false;
    }

    size_t secret_index = 0;
    for (size_t i = 0; i < NUM_HYBRID_COMPONENTS; i++) {
      OPENSSL_memcpy(out_secret->data() + secret_index, component_secrets[i]->data(), component_secrets[i]->size());
      secret_index += component_secrets[i]->size();
    }

    return true;
  }

 private:
  bool Init() {
    for (const HybridGroup &group : HybridGroups()) {
      if (group_id_ == group.group_id) {
        for (size_t i = 0; i < NUM_HYBRID_COMPONENTS; i++) {
          key_shares_[i] = SSLKeyShare::Create(group.component_group_ids[i]);
        }
        return true;
      }
    }
    return false;
  }

  uint16_t group_id_;
  UniquePtr<SSLKeyShare> key_shares_[NUM_HYBRID_COMPONENTS];
};

CONSTEXPR_ARRAY NamedGroup kNamedGroups[] = {
    {NID_secp224r1, SSL_CURVE_SECP224R1, "P-224", "secp224r1"},
    {NID_X9_62_prime256v1, SSL_CURVE_SECP256R1, "P-256", "prime256v1"},
    {NID_secp384r1, SSL_CURVE_SECP384R1, "P-384", "secp384r1"},
    {NID_secp521r1, SSL_CURVE_SECP521R1, "P-521", "secp521r1"},
    {NID_X25519, SSL_CURVE_X25519, "X25519", "x25519"},
    {NID_CECPQ2, SSL_CURVE_CECPQ2, "CECPQ2", "CECPQ2"},
    {NID_X25519_KYBER512, SSL_CURVE_X25519_KYBER512, "X25519_Kyber512", "x25519_kyber512"},
    {NID_SECP256R1_KYBER512, SSL_CURVE_SECP256R1_KYBER512, "P-256_Kyber512", "prime256v1_kyber512"},
};

CONSTEXPR_ARRAY HybridGroup kHybridGroups[] = {
    {SSL_CURVE_X25519_KYBER512, {NID_X25519, NID_KYBER512}},
    {SSL_CURVE_SECP256R1_KYBER512, {NID_X9_62_prime256v1, NID_KYBER512}},
};

}  // namespace

Span<const NamedGroup> NamedGroups() {
  return MakeConstSpan(kNamedGroups, OPENSSL_ARRAY_SIZE(kNamedGroups));
}

Span<const HybridGroup> HybridGroups() {
  return MakeConstSpan(kHybridGroups, OPENSSL_ARRAY_SIZE(kHybridGroups));
}

UniquePtr<SSLKeyShare> SSLKeyShare::Create(uint16_t group_id) {
  switch (group_id) {
    case SSL_CURVE_SECP224R1:
      return UniquePtr<SSLKeyShare>(
          New<ECKeyShare>(NID_secp224r1, SSL_CURVE_SECP224R1));
    case SSL_CURVE_SECP256R1:
      return UniquePtr<SSLKeyShare>(
          New<ECKeyShare>(NID_X9_62_prime256v1, SSL_CURVE_SECP256R1));
    case SSL_CURVE_SECP384R1:
      return UniquePtr<SSLKeyShare>(
          New<ECKeyShare>(NID_secp384r1, SSL_CURVE_SECP384R1));
    case SSL_CURVE_SECP521R1:
      return UniquePtr<SSLKeyShare>(
          New<ECKeyShare>(NID_secp521r1, SSL_CURVE_SECP521R1));
    case SSL_CURVE_X25519:
      return UniquePtr<SSLKeyShare>(New<X25519KeyShare>());
    case SSL_CURVE_CECPQ2:
      return UniquePtr<SSLKeyShare>(New<CECPQ2KeyShare>());
    case SSL_CURVE_X25519_KYBER512:
      return UniquePtr<SSLKeyShare>(New<HybridKeyShare>(SSL_CURVE_X25519_KYBER512));
    case SSL_CURVE_SECP256R1_KYBER512:
      return UniquePtr<SSLKeyShare>(New<HybridKeyShare>(SSL_CURVE_SECP256R1_KYBER512));
    case SSL_CURVE_KYBER512:
      return UniquePtr<SSLKeyShare>(New<PQKeyShare>(NID_KYBER512, SSL_CURVE_KYBER512));
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
      !SerializePrivateKey(&private_key) ||
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
