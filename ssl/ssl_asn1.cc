/* Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com)
 * All rights reserved.
 *
 * This package is an SSL implementation written
 * by Eric Young (eay@cryptsoft.com).
 * The implementation was written so as to conform with Netscapes SSL.
 *
 * This library is free for commercial and non-commercial use as long as
 * the following conditions are aheared to.  The following conditions
 * apply to all code found in this distribution, be it the RC4, RSA,
 * lhash, DES, etc., code; not just the SSL code.  The SSL documentation
 * included with this distribution is covered by the same copyright terms
 * except that the holder is Tim Hudson (tjh@cryptsoft.com).
 *
 * Copyright remains Eric Young's, and as such any Copyright notices in
 * the code are not to be removed.
 * If this package is used in a product, Eric Young should be given attribution
 * as the author of the parts of the library used.
 * This can be in the form of a textual message at program startup or
 * in documentation (online or textual) provided with the package.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    "This product includes cryptographic software written by
 *     Eric Young (eay@cryptsoft.com)"
 *    The word 'cryptographic' can be left out if the rouines from the library
 *    being used are not cryptographic related :-).
 * 4. If you include any Windows specific code (or a derivative thereof) from
 *    the apps directory (application code) you must include an acknowledgement:
 *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
 *
 * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * The licence and distribution terms for any publically available version or
 * derivative of this code cannot be changed.  i.e. this code cannot simply be
 * copied and put under another distribution licence
 * [including the GNU Public Licence.]
 */
/* ====================================================================
 * Copyright 2005 Nokia. All rights reserved.
 *
 * The portions of the attached software ("Contribution") is developed by
 * Nokia Corporation and is licensed pursuant to the OpenSSL open source
 * license.
 *
 * The Contribution, originally written by Mika Kousa and Pasi Eronen of
 * Nokia Corporation, consists of the "PSK" (Pre-Shared Key) ciphersuites
 * support (see RFC 4279) to OpenSSL.
 *
 * No patent licenses or other rights except those expressly stated in
 * the OpenSSL open source license shall be deemed granted or received
 * expressly, by implication, estoppel, or otherwise.
 *
 * No assurances are provided by Nokia that the Contribution does not
 * infringe the patent or other intellectual property rights of any third
 * party or that the license provides you with all the necessary rights
 * to make use of the Contribution.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND. IN
 * ADDITION TO THE DISCLAIMERS INCLUDED IN THE LICENSE, NOKIA
 * SPECIFICALLY DISCLAIMS ANY LIABILITY FOR CLAIMS BROUGHT BY YOU OR ANY
 * OTHER ENTITY BASED ON INFRINGEMENT OF INTELLECTUAL PROPERTY RIGHTS OR
 * OTHERWISE. */

#include <openssl/ssl.h>

#include <limits.h>
#include <string.h>

#include <utility>

#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/x509.h>

#include "../crypto/internal.h"
#include "internal.h"


BSSL_NAMESPACE_BEGIN

// An SSL_SESSION is serialized as the following ASN.1 structure:
//
// SSLSession ::= SEQUENCE {
//     version                     INTEGER (1),  -- session structure version
//     sslVersion                  INTEGER,      -- protocol version number
//     cipher                      OCTET STRING, -- two bytes long
//     sessionID                   OCTET STRING,
//     secret                      OCTET STRING,
//     time                    [1] INTEGER, -- seconds since UNIX epoch
//     timeout                 [2] INTEGER, -- in seconds
//     peer                    [3] Certificate OPTIONAL,
//     sessionIDContext        [4] OCTET STRING OPTIONAL,
//     verifyResult            [5] INTEGER OPTIONAL,  -- one of X509_V_* codes
//     pskIdentity             [8] OCTET STRING OPTIONAL,
//     ticketLifetimeHint      [9] INTEGER OPTIONAL,       -- client-only
//     ticket                  [10] OCTET STRING OPTIONAL, -- client-only
//     peerSHA256              [13] OCTET STRING OPTIONAL,
//     originalHandshakeHash   [14] OCTET STRING OPTIONAL,
//     signedCertTimestampList [15] OCTET STRING OPTIONAL,
//                                  -- contents of SCT extension
//     ocspResponse            [16] OCTET STRING OPTIONAL,
//                                  -- stapled OCSP response from the server
//     extendedMasterSecret    [17] BOOLEAN OPTIONAL,
//     groupID                 [18] INTEGER OPTIONAL,
//     certChain               [19] SEQUENCE OF Certificate OPTIONAL,
//     ticketAgeAdd            [21] OCTET STRING OPTIONAL,
//     isServer                [22] BOOLEAN DEFAULT TRUE,
//     peerSignatureAlgorithm  [23] INTEGER OPTIONAL,
//     ticketMaxEarlyData      [24] INTEGER OPTIONAL,
//     authTimeout             [25] INTEGER OPTIONAL, -- defaults to timeout
//     earlyALPN               [26] OCTET STRING OPTIONAL,
//     isQuic                  [27] BOOLEAN OPTIONAL,
//     quicEarlyDataHash       [28] OCTET STRING OPTIONAL,
//     localALPS               [29] OCTET STRING OPTIONAL,
//     peerALPS                [30] OCTET STRING OPTIONAL,
//     -- Either both or none of localALPS and peerALPS must be present. If both
//     -- are present, earlyALPN must be present and non-empty.
// }
//
// Note: historically this serialization has included other optional
// fields. Their presence is currently treated as a parse error, except for
// hostName, which is ignored.
//
//     keyArg                  [0] IMPLICIT OCTET STRING OPTIONAL,
//     hostName                [6] OCTET STRING OPTIONAL,
//     pskIdentityHint         [7] OCTET STRING OPTIONAL,
//     compressionMethod       [11] OCTET STRING OPTIONAL,
//     srpUsername             [12] OCTET STRING OPTIONAL,
//     ticketFlags             [20] INTEGER OPTIONAL,

static const unsigned kVersion = 1;

static const unsigned kTimeTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 1;
static const unsigned kTimeoutTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 2;
static const unsigned kPeerTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 3;
static const unsigned kSessionIDContextTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 4;
static const unsigned kVerifyResultTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 5;
static const unsigned kHostNameTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 6;
static const unsigned kPSKIdentityTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 8;
static const unsigned kTicketLifetimeHintTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 9;
static const unsigned kTicketTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 10;
static const unsigned kPeerSHA256Tag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 13;
static const unsigned kOriginalHandshakeHashTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 14;
static const unsigned kSignedCertTimestampListTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 15;
static const unsigned kOCSPResponseTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 16;
static const unsigned kExtendedMasterSecretTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 17;
static const unsigned kGroupIDTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 18;
static const unsigned kCertChainTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 19;
static const unsigned kTicketAgeAddTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 21;
static const unsigned kIsServerTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 22;
static const unsigned kPeerSignatureAlgorithmTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 23;
static const unsigned kTicketMaxEarlyDataTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 24;
static const unsigned kAuthTimeoutTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 25;
static const unsigned kEarlyALPNTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 26;
static const unsigned kIsQuicTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 27;
static const unsigned kQuicEarlyDataContextTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 28;
static const unsigned kLocalALPSTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 29;
static const unsigned kPeerALPSTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 30;

static int SSL_SESSION_to_bytes_full(const SSL_SESSION *in, CBB *cbb,
                                     int for_ticket) {
  if (in == NULL || in->cipher == NULL) {
    return 0;
  }

  CBB session, child, child2;
  if (!CBB_add_asn1(cbb, &session, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1_uint64(&session, kVersion) ||
      !CBB_add_asn1_uint64(&session, in->ssl_version) ||
      !CBB_add_asn1(&session, &child, CBS_ASN1_OCTETSTRING) ||
      !CBB_add_u16(&child, (uint16_t)(in->cipher->id & 0xffff)) ||
      // The session ID is irrelevant for a session ticket.
      !CBB_add_asn1_octet_string(&session, in->session_id,
                                 for_ticket ? 0 : in->session_id_length) ||
      !CBB_add_asn1_octet_string(&session, in->secret, in->secret_length) ||
      !CBB_add_asn1(&session, &child, kTimeTag) ||
      !CBB_add_asn1_uint64(&child, in->time) ||
      !CBB_add_asn1(&session, &child, kTimeoutTag) ||
      !CBB_add_asn1_uint64(&child, in->timeout)) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  // The peer certificate is only serialized if the SHA-256 isn't
  // serialized instead.
  if (sk_CRYPTO_BUFFER_num(in->certs.get()) > 0 && !in->peer_sha256_valid) {
    const CRYPTO_BUFFER *buffer = sk_CRYPTO_BUFFER_value(in->certs.get(), 0);
    if (!CBB_add_asn1(&session, &child, kPeerTag) ||
        !CBB_add_bytes(&child, CRYPTO_BUFFER_data(buffer),
                       CRYPTO_BUFFER_len(buffer))) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  // Although it is OPTIONAL and usually empty, OpenSSL has
  // historically always encoded the sid_ctx.
  if (!CBB_add_asn1(&session, &child, kSessionIDContextTag) ||
      !CBB_add_asn1_octet_string(&child, in->sid_ctx, in->sid_ctx_length)) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  if (in->verify_result != X509_V_OK) {
    if (!CBB_add_asn1(&session, &child, kVerifyResultTag) ||
        !CBB_add_asn1_uint64(&child, in->verify_result)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->psk_identity) {
    if (!CBB_add_asn1(&session, &child, kPSKIdentityTag) ||
        !CBB_add_asn1_octet_string(&child,
                                   (const uint8_t *)in->psk_identity.get(),
                                   strlen(in->psk_identity.get()))) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->ticket_lifetime_hint > 0) {
    if (!CBB_add_asn1(&session, &child, kTicketLifetimeHintTag) ||
        !CBB_add_asn1_uint64(&child, in->ticket_lifetime_hint)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (!in->ticket.empty() && !for_ticket) {
    if (!CBB_add_asn1(&session, &child, kTicketTag) ||
        !CBB_add_asn1_octet_string(&child, in->ticket.data(),
                                   in->ticket.size())) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->peer_sha256_valid) {
    if (!CBB_add_asn1(&session, &child, kPeerSHA256Tag) ||
        !CBB_add_asn1_octet_string(&child, in->peer_sha256,
                                   sizeof(in->peer_sha256))) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->original_handshake_hash_len > 0) {
    if (!CBB_add_asn1(&session, &child, kOriginalHandshakeHashTag) ||
        !CBB_add_asn1_octet_string(&child, in->original_handshake_hash,
                                   in->original_handshake_hash_len)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->signed_cert_timestamp_list != nullptr) {
    if (!CBB_add_asn1(&session, &child, kSignedCertTimestampListTag) ||
        !CBB_add_asn1_octet_string(
            &child, CRYPTO_BUFFER_data(in->signed_cert_timestamp_list.get()),
            CRYPTO_BUFFER_len(in->signed_cert_timestamp_list.get()))) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->ocsp_response != nullptr) {
    if (!CBB_add_asn1(&session, &child, kOCSPResponseTag) ||
        !CBB_add_asn1_octet_string(
            &child, CRYPTO_BUFFER_data(in->ocsp_response.get()),
            CRYPTO_BUFFER_len(in->ocsp_response.get()))) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->extended_master_secret) {
    if (!CBB_add_asn1(&session, &child, kExtendedMasterSecretTag) ||
        !CBB_add_asn1_bool(&child, true)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->group_id > 0 &&
      (!CBB_add_asn1(&session, &child, kGroupIDTag) ||
       !CBB_add_asn1_uint64(&child, in->group_id))) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  // The certificate chain is only serialized if the leaf's SHA-256 isn't
  // serialized instead.
  if (in->certs != NULL &&
      !in->peer_sha256_valid &&
      sk_CRYPTO_BUFFER_num(in->certs.get()) >= 2) {
    if (!CBB_add_asn1(&session, &child, kCertChainTag)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
    for (size_t i = 1; i < sk_CRYPTO_BUFFER_num(in->certs.get()); i++) {
      const CRYPTO_BUFFER *buffer = sk_CRYPTO_BUFFER_value(in->certs.get(), i);
      if (!CBB_add_bytes(&child, CRYPTO_BUFFER_data(buffer),
                         CRYPTO_BUFFER_len(buffer))) {
        OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
        return 0;
      }
    }
  }

  if (in->ticket_age_add_valid) {
    if (!CBB_add_asn1(&session, &child, kTicketAgeAddTag) ||
        !CBB_add_asn1(&child, &child2, CBS_ASN1_OCTETSTRING) ||
        !CBB_add_u32(&child2, in->ticket_age_add)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (!in->is_server) {
    if (!CBB_add_asn1(&session, &child, kIsServerTag) ||
        !CBB_add_asn1_bool(&child, false)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->peer_signature_algorithm != 0 &&
      (!CBB_add_asn1(&session, &child, kPeerSignatureAlgorithmTag) ||
       !CBB_add_asn1_uint64(&child, in->peer_signature_algorithm))) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  if (in->ticket_max_early_data != 0 &&
      (!CBB_add_asn1(&session, &child, kTicketMaxEarlyDataTag) ||
       !CBB_add_asn1_uint64(&child, in->ticket_max_early_data))) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  if (in->timeout != in->auth_timeout &&
      (!CBB_add_asn1(&session, &child, kAuthTimeoutTag) ||
       !CBB_add_asn1_uint64(&child, in->auth_timeout))) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  if (!in->early_alpn.empty()) {
    if (!CBB_add_asn1(&session, &child, kEarlyALPNTag) ||
        !CBB_add_asn1_octet_string(&child, in->early_alpn.data(),
                                   in->early_alpn.size())) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->is_quic) {
    if (!CBB_add_asn1(&session, &child, kIsQuicTag) ||
        !CBB_add_asn1_bool(&child, true)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (!in->quic_early_data_context.empty()) {
    if (!CBB_add_asn1(&session, &child, kQuicEarlyDataContextTag) ||
        !CBB_add_asn1_octet_string(&child, in->quic_early_data_context.data(),
                                   in->quic_early_data_context.size())) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->has_application_settings) {
    if (!CBB_add_asn1(&session, &child, kLocalALPSTag) ||
        !CBB_add_asn1_octet_string(&child,
                                   in->local_application_settings.data(),
                                   in->local_application_settings.size()) ||
        !CBB_add_asn1(&session, &child, kPeerALPSTag) ||
        !CBB_add_asn1_octet_string(&child, in->peer_application_settings.data(),
                                   in->peer_application_settings.size())) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  return CBB_flush(cbb);
}

// parse_optional_string gets an optional ASN.1 OCTET STRING explicitly
// tagged with |tag| from |cbs| and saves it in |*out|. If the element was not
// found, it sets |*out| to NULL. It returns one on success, whether or not the
// element was found, and zero on decode error.
static int parse_optional_string(CBS *cbs, UniquePtr<char> *out, unsigned tag, int reason) {
  CBS value;
  int present;
  if (!CBS_get_optional_asn1_octet_string(cbs, &value, &present, tag)) {
    OPENSSL_PUT_ERROR(SSL, reason);
    return 0;
  }
  if (present) {
    if (CBS_contains_zero_byte(&value)) {
      OPENSSL_PUT_ERROR(SSL, reason);
      return 0;
    }
    char *raw = nullptr;
    if (!CBS_strdup(&value, &raw)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
    out->reset(raw);
  } else {
    out->reset();
  }
  return 1;
}

static int SSL_SESSION_parse_string(CBS *cbs, UniquePtr<char> *out, unsigned tag) {
  return parse_optional_string(cbs, out, tag, SSL_R_INVALID_SSL_SESSION);
}

// SSL_SESSION_parse_octet_string gets an optional ASN.1 OCTET STRING explicitly
// tagged with |tag| from |cbs| and stows it in |*out|. It returns one on
// success, whether or not the element was found, and zero on decode error.
static bool SSL_SESSION_parse_octet_string(CBS *cbs, Array<uint8_t> *out,
                                           unsigned tag) {
  CBS value;
  if (!CBS_get_optional_asn1_octet_string(cbs, &value, NULL, tag)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return false;
  }
  return out->CopyFrom(value);
}

// SSL3_STATE_parse_octet_string is duplicate of |SSL_SESSION_parse_octet_string|.
// SSL3_STATE_parse_octet_string gets an optional ASN.1 OCTET STRING explicitly
// tagged with |tag| from |cbs| and stows it in |*out|. It returns one on
// success, whether or not the element was found, and zero on decode error.
static bool SSL3_STATE_parse_octet_string(CBS *cbs, Array<uint8_t> *out,
                                           unsigned tag) {
  CBS value;
  if (!CBS_get_optional_asn1_octet_string(cbs, &value, NULL, tag)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL3_STATE);
    return false;
  }
  return out->CopyFrom(value);
}

static bool SSL3_STATE_get_optional_octet_string(CBS *cbs, void *dst, unsigned tag, size_t target_len) {
  int present;
  CBS value;
  if (!CBS_get_optional_asn1_octet_string(cbs, &value, &present, tag)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL3_STATE);
    return false;
  }
  if (!present) {
    return true;
  }
  size_t data_len = CBS_len(&value);
  if (target_len > 0 && data_len != target_len) {
    return false;
  }
  OPENSSL_memcpy(dst, CBS_data(&value), data_len);
  return true;
}

static int SSL_SESSION_parse_crypto_buffer(CBS *cbs,
                                           UniquePtr<CRYPTO_BUFFER> *out,
                                           unsigned tag,
                                           CRYPTO_BUFFER_POOL *pool) {
  if (!CBS_peek_asn1_tag(cbs, tag)) {
    return 1;
  }

  CBS child, value;
  if (!CBS_get_asn1(cbs, &child, tag) ||
      !CBS_get_asn1(&child, &value, CBS_ASN1_OCTETSTRING) ||
      CBS_len(&child) != 0) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return 0;
  }
  out->reset(CRYPTO_BUFFER_new_from_CBS(&value, pool));
  if (*out == nullptr) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }
  return 1;
}

// SSL_SESSION_parse_bounded_octet_string parses an optional ASN.1 OCTET STRING
// explicitly tagged with |tag| of size at most |max_out|.
static int SSL_SESSION_parse_bounded_octet_string(
    CBS *cbs, uint8_t *out, uint8_t *out_len, uint8_t max_out, unsigned tag) {
  CBS value;
  if (!CBS_get_optional_asn1_octet_string(cbs, &value, NULL, tag) ||
      CBS_len(&value) > max_out) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return 0;
  }
  OPENSSL_memcpy(out, CBS_data(&value), CBS_len(&value));
  *out_len = (uint8_t)CBS_len(&value);
  return 1;
}

static int SSL_SESSION_parse_long(CBS *cbs, long *out, unsigned tag,
                                  long default_value) {
  uint64_t value;
  if (!CBS_get_optional_asn1_uint64(cbs, &value, tag,
                                    (uint64_t)default_value) ||
      value > LONG_MAX) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return 0;
  }
  *out = (long)value;
  return 1;
}

static int SSL_SESSION_parse_u32(CBS *cbs, uint32_t *out, unsigned tag,
                                 uint32_t default_value) {
  uint64_t value;
  if (!CBS_get_optional_asn1_uint64(cbs, &value, tag,
                                    (uint64_t)default_value) ||
      value > 0xffffffff) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return 0;
  }
  *out = (uint32_t)value;
  return 1;
}

static int SSL_SESSION_parse_u16(CBS *cbs, uint16_t *out, unsigned tag,
                                 uint16_t default_value) {
  uint64_t value;
  if (!CBS_get_optional_asn1_uint64(cbs, &value, tag,
                                    (uint64_t)default_value) ||
      value > 0xffff) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return 0;
  }
  *out = (uint16_t)value;
  return 1;
}

UniquePtr<SSL_SESSION> SSL_SESSION_parse(CBS *cbs,
                                         const SSL_X509_METHOD *x509_method,
                                         CRYPTO_BUFFER_POOL *pool) {
  UniquePtr<SSL_SESSION> ret = ssl_session_new(x509_method);
  if (!ret) {
    return nullptr;
  }

  CBS session;
  uint64_t version, ssl_version;
  uint16_t unused;
  if (!CBS_get_asn1(cbs, &session, CBS_ASN1_SEQUENCE) ||
      !CBS_get_asn1_uint64(&session, &version) ||
      version != kVersion ||
      !CBS_get_asn1_uint64(&session, &ssl_version) ||
      // Require sessions have versions valid in either TLS or DTLS. The session
      // will not be used by the handshake if not applicable, but, for
      // simplicity, never parse a session that does not pass
      // |ssl_protocol_version_from_wire|.
      ssl_version > UINT16_MAX ||
      !ssl_protocol_version_from_wire(&unused, ssl_version)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }
  ret->ssl_version = ssl_version;

  CBS cipher;
  uint16_t cipher_value;
  if (!CBS_get_asn1(&session, &cipher, CBS_ASN1_OCTETSTRING) ||
      !CBS_get_u16(&cipher, &cipher_value) ||
      CBS_len(&cipher) != 0) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }
  ret->cipher = SSL_get_cipher_by_value(cipher_value);
  if (ret->cipher == NULL) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_UNSUPPORTED_CIPHER);
    return nullptr;
  }

  CBS session_id, secret;
  if (!CBS_get_asn1(&session, &session_id, CBS_ASN1_OCTETSTRING) ||
      CBS_len(&session_id) > SSL3_MAX_SSL_SESSION_ID_LENGTH ||
      !CBS_get_asn1(&session, &secret, CBS_ASN1_OCTETSTRING) ||
      CBS_len(&secret) > SSL_MAX_MASTER_KEY_LENGTH) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }
  OPENSSL_memcpy(ret->session_id, CBS_data(&session_id), CBS_len(&session_id));
  ret->session_id_length = CBS_len(&session_id);
  OPENSSL_memcpy(ret->secret, CBS_data(&secret), CBS_len(&secret));
  ret->secret_length = CBS_len(&secret);

  CBS child;
  uint64_t timeout;
  if (!CBS_get_asn1(&session, &child, kTimeTag) ||
      !CBS_get_asn1_uint64(&child, &ret->time) ||
      !CBS_get_asn1(&session, &child, kTimeoutTag) ||
      !CBS_get_asn1_uint64(&child, &timeout) ||
      timeout > UINT32_MAX) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }

  ret->timeout = (uint32_t)timeout;

  CBS peer;
  int has_peer;
  if (!CBS_get_optional_asn1(&session, &peer, &has_peer, kPeerTag) ||
      (has_peer && CBS_len(&peer) == 0)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }
  // |peer| is processed with the certificate chain.

  if (!SSL_SESSION_parse_bounded_octet_string(
          &session, ret->sid_ctx, &ret->sid_ctx_length, sizeof(ret->sid_ctx),
          kSessionIDContextTag) ||
      !SSL_SESSION_parse_long(&session, &ret->verify_result, kVerifyResultTag,
                              X509_V_OK)) {
    return nullptr;
  }

  // Skip the historical hostName field.
  CBS unused_hostname;
  if (!CBS_get_optional_asn1(&session, &unused_hostname, nullptr,
                             kHostNameTag)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }

  if (!SSL_SESSION_parse_string(&session, &ret->psk_identity,
                                kPSKIdentityTag) ||
      !SSL_SESSION_parse_u32(&session, &ret->ticket_lifetime_hint,
                             kTicketLifetimeHintTag, 0) ||
      !SSL_SESSION_parse_octet_string(&session, &ret->ticket, kTicketTag)) {
    return nullptr;
  }

  if (CBS_peek_asn1_tag(&session, kPeerSHA256Tag)) {
    CBS peer_sha256;
    if (!CBS_get_asn1(&session, &child, kPeerSHA256Tag) ||
        !CBS_get_asn1(&child, &peer_sha256, CBS_ASN1_OCTETSTRING) ||
        CBS_len(&peer_sha256) != sizeof(ret->peer_sha256) ||
        CBS_len(&child) != 0) {
      OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
      return nullptr;
    }
    OPENSSL_memcpy(ret->peer_sha256, CBS_data(&peer_sha256),
                   sizeof(ret->peer_sha256));
    ret->peer_sha256_valid = 1;
  } else {
    ret->peer_sha256_valid = 0;
  }

  if (!SSL_SESSION_parse_bounded_octet_string(
          &session, ret->original_handshake_hash,
          &ret->original_handshake_hash_len,
          sizeof(ret->original_handshake_hash), kOriginalHandshakeHashTag) ||
      !SSL_SESSION_parse_crypto_buffer(&session,
                                       &ret->signed_cert_timestamp_list,
                                       kSignedCertTimestampListTag, pool) ||
      !SSL_SESSION_parse_crypto_buffer(&session, &ret->ocsp_response,
                                       kOCSPResponseTag, pool)) {
    return nullptr;
  }

  int extended_master_secret;
  if (!CBS_get_optional_asn1_bool(&session, &extended_master_secret,
                                  kExtendedMasterSecretTag,
                                  0 /* default to false */)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }
  ret->extended_master_secret = !!extended_master_secret;

  if (!SSL_SESSION_parse_u16(&session, &ret->group_id, kGroupIDTag, 0)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }

  CBS cert_chain;
  CBS_init(&cert_chain, NULL, 0);
  int has_cert_chain;
  if (!CBS_get_optional_asn1(&session, &cert_chain, &has_cert_chain,
                             kCertChainTag) ||
      (has_cert_chain && CBS_len(&cert_chain) == 0)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }
  if (has_cert_chain && !has_peer) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }
  if (has_peer || has_cert_chain) {
    ret->certs.reset(sk_CRYPTO_BUFFER_new_null());
    if (ret->certs == nullptr) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return nullptr;
    }

    if (has_peer) {
      UniquePtr<CRYPTO_BUFFER> buffer(CRYPTO_BUFFER_new_from_CBS(&peer, pool));
      if (!buffer ||
          !PushToStack(ret->certs.get(), std::move(buffer))) {
        OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
        return nullptr;
      }
    }

    while (CBS_len(&cert_chain) > 0) {
      CBS cert;
      if (!CBS_get_any_asn1_element(&cert_chain, &cert, NULL, NULL) ||
          CBS_len(&cert) == 0) {
        OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
        return nullptr;
      }

      UniquePtr<CRYPTO_BUFFER> buffer(CRYPTO_BUFFER_new_from_CBS(&cert, pool));
      if (buffer == nullptr ||
          !PushToStack(ret->certs.get(), std::move(buffer))) {
        OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
        return nullptr;
      }
    }
  }

  CBS age_add;
  int age_add_present;
  if (!CBS_get_optional_asn1_octet_string(&session, &age_add, &age_add_present,
                                          kTicketAgeAddTag) ||
      (age_add_present &&
       !CBS_get_u32(&age_add, &ret->ticket_age_add)) ||
      CBS_len(&age_add) != 0) {
    return nullptr;
  }
  ret->ticket_age_add_valid = age_add_present != 0;

  int is_server;
  if (!CBS_get_optional_asn1_bool(&session, &is_server, kIsServerTag,
                                  1 /* default to true */)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }
  /* TODO: in time we can include |is_server| for servers too, then we can
     enforce that client and server sessions are never mixed up. */

  ret->is_server = is_server;

  int is_quic;
  if (!SSL_SESSION_parse_u16(&session, &ret->peer_signature_algorithm,
                             kPeerSignatureAlgorithmTag, 0) ||
      !SSL_SESSION_parse_u32(&session, &ret->ticket_max_early_data,
                             kTicketMaxEarlyDataTag, 0) ||
      !SSL_SESSION_parse_u32(&session, &ret->auth_timeout, kAuthTimeoutTag,
                             ret->timeout) ||
      !SSL_SESSION_parse_octet_string(&session, &ret->early_alpn,
                                      kEarlyALPNTag) ||
      !CBS_get_optional_asn1_bool(&session, &is_quic, kIsQuicTag,
                                  /*default_value=*/false) ||
      !SSL_SESSION_parse_octet_string(&session, &ret->quic_early_data_context,
                                      kQuicEarlyDataContextTag)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }

  CBS settings;
  int has_local_alps, has_peer_alps;
  if (!CBS_get_optional_asn1_octet_string(&session, &settings, &has_local_alps,
                                          kLocalALPSTag) ||
      !ret->local_application_settings.CopyFrom(settings) ||
      !CBS_get_optional_asn1_octet_string(&session, &settings, &has_peer_alps,
                                          kPeerALPSTag) ||
      !ret->peer_application_settings.CopyFrom(settings) ||
      CBS_len(&session) != 0) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }
  ret->is_quic = is_quic;

  // The two ALPS values and ALPN must be consistent.
  if (has_local_alps != has_peer_alps ||
      (has_local_alps && ret->early_alpn.empty())) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }
  ret->has_application_settings = has_local_alps;

  if (!x509_method->session_cache_objects(ret.get())) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return nullptr;
  }

  return ret;
}

int ssl_session_serialize(const SSL_SESSION *in, CBB *cbb) {
  return SSL_SESSION_to_bytes_full(in, cbb, 0);
}

BSSL_NAMESPACE_END

using namespace bssl;

int SSL_SESSION_to_bytes(const SSL_SESSION *in, uint8_t **out_data,
                         size_t *out_len) {
  if (in->not_resumable) {
    // If the caller has an unresumable session, e.g. if |SSL_get_session| were
    // called on a TLS 1.3 or False Started connection, serialize with a
    // placeholder value so it is not accidentally deserialized into a resumable
    // one.
    static const char kNotResumableSession[] = "NOT RESUMABLE";

    *out_len = strlen(kNotResumableSession);
    *out_data = (uint8_t *)OPENSSL_memdup(kNotResumableSession, *out_len);
    if (*out_data == NULL) {
      return 0;
    }

    return 1;
  }

  ScopedCBB cbb;
  if (!CBB_init(cbb.get(), 256) ||
      !SSL_SESSION_to_bytes_full(in, cbb.get(), 0) ||
      !CBB_finish(cbb.get(), out_data, out_len)) {
    return 0;
  }

  return 1;
}

int SSL_SESSION_to_bytes_for_ticket(const SSL_SESSION *in, uint8_t **out_data,
                                    size_t *out_len) {
  ScopedCBB cbb;
  if (!CBB_init(cbb.get(), 256) ||
      !SSL_SESSION_to_bytes_full(in, cbb.get(), 1) ||
      !CBB_finish(cbb.get(), out_data, out_len)) {
    return 0;
  }

  return 1;
}

int i2d_SSL_SESSION(SSL_SESSION *in, uint8_t **pp) {
  uint8_t *out;
  size_t len;

  if (!SSL_SESSION_to_bytes(in, &out, &len)) {
    return -1;
  }

  if (len > INT_MAX) {
    OPENSSL_free(out);
    OPENSSL_PUT_ERROR(SSL, ERR_R_OVERFLOW);
    return -1;
  }

  if (pp) {
    OPENSSL_memcpy(*pp, out, len);
    *pp += len;
  }
  OPENSSL_free(out);

  return len;
}

SSL_SESSION *SSL_SESSION_from_bytes(const uint8_t *in, size_t in_len,
                                    const SSL_CTX *ctx) {
  CBS cbs;
  CBS_init(&cbs, in, in_len);
  UniquePtr<SSL_SESSION> ret =
      SSL_SESSION_parse(&cbs, ctx->x509_method, ctx->pool);
  if (!ret) {
    return NULL;
  }
  if (CBS_len(&cbs) != 0) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL_SESSION);
    return NULL;
  }
  return ret.release();
}

// SSL3_STATE serialization.

static const unsigned kS3Version = 1;

static const unsigned kS3EstablishedSessionTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 0;
static const unsigned kS3SessionReusedTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 1;
static const unsigned kS3HostNameTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 2;
static const unsigned kS3ALPNSelectedTag = 
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 3;
static const unsigned kS3NextProtoNegotiatedTag = 
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 4;
static const unsigned kS3ChannelIdValidTag = 
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 5;
static const unsigned kS3ChannelIdTag = 
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 6;

// *** EXPERIMENTAL — DO NOT USE WITHOUT CHECKING ***
// These SSL3_STATE serialization functions are developed to support SSL transfer.

// ssl3_state_to_bytes serializes |in| to bytes stored in |cbb|.
// It returns one on success and zero on failure.
//
// An SSL3_STATE is serialized as the following ASN.1 structure:
//
// SSL3State ::= SEQUENCE {
//    version                           INTEGER (1),  -- SSL3_STATE structure version
//    readSequence                      OCTET STRING,
//    writeSequence                     OCTET STRING,
//    serverRandom                      OCTET STRING,
//    clientRandom                      OCTET STRING,
//    sendAlert                         OCTET STRING,
//    rwstate                           INTEGER,
//    earlyDataReason                   INTEGER,
//    previousClientFinished            OCTET STRING,
//    previousClientFinishedLen         INTEGER,
//    previousServerFinished            OCTET STRING,
//    previousServerFinishedLen         INTEGER,
//    warningAlertCount                 INTEGER,
//    establishedSession                [0] SEQUENCE OPTIONAL,
//    sessionReused                     [1] BOOLEAN OPTIONAL,
//    hostName                          [2] OCTET STRING OPTIONAL,
//    alpnSelected                      [3] OCTET STRING OPTIONAL,
//    nextProtoNegotiated               [4] BOOLEAN OPTIONAL,
//    channelIdValid                    [5] BOOLEAN OPTIONAL,
//    channelId                         [6] OCTET STRING OPTIONAL,
// }
static int SSL3_STATE_to_bytes(const SSL3_STATE *in, CBB *cbb) {
  if (in == NULL || cbb == NULL) {
    return 0;
  }

  CBB s3, child;
  if (!CBB_add_asn1(cbb, &s3, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1_uint64(&s3, kS3Version) ||
      !CBB_add_asn1_octet_string(&s3, in->read_sequence, TLS_SEQ_NUM_SIZE) ||
      !CBB_add_asn1_octet_string(&s3, in->write_sequence, TLS_SEQ_NUM_SIZE) ||
      !CBB_add_asn1_octet_string(&s3, in->server_random, SSL3_RANDOM_SIZE) ||
      !CBB_add_asn1_octet_string(&s3, in->client_random, SSL3_RANDOM_SIZE) ||
      !CBB_add_asn1_octet_string(&s3, in->send_alert, SSL3_SEND_ALERT_SIZE) ||
      !CBB_add_asn1_int64(&s3, in->rwstate) ||
      !CBB_add_asn1_int64(&s3, in->early_data_reason) ||
      !CBB_add_asn1_octet_string(&s3, in->previous_client_finished, PREV_FINISHED_MAX_SIZE) ||
      !CBB_add_asn1_uint64(&s3, in->previous_client_finished_len) ||
      !CBB_add_asn1_octet_string(&s3, in->previous_server_finished, PREV_FINISHED_MAX_SIZE) ||
      !CBB_add_asn1_uint64(&s3, in->previous_server_finished_len) ||
      !CBB_add_asn1_uint64(&s3, in->warning_alert_count)) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  #if defined(SSL_DEBUG)
    const bssl::SSLBuffer *buf = &(in->write_buffer);
    fprintf( stderr, "SSL3_STATE_to_bytes buf %d\n", buf->empty());
  #endif

  if (in->established_session != nullptr) {
    if (!CBB_add_asn1(&s3, &child, kS3EstablishedSessionTag) ||
        !ssl_session_serialize(in->established_session.get(), &child)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->session_reused) {
    if (!CBB_add_asn1(&s3, &child, kS3SessionReusedTag) ||
        !CBB_add_asn1_bool(&child, true)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->hostname != nullptr) {
    if (!CBB_add_asn1(&s3, &child, kS3HostNameTag) ||
        !CBB_add_asn1_octet_string(&child,
                                   (const uint8_t *)(in->hostname.get()),
                                   strlen(in->hostname.get()))) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (!in->alpn_selected.empty()) {
    if (!CBB_add_asn1(&s3, &child, kS3ALPNSelectedTag) ||
        !CBB_add_asn1_octet_string(&child, in->alpn_selected.data(),
                                   in->alpn_selected.size())) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (!in->next_proto_negotiated.empty()) {
    if (!CBB_add_asn1(&s3, &child, kS3NextProtoNegotiatedTag) ||
        !CBB_add_asn1_octet_string(&child, in->next_proto_negotiated.data(),
                                   in->next_proto_negotiated.size())) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->channel_id_valid) {
    if (!CBB_add_asn1(&s3, &child, kS3ChannelIdValidTag) ||
        !CBB_add_asn1_bool(&child, true)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
    if (!CBB_add_asn1(&s3, &child, kS3ChannelIdTag) ||
        !CBB_add_asn1_octet_string(&child, in->channel_id, SSL3_CHANNEL_ID_SIZE)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  return CBB_flush(cbb);
}

static int SSL3_STATE_parse_session(CBS *cbs, UniquePtr<SSL_SESSION> *out, const SSL_CTX *ctx) {
  CBS value;
  int present;
  if (!CBS_get_optional_asn1(cbs, &value, &present, kS3EstablishedSessionTag)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL3_STATE);
    return 0;
  }
  if (present) {
    UniquePtr<SSL_SESSION> ptr =
      SSL_SESSION_parse(&value, ctx->x509_method, ctx->pool);
    if (!ptr) {
      return 0;
    }
    out->reset(ptr.release());
  } else {
    out->reset();
  }
  return 1;
}

static int SSL3_STATE_from_bytes(SSL3_STATE *out, CBS *cbs, const SSL_CTX *ctx) {
  if (out == NULL || cbs == NULL || ctx == NULL) {
    return 0;
  }

  CBS s3, read_seq, write_seq, server_random, client_random, send_alert;
  CBS previous_client_finished, previous_server_finished;
  int session_reused, channel_id_valid;
  uint64_t version, early_data_reason, previous_client_finished_len, previous_server_finished_len;
  uint64_t warning_alert_count;
  int64_t rwstate;
  if (!CBS_get_asn1(cbs, &s3, CBS_ASN1_SEQUENCE) ||
      !CBS_get_asn1_uint64(&s3, &version) ||
      version != kS3Version ||
      !CBS_get_asn1(&s3, &read_seq, CBS_ASN1_OCTETSTRING) ||
      CBS_len(&read_seq) != TLS_SEQ_NUM_SIZE ||
      !CBS_get_asn1(&s3, &write_seq, CBS_ASN1_OCTETSTRING) ||
      CBS_len(&write_seq) != TLS_SEQ_NUM_SIZE ||
      !CBS_get_asn1(&s3, &server_random, CBS_ASN1_OCTETSTRING) ||
      CBS_len(&server_random) != SSL3_RANDOM_SIZE ||
      !CBS_get_asn1(&s3, &client_random, CBS_ASN1_OCTETSTRING) ||
      CBS_len(&client_random) != SSL3_RANDOM_SIZE ||
      !CBS_get_asn1(&s3, &send_alert, CBS_ASN1_OCTETSTRING) ||
      CBS_len(&send_alert) != SSL3_SEND_ALERT_SIZE ||
      !CBS_get_asn1_int64(&s3, &rwstate) ||
      !CBS_get_asn1_uint64(&s3, &early_data_reason) ||
      early_data_reason > ssl_early_data_reason_max_value ||
      !CBS_get_asn1(&s3, &previous_client_finished, CBS_ASN1_OCTETSTRING) ||
      CBS_len(&previous_client_finished) != PREV_FINISHED_MAX_SIZE ||
      !CBS_get_asn1_uint64(&s3, &previous_client_finished_len) ||
      previous_client_finished_len > PREV_FINISHED_MAX_SIZE ||
      !CBS_get_asn1(&s3, &previous_server_finished, CBS_ASN1_OCTETSTRING) ||
      CBS_len(&previous_server_finished) != PREV_FINISHED_MAX_SIZE ||
      !CBS_get_asn1_uint64(&s3, &previous_server_finished_len) ||
      previous_server_finished_len > PREV_FINISHED_MAX_SIZE ||
      !CBS_get_asn1_uint64(&s3, &warning_alert_count) ||
      !SSL3_STATE_parse_session(&s3, &(out->established_session), ctx) ||
      !CBS_get_optional_asn1_bool(&s3, &session_reused, kS3SessionReusedTag, 0 /* default to false */) ||
      !parse_optional_string(&s3, &(out->hostname), kS3HostNameTag, SSL_R_INVALID_SSL3_STATE) ||
      !SSL3_STATE_parse_octet_string(&s3, &(out->alpn_selected), kS3ALPNSelectedTag) ||
      !SSL3_STATE_parse_octet_string(&s3, &(out->next_proto_negotiated), kS3NextProtoNegotiatedTag) ||
      !CBS_get_optional_asn1_bool(&s3, &channel_id_valid, kS3ChannelIdValidTag, 0 /* default to false */) ||
      !SSL3_STATE_get_optional_octet_string(&s3, out->channel_id, kS3ChannelIdTag, SSL3_CHANNEL_ID_SIZE) ||
      CBS_len(&s3) != 0) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL3_STATE);
    return 0;
  }
  OPENSSL_memcpy(out->read_sequence, CBS_data(&read_seq), TLS_SEQ_NUM_SIZE);
  OPENSSL_memcpy(out->write_sequence, CBS_data(&write_seq), TLS_SEQ_NUM_SIZE);
  OPENSSL_memcpy(out->server_random, CBS_data(&server_random), SSL3_RANDOM_SIZE);
  OPENSSL_memcpy(out->client_random, CBS_data(&client_random), SSL3_RANDOM_SIZE);
  OPENSSL_memcpy(out->send_alert, CBS_data(&send_alert), SSL3_SEND_ALERT_SIZE);
  OPENSSL_memcpy(out->previous_client_finished, CBS_data(&previous_client_finished), PREV_FINISHED_MAX_SIZE);
  OPENSSL_memcpy(out->previous_server_finished, CBS_data(&previous_server_finished), PREV_FINISHED_MAX_SIZE);
  out->early_data_reason = static_cast<ssl_early_data_reason_t>(early_data_reason);
  out->rwstate = rwstate;
  out->session_reused = !!session_reused;
  out->channel_id_valid = !!channel_id_valid;
  out->previous_client_finished_len = previous_client_finished_len;
  out->previous_server_finished_len = previous_server_finished_len;
  out->v2_hello_done = true;
  out->initial_handshake_complete = true;
  out->warning_alert_count = warning_alert_count;
  // Below comment is copied from |SSL_do_handshake|.
  // Destroy the handshake object if the handshake has completely finished.
  out->hs.reset();
  return 1;
}

// SSL serialization.

// Serialized SSL data version for forward compatibility
#define SSL_SERIAL_VERSION 1

static const unsigned kSSLQuietShutdownTag = 
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 0;

//  Parse serialized SSL connection binary
//
//  @details This function attempts to recover serialized SSL connection from
//  binary. It restores session key, IV and sequence number for both read and
//  write directions. Restored data is saved to given SSL handler.
//
//  An SSL object is serialized as the following ASN.1 structure:
//  SSL ::= SEQUENCE {
//      ssl_serial_ver UINT64                        -- version of the SSL serialization format
//      version        UINT64
//      sheded         BOOLEAN                       -- indicate if the config is sheded. The config may not exist
//                                                      since the configuration 
//                                                      may be shed after the handshake completes
//      s3             SEQUENCE
//      mode           UINT64
//      quietShutdown  [0] BOOLEAN OPTIONAL,
//  }
//
//  Note that serialized SSL_SESSION is always prepended to the serialized SSL
//
//  @returns
//    0 if an error occur
//    1 if SSL is succesfully restored
//
static int SSL_to_bytes_full(const SSL *in, CBB *cbb) {
  CBB ssl, child;

  // TODO: check how to handle config.
  int sheded = !in->config;

  if (!CBB_add_asn1(cbb, &ssl, CBS_ASN1_SEQUENCE) ||
    !CBB_add_asn1_uint64(&ssl, SSL_SERIAL_VERSION) ||
    //    FIXME add hash of SSL_CTX
    !CBB_add_asn1_uint64(&ssl, in->version) ||
    !CBB_add_asn1_uint64(&ssl, in->max_send_fragment) ||
    !CBB_add_asn1_bool(&ssl, sheded) ||
    !SSL3_STATE_to_bytes(in->s3, &ssl) ||
    !CBB_add_asn1_uint64(&ssl, in->mode)) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  if (in->quiet_shutdown) {
    if (!CBB_add_asn1(&ssl, &child, kSSLQuietShutdownTag) ||
        !CBB_add_asn1_bool(&child, true)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  return CBB_flush(cbb);
}

static int SSL_parse(SSL *ssl, CBS *cbs, SSL_CTX *ctx) {
  CBS ssl_cbs;
  uint64_t ssl_serial_ver, version, max_send_fragment, mode;
  int quiet_shutdown;

  int sheded = 0;
  // Read version string from buffer
  if (!CBS_get_asn1(cbs, &ssl_cbs, CBS_ASN1_SEQUENCE) ||
      CBS_len(cbs) != 0 ||
      !CBS_get_asn1_uint64(&ssl_cbs, &ssl_serial_ver)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL);
    return 0;
  }
  // At the moment we're simply asserting the version is correct. However
  // future updates could use SSL serial version to figure out what data
  // was actually serialized and act accordingly.
  assert(ssl_serial_ver <= SSL_SERIAL_VERSION);

  //    FIXME add hash of SSL_CTX
  // This TODO is actually a part of SSL DER struct revisit.
  if (!CBS_get_asn1_uint64(&ssl_cbs, &version) ||
    !CBS_get_asn1_uint64(&ssl_cbs, &max_send_fragment) ||
    !CBS_get_asn1_bool(&ssl_cbs, &sheded)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL);
    return 0;
  }

  ssl->version = version;
  ssl->max_send_fragment = max_send_fragment;

  // This is called separately to avoid overriding error code.
  if (!SSL3_STATE_from_bytes(ssl->s3, &ssl_cbs, ssl->ctx.get())) {
    return 0;
  }

  if (!CBS_get_asn1_uint64(&ssl_cbs, &mode)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL);
    return 0;
  }
  ssl->mode = mode;

  if (!CBS_get_optional_asn1_bool(&ssl_cbs, &quiet_shutdown, kSSLQuietShutdownTag, 0 /* default to false */)) {
    return 0;
  }
  ssl->quiet_shutdown = !!quiet_shutdown;

  // TODO: remove below copy when investigated why set_read_state reset read_sequence to zero.
  uint8_t read_sequence[TLS_SEQ_NUM_SIZE] = {0};
  uint8_t write_sequence[TLS_SEQ_NUM_SIZE] = {0};
  OPENSSL_memcpy(read_sequence, ssl->s3->read_sequence, TLS_SEQ_NUM_SIZE);
  OPENSSL_memcpy(write_sequence, ssl->s3->write_sequence, TLS_SEQ_NUM_SIZE);

  // TODO: check how to serialize internal field state.
  // have_version is true if the connection's final version is known. Otherwise
  // the version has not been negotiated yet.
  // uint16_t ssl_protocol_version(const SSL *ssl) {
  // assert(ssl->s3->have_version);
  ssl->s3->have_version = true;

  SSL_SESSION *session = ssl->s3->established_session.get();

  if (CBS_len(&ssl_cbs) != 0) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL);
    return 0;
  }

  if (sheded) {
    Delete(ssl->config.release());
  }

  // TODO: encode the state of ssl instead of calling SSL_set_accept_state below.
  SSL_set_accept_state(ssl);

  // TODO: revisit iv. it seems the iv is always empty based on
  // the impl of |SSL_serialize_handback|, which only fetch IV when it's TLS 1.
  Array<uint8_t> key_block1, key_block2;
  // Span<const uint8_t> w_iv = MakeConstSpan(CBS_data(&write_iv), CBS_len(&write_iv));
  if (!tls1_configure_aead(ssl, evp_aead_seal, &key_block1, session, {})) {
    return 0;
  }
  // Span<const uint8_t> r_iv = MakeConstSpan(CBS_data(&read_iv), CBS_len(&read_iv));
  if (!tls1_configure_aead(ssl, evp_aead_open, &key_block2, session, {})) {
    return 0;
  }

  // TODO: remove below copy when investigated why set_read_state reset read_sequence to zero.
  OPENSSL_memcpy(ssl->s3->read_sequence, read_sequence, TLS_SEQ_NUM_SIZE);
  OPENSSL_memcpy(ssl->s3->write_sequence, write_sequence, TLS_SEQ_NUM_SIZE);
  return 1;
}

SSL *SSL_from_bytes(const uint8_t *in, size_t in_len, SSL_CTX *ctx) {
  if (!in || !in_len || !ctx) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_SHOULD_NOT_HAVE_BEEN_CALLED);
    return NULL;
  }

  SSL *ssl = SSL_new(ctx);
  if (ssl == NULL) {
    return NULL;
  }
  UniquePtr<SSL> ret(ssl);

  CBS cbs, seq;
  CBS_init(&cbs, in, in_len);
  if (!CBS_get_asn1(&cbs, &seq, CBS_ASN1_SEQUENCE) ||
      (CBS_len(&cbs) != 0)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_INVALID_SSL);
    return NULL;
  }

  // Restore SSL part
  if (!SSL_parse(ret.get(), &seq, ctx)) {
    return NULL;
  }

  return ret.release();
}

int SSL_to_bytes(const SSL *in, uint8_t **out_data, size_t *out_len) {
  if (in == NULL) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_SHOULD_NOT_HAVE_BEEN_CALLED);
    return 0;
  }

  ScopedCBB cbb;
  // An SSL connection can't be serialized by current implementation under some conditions
  // 0) It's server SSL.
  // 1) It's a DTLS connection.
  // 2) It uses QUIC
  // 3) Its SSL_SESSION isn't serializable.
  // 4) Handshake hasn't finished yet.
  // 5) TLS version is not supported(currently, only TLS 1.2 is supported).
  // 6) Write is in clean state(|SSL_write| should finish the |in| write, no pending writes).
  // 7) ssl is not shutdown or has shutdown error.
  //    TODO: support TLS 1.3 and TLS 1.1.
  if (!SSL_is_server(in) ||                                     // (0)
      SSL_is_dtls(in) ||                                        // (1)
      in->quic_method != nullptr ||                             // (2)
      !in->s3 ||                                                // (3)
      !in->s3->established_session ||
      in->s3->established_session.get()->not_resumable ||
      // TODO: Check in->s3->rwstate.
      SSL_in_init(in) ||                                        // (4)
      in->version != TLS1_2_VERSION ||                          // (5)
      in->s3->wnum != 0 ||                                      // (6)
      in->s3->wpend_pending ||
      in->s3->read_shutdown != ssl_shutdown_none ||             // (7)
      in->s3->write_shutdown != ssl_shutdown_none) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_SHOULD_NOT_HAVE_BEEN_CALLED);
    // fprintf( stderr, "!SSL_is_server(in) %d\n", !SSL_is_server(in));
    // fprintf( stderr, "SSL_is_dtls(in) %d\n", SSL_is_dtls(in));
    // fprintf( stderr, "SSL_in_init(in) %d\n", SSL_in_init(in));
    // fprintf( stderr, "in->version %x\n", in->version);
    // fprintf( stderr, "in->s3->established_session.get()->not_resumable %d\n", in->s3->established_session.get()->not_resumable);
    return 0;
  }

  // TODO: add ssl shutdown check?

  CBB seq;
  if (!CBB_init(cbb.get(), 1024) ||
      !CBB_add_asn1(cbb.get(), &seq, CBS_ASN1_SEQUENCE) ||
      !SSL_to_bytes_full(in, &seq)) {
    return 0;
  }

  return CBB_finish(cbb.get(), out_data, out_len);
}
