/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0
 */

#include <openssl/ssl.h>

#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "internal.h"

BSSL_NAMESPACE_BEGIN

bool ssl_transfer_supported(const SSL *in) {
  if (in == NULL) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_UNSUPPORTED);
    return false;
  }

  // An SSL connection can't be serialized by current implementation under some conditions
  // 0) It's not server SSL.
  // 1) It's a DTLS connection.
  // 2) It uses QUIC
  // 3) Its SSL_SESSION isn't serializable.
  // 4) Handshake hasn't finished yet.
  // 5) TLS version is not supported(currently, only TLS 1.2 is supported).
  // 6) Write is not in clean state(|SSL_write| should finish the |in| write, no pending writes).
  // 7) ssl shutdown state is not ssl_shutdown_none.
  //    TODO: support TLS 1.3 and TLS 1.1.
  if (!SSL_is_server(in) ||                                     // (0)
      SSL_is_dtls(in) ||                                        // (1)
      in->quic_method != nullptr ||                             // (2)
      !in->s3 ||                                                // (3)
      !in->s3->established_session ||
      SSL_in_init(in) ||                                        // (4)
      in->version != TLS1_2_VERSION ||                          // (5)
      in->s3->wnum != 0 ||                                      // (6)
      in->s3->wpend_pending ||
      in->s3->read_shutdown != ssl_shutdown_none ||             // (7)
      in->s3->write_shutdown != ssl_shutdown_none) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_UNSUPPORTED);
    return false;
  }

  return true;
}

BSSL_NAMESPACE_END

using namespace bssl;

// SSL3_STATE_parse_octet_string gets an optional ASN.1 OCTET STRING explicitly
// tagged with |tag| from |cbs| and stows it in |*out|. It returns one on
// success, whether or not the element was found, and zero on decode error.
static bool SSL3_STATE_parse_octet_string(CBS *cbs, Array<uint8_t> *out,
                               unsigned tag) {
  CBS value;
  if (!CBS_get_optional_asn1_octet_string(cbs, &value, NULL, tag)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL3_STATE);
    return false;
  }
  return out->CopyFrom(value);
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

// SSL3_STATE_get_optional_octet_string requires |dst| has |target_len|
// space to store the |tag| data from the |cbs|.
static bool SSL3_STATE_get_optional_octet_string(CBS *cbs, void *dst,
                                                 unsigned tag,
                                                 size_t target_len) {
  int present;
  CBS value;
  if (!CBS_get_optional_asn1_octet_string(cbs, &value, &present, tag)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL3_STATE);
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
static const unsigned kS3SendConnectionBindingTag = 
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 7;
static const unsigned kS3PendingAppDataTag = 
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 8;
static const unsigned kS3ReadBufferTag = 
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 9;
static const unsigned kS3NotResumableTag = 
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 10;

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
//    emptyRecordCount                  INTEGER,
//    warningAlertCount                 INTEGER,
//    totalRenegotiations               INTEGER,
//    establishedSession                [0] SEQUENCE OPTIONAL,
//    sessionReused                     [1] BOOLEAN OPTIONAL,
//    hostName                          [2] OCTET STRING OPTIONAL,
//    alpnSelected                      [3] OCTET STRING OPTIONAL,
//    nextProtoNegotiated               [4] OCTET STRING OPTIONAL,
//    channelIdValid                    [5] BOOLEAN OPTIONAL,
//    channelId                         [6] OCTET STRING OPTIONAL,
//    sendConnectionBinding             [7] BOOLEAN OPTIONAL,
//    pendingAppData                    [8] SEQUENCE OPTIONAL,
//                                          -- see Span ASN1.
//    readBuffer                        [9] SEQUENCE OPTIONAL,
//                                          -- see ASN1 struct in the comment of |DoSerialization|.
//    notResumable                      [10] BOOLEAN OPTIONAL,
// }
//
// Span ::= SEQUENCE {
//    offset                           INTEGER,
//    size                             INTEGER,
// }
static int SSL3_STATE_to_bytes(SSL3_STATE *in, CBB *cbb) {
  if (in == NULL || cbb == NULL) {
    return 0;
  }

  CBB s3, child, child2;
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
      !CBB_add_asn1_uint64(&s3, in->empty_record_count) ||
      !CBB_add_asn1_uint64(&s3, in->warning_alert_count) ||
      !CBB_add_asn1_uint64(&s3, in->total_renegotiations)) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  if (!CBB_add_asn1(&s3, &child, kS3EstablishedSessionTag) ||
      !ssl_session_serialize(in->established_session.get(), &child)) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  if (in->session_reused) {
    if (!CBB_add_asn1(&s3, &child, kS3SessionReusedTag) ||
        !CBB_add_asn1_bool(&child, true)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (in->hostname) {
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

  if (in->send_connection_binding) {
    if (!CBB_add_asn1(&s3, &child, kS3SendConnectionBindingTag) ||
        !CBB_add_asn1_bool(&child, true)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (!in->pending_app_data.empty()) {
    // This should never happen because pending_app_data is just a span and points to read_buffer.
    if (!in->read_buffer.buf_ptr() || in->read_buffer.buf_ptr() > in->pending_app_data.data()) {
      OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL3_STATE);
      return 0;
    }
    uint64_t offset = in->pending_app_data.data() - in->read_buffer.buf_ptr();
    if (!CBB_add_asn1(&s3, &child, kS3PendingAppDataTag) ||
        !CBB_add_asn1(&child, &child2, CBS_ASN1_SEQUENCE) ||
        !CBB_add_asn1_uint64(&child2, offset) ||
        !CBB_add_asn1_uint64(&child2, in->pending_app_data.size())) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  if (!in->pending_app_data.empty() ||
      !in->read_buffer.empty()) {
    if (!CBB_add_asn1(&s3, &child, kS3ReadBufferTag) ||
        !in->read_buffer.DoSerialization(&child)) {
      return 0;
    }
  }
  // serialization of |not_resumable| is not added in |ssl_session_serialize|
  // because the function is used to serialize a session for resumption.
  if (in->established_session.get()->not_resumable) {
    if (!CBB_add_asn1(&s3, &child, kS3NotResumableTag) ||
        !CBB_add_asn1_bool(&child, true)) {
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
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL3_STATE);
    return 0;
  }
  if (present) {
    UniquePtr<SSL_SESSION> ptr =
      SSL_SESSION_parse(&value, ctx->x509_method, ctx->pool);
    if (!ptr) {
      return 0;
    }
    out->reset(ptr.release());
    return 1;
  } else {
    // session should exist because ssl transfer only supports SSL completes handshake.
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL3_STATE);
    out->reset();
    return 0;
  }
}

// SSL3_STATE_from_bytes recovers SSL3_STATE from |cbs|.
// |ssl| is used because |tls1_configure_aead| is used to recover |aead_read_ctx| and |aead_write_ctx|.
static int SSL3_STATE_from_bytes(SSL *ssl, CBS *cbs, const SSL_CTX *ctx) {
  SSL3_STATE *out = ssl->s3;
  CBS s3, read_seq, write_seq, server_random, client_random, send_alert, pending_app_data, read_buffer;
  CBS previous_client_finished, previous_server_finished;
  int session_reused, channel_id_valid, send_connection_binding, not_resumable;
  uint64_t version, early_data_reason, previous_client_finished_len, previous_server_finished_len;
  uint64_t empty_record_count, warning_alert_count, total_renegotiations;
  int64_t rwstate;
  int pending_app_data_present, read_buffer_present;
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
      !CBS_get_asn1_uint64(&s3, &empty_record_count) ||
      !CBS_get_asn1_uint64(&s3, &warning_alert_count) ||
      !CBS_get_asn1_uint64(&s3, &total_renegotiations) ||
      !SSL3_STATE_parse_session(&s3, &(out->established_session), ctx) ||
      !CBS_get_optional_asn1_bool(&s3, &session_reused, kS3SessionReusedTag, 0 /* default to false */) ||
      !parse_optional_string(&s3, &(out->hostname), kS3HostNameTag, SSL_R_SERIALIZATION_INVALID_SSL3_STATE) ||
      !SSL3_STATE_parse_octet_string(&s3, &(out->alpn_selected), kS3ALPNSelectedTag) ||
      !SSL3_STATE_parse_octet_string(&s3, &(out->next_proto_negotiated), kS3NextProtoNegotiatedTag) ||
      !CBS_get_optional_asn1_bool(&s3, &channel_id_valid, kS3ChannelIdValidTag, 0 /* default to false */) ||
      !SSL3_STATE_get_optional_octet_string(&s3, out->channel_id, kS3ChannelIdTag, SSL3_CHANNEL_ID_SIZE) ||
      !CBS_get_optional_asn1_bool(&s3, &send_connection_binding, kS3SendConnectionBindingTag, 0 /* default to false */) ||
      !CBS_get_optional_asn1(&s3, &pending_app_data, &pending_app_data_present, kS3PendingAppDataTag) ||
      !CBS_get_optional_asn1(&s3, &read_buffer, &read_buffer_present, kS3ReadBufferTag) ||
      !CBS_get_optional_asn1_bool(&s3, &not_resumable, kS3NotResumableTag, 0 /* default to false */) ||
      CBS_len(&s3) != 0) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL3_STATE);
    return 0;
  }
  if (read_buffer_present && !out->read_buffer.DoDeserialization(&read_buffer)) {
    return 0;
  }
  // If |pending_app_data_size| is not zero, it needs to point to |read_buffer|.
  if (pending_app_data_present) {
    if (!read_buffer_present) {
      OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL3_STATE);
      return 0;
    }
    CBS app_seq; 
    uint64_t pending_app_data_offset, pending_app_data_size;
    if (!CBS_get_asn1(&pending_app_data, &app_seq, CBS_ASN1_SEQUENCE) ||
      !CBS_get_asn1_uint64(&app_seq, &pending_app_data_offset) ||
      !CBS_get_asn1_uint64(&app_seq, &pending_app_data_size)) {
      OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL3_STATE);
      return 0;
    }
    if (pending_app_data_size > out->read_buffer.buf_size()) {
      OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL3_STATE);
      return 0;
    }
    out->pending_app_data = MakeSpan(out->read_buffer.buf_ptr() + pending_app_data_offset, pending_app_data_size);
  }
  // Initialize some states before call |tls1_configure_aead|.
  // Below comment is copied from |SSL_do_handshake|.
  // Destroy the handshake object if the handshake has completely finished.
  out->hs.reset();
  // have_version is true if the connection's final version is known. Otherwise
  // the version has not been negotiated yet.
  out->have_version = true;
  OPENSSL_memcpy(out->server_random, CBS_data(&server_random), SSL3_RANDOM_SIZE);
  OPENSSL_memcpy(out->client_random, CBS_data(&client_random), SSL3_RANDOM_SIZE);
  SSL_SESSION *session = out->established_session.get();
  // the impl of |SSL_serialize_handback|, which only fetch IV when it's TLS 1.
  Array<uint8_t> key_block1, key_block2;
  if (!tls1_configure_aead(ssl, evp_aead_seal, &key_block1, session, {})) {
    return 0;
  }
  if (!tls1_configure_aead(ssl, evp_aead_open, &key_block2, session, {})) {
    return 0;
  }
  OPENSSL_memcpy(out->read_sequence, CBS_data(&read_seq), TLS_SEQ_NUM_SIZE);
  OPENSSL_memcpy(out->write_sequence, CBS_data(&write_seq), TLS_SEQ_NUM_SIZE);
  OPENSSL_memcpy(out->send_alert, CBS_data(&send_alert), SSL3_SEND_ALERT_SIZE);
  OPENSSL_memcpy(out->previous_client_finished, CBS_data(&previous_client_finished), PREV_FINISHED_MAX_SIZE);
  OPENSSL_memcpy(out->previous_server_finished, CBS_data(&previous_server_finished), PREV_FINISHED_MAX_SIZE);
  out->early_data_reason = static_cast<ssl_early_data_reason_t>(early_data_reason);
  out->rwstate = rwstate;
  out->session_reused = !!session_reused;
  if (out->session_reused) {
    ssl->session = UpRef(out->established_session);
  }
  out->channel_id_valid = !!channel_id_valid;
  out->previous_client_finished_len = previous_client_finished_len;
  out->previous_server_finished_len = previous_server_finished_len;
  out->v2_hello_done = true;
  out->initial_handshake_complete = true;
  out->empty_record_count = empty_record_count;
  out->warning_alert_count = warning_alert_count;
  out->total_renegotiations = total_renegotiations;
  out->send_connection_binding = !!send_connection_binding;
  out->established_session.get()->not_resumable = !!not_resumable;
  return 1;
}

// SSL_CONFIG serialization.

static const unsigned kSSLConfigVersion = 1;

static const unsigned kSSLConfigOcspStaplingEnabledTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 0;

static const unsigned kSSLConfigJdk11WorkaroundTag =
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 1;

// *** EXPERIMENTAL — DO NOT USE WITHOUT CHECKING ***
// These SSL_CONFIG serialization functions are developed to support SSL transfer.
// Most fields of SSL_CONFIG are not used after handshake completes.
// It only encodes some fields needed by SSL_*_getter functions.

// SSL_CONFIG_to_bytes serializes |in| to bytes stored in |cbb|.
// It returns one on success and zero on failure.
//
// An SSL_CONFIG is serialized as the following ASN.1 structure:
//
// SSL_CONFIG ::= SEQUENCE {
//    version                           INTEGER (1),  -- SSL_CONFIG structure version
//    confMaxVersion                    INTEGER,
//    confMinVersion                    INTEGER,
//    ocspStaplingEnabled               [0] BOOLEAN OPTIONAL,
//    jdk11Workaround                   [1] BOOLEAN OPTIONAL
// }
static int SSL_CONFIG_to_bytes(SSL_CONFIG *in, CBB *cbb) {
  if (in == NULL || cbb == NULL) {
    return 0;
  }

  CBB config, child;
  if (!CBB_add_asn1(cbb, &config, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1_uint64(&config, kSSLConfigVersion) ||
      !CBB_add_asn1_uint64(&config, in->conf_max_version) ||
      !CBB_add_asn1_uint64(&config, in->conf_min_version)) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
    return 0;
  }

  if (in->ocsp_stapling_enabled) {
    if (!CBB_add_asn1(&config, &child, kSSLConfigOcspStaplingEnabledTag) ||
        !CBB_add_asn1_bool(&child, true)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }
  if (in->jdk11_workaround) {
    if (!CBB_add_asn1(&config, &child, kSSLConfigJdk11WorkaroundTag) ||
        !CBB_add_asn1_bool(&child, true)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }
  return CBB_flush(cbb);
}

static int SSL_CONFIG_from_bytes(SSL_CONFIG *out, CBS *cbs) {
  CBS config;
  int ocsp_stapling_enabled, jdk11_workaround;
  uint64_t version, conf_max_version, conf_min_version;
  if (!CBS_get_asn1(cbs, &config, CBS_ASN1_SEQUENCE) ||
      !CBS_get_asn1_uint64(&config, &version) ||
      version != kSSLConfigVersion ||
      !CBS_get_asn1_uint64(&config, &conf_max_version) ||
      !CBS_get_asn1_uint64(&config, &conf_min_version) ||
      !CBS_get_optional_asn1_bool(&config, &ocsp_stapling_enabled, kSSLConfigOcspStaplingEnabledTag, 0 /* default to false */) ||
      !CBS_get_optional_asn1_bool(&config, &jdk11_workaround, kSSLConfigJdk11WorkaroundTag, 0 /* default to false */) ||
      CBS_len(&config) != 0) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL_CONFIG);
    return 0;
  }
  out->conf_max_version = conf_max_version;
  out->conf_min_version = conf_min_version;
  out->ocsp_stapling_enabled = !!ocsp_stapling_enabled;
  out->jdk11_workaround = !!jdk11_workaround;
  // handoff will always be the normal state(false) after handshake completes.
  out->handoff = false;
  // shed_handshake_config will always be false if config can be encoded(not sheded).
  out->shed_handshake_config = false;
  return 1;
}

// SSL serialization.

// Serialized SSL data version for forward compatibility
#define SSL_SERIAL_VERSION 1

static const unsigned kSSLQuietShutdownTag = 
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 0;
static const unsigned kSSLConfigTag = 
    CBS_ASN1_CONSTRUCTED | CBS_ASN1_CONTEXT_SPECIFIC | 1;

// Parse serialized SSL connection binary
//
// SSL_to_bytes_full serializes |in| to bytes stored in |cbb|.
// It returns one on success and zero on failure.
//
// An SSL is serialized as the following ASN.1 structure:
//
// SSL ::= SEQUENCE {
//     sslSerialVer      UINT64   -- version of the SSL serialization format
//     version           UINT64
//     maxSendFragement  UINT64
//     s3                SSL3State
//     mode              UINT64
//     options           UINT64
//     quietShutdown     [0] BOOLEAN OPTIONAL
//     config            [1] SEQUENCE OPTIONAL
// }
static int SSL_to_bytes_full(const SSL *in, CBB *cbb) {
  CBB ssl, child;

  if (!CBB_add_asn1(cbb, &ssl, CBS_ASN1_SEQUENCE) ||
    !CBB_add_asn1_uint64(&ssl, SSL_SERIAL_VERSION) ||
    //    FIXME add hash of SSL_CTX
    !CBB_add_asn1_uint64(&ssl, in->version) ||
    !CBB_add_asn1_uint64(&ssl, in->max_send_fragment) ||
    !SSL3_STATE_to_bytes(in->s3, &ssl) ||
    !CBB_add_asn1_uint64(&ssl, in->mode) ||
    !CBB_add_asn1_uint64(&ssl, in->options)) {
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

  if (in->config) {
    if (!CBB_add_asn1(&ssl, &child, kSSLConfigTag) ||
        !SSL_CONFIG_to_bytes(in->config.get(), &child)) {
      OPENSSL_PUT_ERROR(SSL, ERR_R_MALLOC_FAILURE);
      return 0;
    }
  }

  return CBB_flush(cbb);
}

static int SSL_parse(SSL *ssl, CBS *cbs, SSL_CTX *ctx) {
  CBS ssl_cbs, ssl_config;
  uint64_t ssl_serial_ver, version, max_send_fragment, mode, options;
  int quiet_shutdown;
  int ssl_config_present = 0;

  if (!CBS_get_asn1(cbs, &ssl_cbs, CBS_ASN1_SEQUENCE) ||
      CBS_len(cbs) != 0 ||
      !CBS_get_asn1_uint64(&ssl_cbs, &ssl_serial_ver)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL);
    return 0;
  }
  // At the moment we're simply asserting the version is correct. However
  // future updates could use SSL serial version to figure out what data
  // was actually serialized and act accordingly.
  assert(ssl_serial_ver <= SSL_SERIAL_VERSION);

  //    FIXME add hash of SSL_CTX
  // This TODO is actually a part of SSL DER struct revisit.
  if (!CBS_get_asn1_uint64(&ssl_cbs, &version) ||
    !CBS_get_asn1_uint64(&ssl_cbs, &max_send_fragment)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL);
    return 0;
  }

  ssl->version = version;
  ssl->max_send_fragment = max_send_fragment;
  SSL_set_accept_state(ssl);
  // This is called separately to avoid overriding error code.
  if (!SSL3_STATE_from_bytes(ssl, &ssl_cbs, ssl->ctx.get())) {
    return 0;
  }

  if (!CBS_get_asn1_uint64(&ssl_cbs, &mode) ||
      !CBS_get_asn1_uint64(&ssl_cbs, &options)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL);
    return 0;
  }
  ssl->mode = mode;
  ssl->options = options;

  if (!CBS_get_optional_asn1_bool(&ssl_cbs, &quiet_shutdown, kSSLQuietShutdownTag, 0 /* default to false */)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL);
    return 0;
  }
  ssl->quiet_shutdown = !!quiet_shutdown;

  if (!CBS_get_optional_asn1(&ssl_cbs, &ssl_config, &ssl_config_present, kSSLConfigTag)) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL);
    return 0;
  }

  if (ssl_config_present) {
    if (!SSL_CONFIG_from_bytes(ssl->config.get(), &ssl_config)) {
      return 0;
    }
  } else {
    ssl->config.reset();
  }

  if (CBS_len(&ssl_cbs) != 0) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL);
    return 0;
  }

  return 1;
}

SSL *SSL_from_bytes(const uint8_t *in, size_t in_len, SSL_CTX *ctx) {
  if (!in || !in_len || !ctx) {
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_UNSUPPORTED);
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
    OPENSSL_PUT_ERROR(SSL, SSL_R_SERIALIZATION_INVALID_SSL);
    return NULL;
  }

  // Restore SSL part
  if (!SSL_parse(ret.get(), &seq, ctx)) {
    return NULL;
  }

  return ret.release();
}

int SSL_to_bytes(const SSL *in, uint8_t **out_data, size_t *out_len) {
  if (!ssl_transfer_supported(in)) {
    return 0;
  }

  ScopedCBB cbb;

  CBB seq;
  if (!CBB_init(cbb.get(), 1024) ||
      !CBB_add_asn1(cbb.get(), &seq, CBS_ASN1_SEQUENCE) ||
      !SSL_to_bytes_full(in, &seq)) {
    return 0;
  }

  return CBB_finish(cbb.get(), out_data, out_len);
}
