// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <string.h>
#include <algorithm>
#include <array>
#include <atomic>

#include <string>
#include <vector>

#include <gtest/gtest.h>

#include <openssl/asn1.h>
#include <openssl/base.h>
#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/ocsp.h>
#include <openssl/x509.h>

#include "../test/test_util.h"
#include "../test/x509_util.h"
#include "internal.h"
#include "x509_view.h"

#if defined(OPENSSL_THREADS)
#include <thread>
#endif

std::string GetTestData(const char *path);

// Older g++ treats `= {}` on a multi-member aggregate as a partial initializer
// and -Wmissing-field-initializers is -Werror, so zero the view explicitly.
static AWSLC_X509_CERTIFICATE_VIEW ZeroedView(void) {
  AWSLC_X509_CERTIFICATE_VIEW view;
  OPENSSL_memset(&view, 0, sizeof(view));
  return view;
}

namespace {

bool RangeIsValid(const AWSLC_X509_DER_RANGE &range, size_t input_len) {
  return range.offset <= input_len && range.length <= input_len - range.offset;
}

bssl::Span<const uint8_t> RangeBytes(const uint8_t *der, size_t der_len,
                                     const AWSLC_X509_DER_RANGE &range) {
  EXPECT_TRUE(RangeIsValid(range, der_len));
  if (!RangeIsValid(range, der_len)) {
    return {};
  }
  return bssl::MakeConstSpan(der + range.offset, range.length);
}

std::atomic<bool> g_custom_critical_callback_called{false};

int AcceptCustomCriticalExtensions(X509_STORE_CTX *ctx, X509 *x509,
                                   STACK_OF(ASN1_OBJECT) *oids) {
  g_custom_critical_callback_called.store(true, std::memory_order_relaxed);
  return 1;
}

TEST(X509ViewParserTest, MatchesLegacyFields) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);
  ASSERT_GT(der_len, 0);

  AWSLC_X509_CERTIFICATE_VIEW view = ZeroedView();
  ASSERT_EQ(AWSLC_X509_PARSE_OK,
            x509_parse_der_view(der.get(), static_cast<size_t>(der_len),
                                /*exact=*/1, &view));
  EXPECT_EQ(2, view.version);
  EXPECT_EQ(AWSLC_X509_FLAG_EXTENSIONS,
            view.flags & AWSLC_X509_FLAG_EXTENSIONS);
  EXPECT_EQ(0, view.reserved[0]);
  EXPECT_EQ(0, view.reserved[1]);
  EXPECT_EQ(static_cast<size_t>(der_len), view.certificate.length);
  EXPECT_NE(0u, view.extension_flags &
                    (1u << AWSLC_X509_EXTENSION_BASIC_CONSTRAINTS));
  EXPECT_TRUE(RangeIsValid(
      view.extension_values[AWSLC_X509_EXTENSION_BASIC_CONSTRAINTS],
      static_cast<size_t>(der_len)));

  const uint8_t *cursor = der.get();
  bssl::UniquePtr<X509> legacy(reinterpret_cast<X509 *>(
      ASN1_item_d2i(nullptr, &cursor, der_len, ASN1_ITEM_rptr(X509))));
  ASSERT_TRUE(legacy);
  ASSERT_EQ(der.get() + der_len, cursor);
  EXPECT_EQ(X509_get_version(legacy.get()), view.version);
  const int basic_constraints_index =
      X509_get_ext_by_NID(legacy.get(), NID_basic_constraints, -1);
  ASSERT_GE(basic_constraints_index, 0);
  const int basic_constraints_critical = X509_EXTENSION_get_critical(
      X509_get_ext(legacy.get(), basic_constraints_index));
  EXPECT_EQ(basic_constraints_critical,
            (view.extension_flags &
             (1u << (AWSLC_X509_EXTENSION_CRITICAL_SHIFT +
                     AWSLC_X509_EXTENSION_BASIC_CONSTRAINTS))) != 0);

  const ASN1_INTEGER *serial = X509_get0_serialNumber(legacy.get());
  ASSERT_TRUE(serial);
  const int serial_len = i2d_ASN1_INTEGER(serial, nullptr);
  ASSERT_GT(serial_len, 0);
  std::vector<uint8_t> serial_der(static_cast<size_t>(serial_len));
  uint8_t *serial_cursor = serial_der.data();
  ASSERT_EQ(serial_len, i2d_ASN1_INTEGER(serial, &serial_cursor));
  EXPECT_EQ(Bytes(serial_der),
            Bytes(RangeBytes(der.get(), der_len, view.serial)));

  EXPECT_EQ(0x30, RangeBytes(der.get(), der_len, view.tbs_certificate)[0]);
  EXPECT_EQ(0x30, RangeBytes(der.get(), der_len, view.issuer)[0]);
  EXPECT_EQ(0x30, RangeBytes(der.get(), der_len, view.validity)[0]);
  EXPECT_EQ(0x30, RangeBytes(der.get(), der_len, view.subject)[0]);
  EXPECT_EQ(0x30, RangeBytes(der.get(), der_len, view.spki)[0]);
  EXPECT_EQ(0xa3, RangeBytes(der.get(), der_len, view.extensions)[0]);
  EXPECT_EQ(0x03, RangeBytes(der.get(), der_len, view.signature)[0]);
}

TEST(X509ViewParserTest, ExactPrefixAndFailureContract) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_leaf.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  std::vector<uint8_t> trailing(der.get(), der.get() + der_len);
  trailing.push_back(0);

  AWSLC_X509_CERTIFICATE_VIEW view;
  OPENSSL_memset(&view, 0xa5, sizeof(view));
  EXPECT_EQ(AWSLC_X509_PARSE_TRAILING_DATA,
            x509_parse_der_view(trailing.data(), trailing.size(),
                                /*exact=*/1, &view));
  EXPECT_EQ(0xa5, view.version);

  OPENSSL_memset(&view, 0, sizeof(view));
  EXPECT_EQ(AWSLC_X509_PARSE_OK,
            x509_parse_der_view(trailing.data(), trailing.size(),
                                /*exact=*/0, &view));
  EXPECT_EQ(static_cast<size_t>(der_len), view.certificate.length);

  EXPECT_EQ(AWSLC_X509_PARSE_NULL_POINTER,
            x509_parse_der_view(der.get(), der_len, 1, nullptr));
  EXPECT_EQ(AWSLC_X509_PARSE_NULL_POINTER,
            x509_parse_der_view(nullptr, 1, 1, &view));
  EXPECT_EQ(AWSLC_X509_PARSE_TRUNCATED,
            x509_parse_der_view(nullptr, 0, 1, &view));
}

TEST(X509ViewParserTest, RejectsUnmaterializableAlgorithmParameter) {
  const std::string pem = GetTestData("crypto/x509/test/some_names1.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  AWSLC_X509_CERTIFICATE_VIEW view = ZeroedView();
  ASSERT_EQ(AWSLC_X509_PARSE_OK,
            x509_parse_der_view(der.get(), static_cast<size_t>(der_len),
                                /*exact=*/1, &view));

  CBS encoded_algorithm, algorithm, oid;
  CBS_init(&encoded_algorithm, der.get() + view.signature_algorithm.offset,
           view.signature_algorithm.length);
  ASSERT_TRUE(CBS_get_asn1(&encoded_algorithm, &algorithm, CBS_ASN1_SEQUENCE));
  ASSERT_EQ(0u, CBS_len(&encoded_algorithm));
  ASSERT_TRUE(CBS_get_asn1(&algorithm, &oid, CBS_ASN1_OBJECT));
  ASSERT_EQ(2u, CBS_len(&algorithm));
  ASSERT_EQ(CBS_ASN1_NULL, CBS_data(&algorithm)[0]);
  ASSERT_EQ(0, CBS_data(&algorithm)[1]);

  std::vector<uint8_t> invalid(der.get(), der.get() + der_len);
  invalid[static_cast<size_t>(CBS_data(&algorithm) - der.get())] =
      CBS_ASN1_BOOLEAN;
  EXPECT_EQ(
      AWSLC_X509_PARSE_INVALID_ALGORITHM,
      x509_parse_der_view(invalid.data(), invalid.size(), /*exact=*/1, &view));

  const uint8_t *cursor = invalid.data();
  bssl::UniquePtr<X509> x509(
      d2i_X509(nullptr, &cursor, static_cast<long>(invalid.size())));
  EXPECT_FALSE(x509);
  EXPECT_EQ(invalid.data(), cursor);
}

TEST(X509ViewParserTest, RejectsUnmaterializableNameValue) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_leaf.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  AWSLC_X509_CERTIFICATE_VIEW view = ZeroedView();
  ASSERT_EQ(AWSLC_X509_PARSE_OK,
            x509_parse_der_view(der.get(), static_cast<size_t>(der_len),
                                /*exact=*/1, &view));

  CBS encoded_name, name, rdn, attribute, oid;
  CBS_init(&encoded_name, der.get() + view.issuer.offset, view.issuer.length);
  ASSERT_TRUE(CBS_get_asn1(&encoded_name, &name, CBS_ASN1_SEQUENCE));
  ASSERT_EQ(0u, CBS_len(&encoded_name));
  ASSERT_TRUE(CBS_get_asn1(&name, &rdn, CBS_ASN1_SET));
  ASSERT_TRUE(CBS_get_asn1(&rdn, &attribute, CBS_ASN1_SEQUENCE));
  ASSERT_TRUE(CBS_get_asn1(&attribute, &oid, CBS_ASN1_OBJECT));
  ASSERT_GT(CBS_len(&attribute), 0u);
  ASSERT_EQ(CBS_ASN1_PRINTABLESTRING, CBS_data(&attribute)[0]);
  const size_t value_tag_offset =
      static_cast<size_t>(CBS_data(&attribute) - der.get());
  CBS value;
  ASSERT_TRUE(CBS_get_asn1(&attribute, &value, CBS_ASN1_PRINTABLESTRING));
  ASSERT_GT(CBS_len(&value), 0u);
  const size_t value_content_offset =
      static_cast<size_t>(CBS_data(&value) - der.get());

  std::vector<uint8_t> invalid(der.get(), der.get() + der_len);
  invalid[value_tag_offset] = CBS_ASN1_INTEGER;
  EXPECT_EQ(
      AWSLC_X509_PARSE_INVALID_NAME,
      x509_parse_der_view(invalid.data(), invalid.size(), /*exact=*/1, &view));

  const uint8_t *cursor = invalid.data();
  bssl::UniquePtr<X509> x509(
      d2i_X509(nullptr, &cursor, static_cast<long>(invalid.size())));
  EXPECT_FALSE(x509);
  EXPECT_EQ(invalid.data(), cursor);

  invalid.assign(der.get(), der.get() + der_len);
  invalid[value_tag_offset] = CBS_ASN1_UTF8STRING;
  invalid[value_content_offset] = 0xff;
  EXPECT_EQ(
      AWSLC_X509_PARSE_INVALID_NAME,
      x509_parse_der_view(invalid.data(), invalid.size(), /*exact=*/1, &view));
  cursor = invalid.data();
  x509.reset(d2i_X509(nullptr, &cursor, static_cast<long>(invalid.size())));
  EXPECT_FALSE(x509);
  EXPECT_EQ(invalid.data(), cursor);
}

TEST(X509ViewParserTest, AcceptedSingleByteMutationsDecodeWithLegacyParser) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_leaf.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);
  std::vector<uint8_t> mutated(der.get(), der.get() + der_len);

  for (size_t offset = 0; offset < mutated.size(); offset++) {
    const uint8_t original = mutated[offset];
    for (unsigned value = 0; value <= 0xff; value++) {
      if (value == original) {
        continue;
      }
      mutated[offset] = static_cast<uint8_t>(value);
      AWSLC_X509_CERTIFICATE_VIEW view = ZeroedView();
      if (x509_parse_der_view(mutated.data(), mutated.size(), /*exact=*/1,
                              &view) == AWSLC_X509_PARSE_OK) {
        const uint8_t *cursor = mutated.data();
        bssl::UniquePtr<X509> legacy(reinterpret_cast<X509 *>(
            ASN1_item_d2i(nullptr, &cursor, static_cast<long>(mutated.size()),
                          ASN1_ITEM_rptr(X509))));
        if (legacy == nullptr || cursor != mutated.data() + mutated.size()) {
          ADD_FAILURE() << "view-only acceptance at offset " << offset
                        << " with byte " << value;
          return;
        }
      }
      ERR_clear_error();
    }
    mutated[offset] = original;
  }
}

TEST(X509ViewParserTest, D2iReturnsViewBackedCertificatePrefix) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_leaf.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  std::vector<uint8_t> input(der.get(), der.get() + der_len);
  input.push_back(0);
  input.push_back(1);

  const uint8_t *cursor = input.data();
  X509 *out = nullptr;
  bssl::UniquePtr<X509> x509(
      d2i_X509(&out, &cursor, static_cast<long>(input.size())));
  ASSERT_TRUE(x509);
  EXPECT_EQ(x509.get(), out);
  EXPECT_EQ(input.data() + der_len, cursor);
  EXPECT_EQ(nullptr, x509->cert_info);
  EXPECT_EQ(static_cast<uint32_t>(der_len), x509->view.certificate.length);

  uint8_t *encoded_raw = nullptr;
  ASSERT_EQ(der_len, i2d_X509(x509.get(), &encoded_raw));
  bssl::UniquePtr<uint8_t> encoded(encoded_raw);
  EXPECT_EQ(Bytes(der.get(), der_len), Bytes(encoded.get(), der_len));

  encoded_raw = nullptr;
  ASSERT_EQ(der_len, ASN1_item_i2d(reinterpret_cast<ASN1_VALUE *>(x509.get()),
                                   &encoded_raw, ASN1_ITEM_rptr(X509)));
  encoded.reset(encoded_raw);
  EXPECT_EQ(Bytes(der.get(), der_len), Bytes(encoded.get(), der_len));

  ASSERT_TRUE(X509_up_ref(x509.get()));
  X509_free(x509.get());
  EXPECT_EQ(X509_VERSION_3, X509_get_version(x509.get()));
}

TEST(X509ViewParserTest, D2iFailureDoesNotAdvanceInput) {
  const uint8_t invalid[] = {0x30, 0x03, 0x01, 0x01, 0xff};
  const uint8_t *cursor = invalid;
  X509 *out = nullptr;
  bssl::UniquePtr<X509> x509(
      d2i_X509(&out, &cursor, static_cast<long>(sizeof(invalid))));
  EXPECT_FALSE(x509);
  EXPECT_EQ(nullptr, out);
  EXPECT_EQ(invalid, cursor);
}

TEST(X509ViewParserTest, ViewBackedX509DefersMaterialization) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);
  ASSERT_EQ(nullptr, x509->cert_info);

  EXPECT_EQ(X509_VERSION_3, X509_get_version(x509.get()));
  EXPECT_EQ(nullptr, x509->cert_info);

  uint8_t *encoded_raw = nullptr;
  ASSERT_EQ(der_len, i2d_X509(x509.get(), &encoded_raw));
  bssl::UniquePtr<uint8_t> encoded(encoded_raw);
  EXPECT_EQ(Bytes(der.get(), der_len), Bytes(encoded.get(), der_len));
  EXPECT_EQ(nullptr, x509->cert_info);

  uint8_t *tbs_raw = nullptr;
  const int tbs_len = i2d_X509_tbs(x509.get(), &tbs_raw);
  ASSERT_GT(tbs_len, 0);
  bssl::UniquePtr<uint8_t> tbs(tbs_raw);
  EXPECT_EQ(Bytes(RangeBytes(der.get(), der_len, x509->view.tbs_certificate)),
            Bytes(tbs.get(), tbs_len));
  EXPECT_EQ(nullptr, x509->cert_info);

  const ASN1_INTEGER *serial = X509_get0_serialNumber(x509.get());
  ASSERT_NE(nullptr, serial);
  EXPECT_EQ(nullptr, x509->cert_info);
  EXPECT_EQ(serial, x509->view_serial);
}

TEST(X509ViewParserTest, DigestUsesPristineCertificateView) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_leaf.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  const uint8_t *cursor = der.get();
  bssl::UniquePtr<X509> x509(d2i_X509(nullptr, &cursor, der_len));
  ASSERT_TRUE(x509);
  ASSERT_EQ(nullptr, x509->cert_info);

  uint8_t expected[EVP_MAX_MD_SIZE];
  uint8_t actual[EVP_MAX_MD_SIZE];
  unsigned expected_len = 0;
  unsigned actual_len = 0;
  ASSERT_TRUE(EVP_Digest(der.get(), der_len, expected, &expected_len,
                         EVP_sha1(), nullptr));
  ASSERT_TRUE(X509_digest(x509.get(), EVP_sha1(), actual, &actual_len));
  EXPECT_EQ(expected_len, actual_len);
  EXPECT_EQ(Bytes(expected, expected_len), Bytes(actual, actual_len));
  EXPECT_EQ(nullptr, x509->cert_info);
}

TEST(X509ViewParserTest, CommonFieldsMaterializeIndependently) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);

  EXPECT_NE(nullptr, X509_get_issuer_name(x509.get()));
  EXPECT_EQ(nullptr, x509->cert_info);
  EXPECT_NE(nullptr, x509->view_issuer);
  EXPECT_NE(nullptr, X509_get_subject_name(x509.get()));
  EXPECT_EQ(nullptr, x509->cert_info);
  EXPECT_NE(nullptr, x509->view_subject);
  EXPECT_NE(nullptr, X509_get0_notBefore(x509.get()));
  EXPECT_NE(nullptr, X509_get0_notAfter(x509.get()));
  EXPECT_EQ(nullptr, x509->cert_info);
  EXPECT_NE(nullptr, x509->view_validity);
  EXPECT_NE(nullptr, X509_get0_pubkey(x509.get()));
  EXPECT_EQ(nullptr, x509->cert_info);
  EXPECT_NE(nullptr, x509->view_key);

  int critical = -1;
  bssl::UniquePtr<BASIC_CONSTRAINTS> basic_constraints(
      static_cast<BASIC_CONSTRAINTS *>(X509_get_ext_d2i(
          x509.get(), NID_basic_constraints, &critical, nullptr)));
  EXPECT_NE(nullptr, basic_constraints);
  EXPECT_EQ(1, critical);
  EXPECT_EQ(nullptr, x509->view_extensions);

  EXPECT_GT(X509_get_ext_count(x509.get()), 0);
  EXPECT_EQ(nullptr, x509->cert_info);
  EXPECT_NE(nullptr, x509->view_extensions);
}

TEST(X509ViewParserTest, MaterializationFailureIsRetryable) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);

  const AWSLC_X509_DER_RANGE subject = x509->view.subject;
  x509->view.subject = x509->view.signature;
  EXPECT_EQ(nullptr, X509_get_subject_name(x509.get()));
  EXPECT_EQ(X509_VIEW_STATE_PARSED, x509->view_state);

  x509->view.subject = subject;
  EXPECT_NE(nullptr, X509_get_subject_name(x509.get()));
  EXPECT_EQ(X509_VIEW_STATE_PARSED, x509->view_state);
}

TEST(X509ViewParserTest, ExtensionMaterializationFailureIsReported) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);

  const AWSLC_X509_DER_RANGE extensions = x509->view.extensions;
  x509->view.extensions = x509->view.signature;
  ERR_clear_error();
  EXPECT_EQ(-1, X509_get_ext_count(x509.get()));
  EXPECT_NE(0u, ERR_peek_error());
  EXPECT_EQ(nullptr, x509->view_extensions);

  ERR_clear_error();
  EXPECT_EQ(-1, X509_get_ext_by_NID(x509.get(), NID_basic_constraints, -1));
  EXPECT_NE(0u, ERR_peek_error());

  ERR_clear_error();
  EXPECT_EQ(-1, X509_get_ext_by_OBJ(x509.get(),
                                    OBJ_nid2obj(NID_basic_constraints), -1));
  EXPECT_NE(0u, ERR_peek_error());

  ERR_clear_error();
  EXPECT_EQ(-1, X509_get_ext_by_critical(x509.get(), 1, -1));
  EXPECT_NE(0u, ERR_peek_error());

  ERR_clear_error();
  EXPECT_EQ(nullptr, X509_get_ext(x509.get(), 0));
  EXPECT_NE(0u, ERR_peek_error());

  ERR_clear_error();
  EXPECT_EQ(nullptr, X509_delete_ext(x509.get(), 0));
  EXPECT_NE(0u, ERR_peek_error());

  int critical = -1;
  int index = -1;
  ERR_clear_error();
  EXPECT_EQ(nullptr, X509_get_ext_d2i(x509.get(), NID_basic_constraints,
                                      &critical, &index));
  EXPECT_NE(0u, ERR_peek_error());

  ERR_clear_error();
  x509->view.extensions = extensions;
  EXPECT_GT(X509_get_ext_count(x509.get()), 0);
}

TEST(X509ViewParserTest,
     CustomCriticalVerificationRejectsExtensionMaterializationFailure) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);

  // Simulate an already-cached unknown critical extension, then make deferred
  // extension materialization fail. Verification must stop before delegating
  // validation to the consumer callback.
  x509->ex_flags |= EXFLAG_SET | EXFLAG_CRITICAL | EXFLAG_CA | EXFLAG_SS;
  x509->view.extensions = x509->view.signature;
  bssl::UniquePtr<ASN1_OBJECT> custom_oid(OBJ_txt2obj("1.2.3.4", 1));
  ASSERT_TRUE(custom_oid);
  g_custom_critical_callback_called.store(false, std::memory_order_relaxed);

  auto configure = [&](X509_STORE_CTX *ctx) {
    ASSERT_TRUE(X509_STORE_CTX_add_custom_crit_oid(ctx, custom_oid.get()));
    X509_STORE_CTX_set_verify_crit_oids(ctx, AcceptCustomCriticalExtensions);
  };
  EXPECT_EQ(X509_V_ERR_UNHANDLED_CRITICAL_EXTENSION,
            Verify(x509.get(), {x509.get()}, {}, {}, 0, configure));
  EXPECT_FALSE(
      g_custom_critical_callback_called.load(std::memory_order_relaxed));
}

TEST(X509ViewParserTest, ComparisonHelpersRejectMaterializationFailure) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  auto parse = [&]() {
    bssl::UniquePtr<CRYPTO_BUFFER> buffer(
        CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
    return bssl::UniquePtr<X509>(
        buffer == nullptr ? nullptr : X509_parse_from_buffer(buffer.get()));
  };

  bssl::UniquePtr<X509> reference = parse();
  ASSERT_TRUE(reference);
  X509_NAME *issuer_name = X509_get_issuer_name(reference.get());
  X509_NAME *subject_name = X509_get_subject_name(reference.get());
  const ASN1_INTEGER *serial = X509_get0_serialNumber(reference.get());
  ASSERT_TRUE(issuer_name);
  ASSERT_TRUE(subject_name);
  ASSERT_TRUE(serial);

  bssl::UniquePtr<X509> candidate = parse();
  ASSERT_TRUE(candidate);
  STACK_OF(X509) *certificates = sk_X509_new_null();
  ASSERT_TRUE(certificates);
  ASSERT_TRUE(sk_X509_push(certificates, candidate.get()));

  candidate->view.subject = candidate->view.signature;
  ERR_clear_error();
  EXPECT_EQ(nullptr, X509_find_by_subject(certificates, subject_name));
  EXPECT_NE(0u, ERR_peek_error());
  EXPECT_EQ(X509_V_ERR_UNSPECIFIED,
            X509_check_issued(candidate.get(), reference.get()));
  bssl::UniquePtr<NAME_CONSTRAINTS> constraints(NAME_CONSTRAINTS_new());
  ASSERT_TRUE(constraints);
  EXPECT_EQ(X509_V_ERR_OUT_OF_MEM,
            NAME_CONSTRAINTS_check(candidate.get(), constraints.get()));
  EXPECT_EQ(nullptr, X509_get1_email(candidate.get()));

  bssl::UniquePtr<X509> next_candidate = parse();
  ASSERT_TRUE(next_candidate);
  ASSERT_EQ(next_candidate.get(),
            sk_X509_set(certificates, 0, next_candidate.get()));
  candidate = std::move(next_candidate);
  candidate->view.serial = candidate->view.signature;
  ERR_clear_error();
  EXPECT_EQ(nullptr, X509_find_by_issuer_and_serial(certificates, issuer_name,
                                                    serial));
  EXPECT_NE(0u, ERR_peek_error());
  EXPECT_EQ(nullptr,
            OCSP_cert_to_id(nullptr, candidate.get(), reference.get()));

  next_candidate = parse();
  ASSERT_TRUE(next_candidate);
  ASSERT_EQ(next_candidate.get(),
            sk_X509_set(certificates, 0, next_candidate.get()));
  candidate = std::move(next_candidate);
  candidate->view.issuer = candidate->view.signature;
  ERR_clear_error();
  EXPECT_EQ(nullptr, X509_find_by_issuer_and_serial(certificates, issuer_name,
                                                    serial));
  EXPECT_NE(0u, ERR_peek_error());
  EXPECT_EQ(nullptr,
            OCSP_cert_to_id(nullptr, candidate.get(), reference.get()));
  sk_X509_free(certificates);
}

TEST(X509ViewParserTest, CountsCompatibilityFallbacks) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);
  std::vector<uint8_t> noncanonical(der.get(), der.get() + der_len);

  static const uint8_t kCriticalBasicConstraints[] = {
      0x06, 0x03, 0x55, 0x1d, 0x13, 0x01, 0x01, 0xff,
  };
  const auto critical = std::search(noncanonical.begin(), noncanonical.end(),
                                    std::begin(kCriticalBasicConstraints),
                                    std::end(kCriticalBasicConstraints));
  ASSERT_NE(noncanonical.end(), critical);
  ASSERT_EQ(noncanonical.end(),
            std::search(critical + 1, noncanonical.end(),
                        std::begin(kCriticalBasicConstraints),
                        std::end(kCriticalBasicConstraints)));
  critical[sizeof(kCriticalBasicConstraints) - 1] = 0x01;

  AWSLC_X509_CERTIFICATE_VIEW view = ZeroedView();
  ASSERT_EQ(AWSLC_X509_PARSE_INVALID_EXTENSIONS,
            x509_parse_der_view(noncanonical.data(), noncanonical.size(),
                                /*exact=*/1, &view));

  x509_view_reset_fallback_counts_for_testing();
  const uint8_t *cursor = noncanonical.data();
  bssl::UniquePtr<X509> x509(
      d2i_X509(nullptr, &cursor, static_cast<long>(noncanonical.size())));
  ASSERT_TRUE(x509);
  EXPECT_EQ(noncanonical.data() + noncanonical.size(), cursor);
  EXPECT_NE(nullptr, x509->cert_info);
  EXPECT_EQ(1u, x509_view_fallback_count_for_testing(
                    AWSLC_X509_PARSE_INVALID_EXTENSIONS));
}

TEST(X509ViewParserTest, DupPreservesParsedView) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);
  ASSERT_EQ(nullptr, x509->cert_info);

  bssl::UniquePtr<X509> duplicate(X509_dup(x509.get()));
  ASSERT_TRUE(duplicate);
  EXPECT_EQ(nullptr, duplicate->cert_info);
  EXPECT_EQ(X509_VIEW_STATE_PARSED, duplicate->view_state);
  EXPECT_EQ(x509->view.certificate.offset, duplicate->view.certificate.offset);
  EXPECT_EQ(x509->view.certificate.length, duplicate->view.certificate.length);

  uint8_t *encoded_raw = nullptr;
  ASSERT_EQ(der_len, i2d_X509(duplicate.get(), &encoded_raw));
  bssl::UniquePtr<uint8_t> encoded(encoded_raw);
  EXPECT_EQ(Bytes(der.get(), der_len), Bytes(encoded.get(), der_len));
}

TEST(X509ViewParserTest, MutableCachedFieldSurvivesFullMaterialization) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);

  ASN1_INTEGER *serial = X509_get_serialNumber(x509.get());
  ASSERT_NE(nullptr, serial);
  ASSERT_TRUE(ASN1_INTEGER_set(serial, 42));
  ASSERT_EQ(nullptr, x509->cert_info);

  uint8_t *encoded_raw = nullptr;
  const int encoded_len = i2d_X509(x509.get(), &encoded_raw);
  ASSERT_GT(encoded_len, 0);
  bssl::UniquePtr<uint8_t> encoded(encoded_raw);
  ASSERT_EQ(nullptr, x509->cert_info);

  const uint8_t *cursor = encoded.get();
  bssl::UniquePtr<X509> reparsed(
      d2i_X509(nullptr, &cursor, static_cast<long>(encoded_len)));
  ASSERT_TRUE(reparsed);
  EXPECT_NE(42, ASN1_INTEGER_get(X509_get0_serialNumber(reparsed.get())));

  ASSERT_GT(i2d_re_X509_tbs(x509.get(), nullptr), 0);
  encoded.reset();
  encoded_raw = nullptr;
  const int reencoded_len = i2d_X509(x509.get(), &encoded_raw);
  ASSERT_GT(reencoded_len, 0);
  encoded.reset(encoded_raw);
  cursor = encoded.get();
  reparsed.reset(d2i_X509(nullptr, &cursor, static_cast<long>(reencoded_len)));
  ASSERT_TRUE(reparsed);
  EXPECT_EQ(42, ASN1_INTEGER_get(X509_get0_serialNumber(reparsed.get())));
}

TEST(X509ViewParserTest, VerifyUsesRetainedTbsAfterExtensionCaching) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);
  bssl::UniquePtr<EVP_PKEY> key(X509_get_pubkey(x509.get()));
  ASSERT_TRUE(key);
  EXPECT_EQ(nullptr, x509->cert_info);

  (void)X509_check_ca(x509.get());
  ASSERT_EQ(nullptr, x509->cert_info);
  ASSERT_NE(0, x509->view_materialized);

  EXPECT_EQ(1, X509_verify(x509.get(), key.get()));
  EXPECT_EQ(nullptr, x509->cert_info);
}

TEST(X509ViewParserTest, ExtensionCacheObservesMutableExtension) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);

  const int index =
      X509_get_ext_by_NID(x509.get(), NID_basic_constraints, /*lastpos=*/-1);
  ASSERT_GE(index, 0);
  X509_EXTENSION *extension = X509_get_ext(x509.get(), index);
  ASSERT_TRUE(extension);
  ASSERT_TRUE(X509_EXTENSION_set_object(extension, OBJ_get_undef()));
  ASSERT_TRUE(X509_EXTENSION_set_critical(extension, /*crit=*/1));

  const uint32_t flags = X509_get_extension_flags(x509.get());
  EXPECT_EQ(0u, flags & (EXFLAG_BCONS | EXFLAG_CA));
  EXPECT_NE(0u, flags & EXFLAG_CRITICAL);
  EXPECT_EQ(nullptr, x509->cert_info);
}

TEST(X509ViewParserTest, SignatureAccessorsStaySelective) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);

  const ASN1_BIT_STRING *signature = nullptr;
  const X509_ALGOR *outer_algorithm = nullptr;
  X509_get0_signature(&signature, &outer_algorithm, x509.get());
  EXPECT_NE(nullptr, signature);
  EXPECT_NE(nullptr, outer_algorithm);
  EXPECT_EQ(OBJ_obj2nid(outer_algorithm->algorithm),
            X509_get_signature_nid(x509.get()));
  EXPECT_NE(nullptr, X509_get0_tbs_sigalg(x509.get()));
  EXPECT_EQ(nullptr, x509->cert_info);
  EXPECT_NE(nullptr, x509->view_signature);
  EXPECT_NE(nullptr, x509->view_sig_alg);
  EXPECT_NE(nullptr, x509->view_tbs_sig_alg);

  X509_get0_uids(x509.get(), nullptr, nullptr);
  ASSERT_NE(nullptr, x509->cert_info);
  EXPECT_EQ(signature, x509->signature);
  EXPECT_EQ(outer_algorithm, x509->sig_alg);
}

TEST(X509ViewParserTest, CertificateWithoutExtensionsStaysSelective) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_none.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  AWSLC_X509_CERTIFICATE_VIEW view = ZeroedView();
  ASSERT_EQ(AWSLC_X509_PARSE_OK,
            x509_parse_der_view(der.get(), static_cast<size_t>(der_len),
                                /*exact=*/1, &view));

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);
  EXPECT_EQ(0, X509_get_ext_count(x509.get()));
  EXPECT_NE(nullptr, x509->view_extensions);
  EXPECT_EQ(nullptr, x509->cert_info);

  bssl::UniquePtr<EVP_PKEY> key(X509_get_pubkey(x509.get()));
  ASSERT_TRUE(key);
  EXPECT_EQ(0, X509_check_ca(x509.get()));
  EXPECT_EQ(1, X509_verify(x509.get(), key.get()));
  EXPECT_EQ(nullptr, x509->cert_info);
}

TEST(X509ViewParserTest, ViewBackedX509ComparisonUsesExtensionView) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer1(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  bssl::UniquePtr<CRYPTO_BUFFER> buffer2(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer1);
  ASSERT_TRUE(buffer2);
  bssl::UniquePtr<X509> x5091(X509_parse_from_buffer(buffer1.get()));
  bssl::UniquePtr<X509> x5092(X509_parse_from_buffer(buffer2.get()));
  ASSERT_TRUE(x5091);
  ASSERT_TRUE(x5092);
  ASSERT_EQ(nullptr, x5091->cert_info);
  ASSERT_EQ(nullptr, x5092->cert_info);

  EXPECT_EQ(0, X509_cmp(x5091.get(), x5092.get()));
  EXPECT_EQ(nullptr, x5091->cert_info);
  EXPECT_EQ(nullptr, x5092->cert_info);
  EXPECT_EQ(nullptr, x5091->view_extensions);
  EXPECT_EQ(nullptr, x5092->view_extensions);
}

TEST(X509ViewParserTest, ComparisonHashesCertificatesOnCacheFailure) {
  const std::string pem1 =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  const std::string pem2 =
      GetTestData("crypto/x509/test/basic_constraints_leaf.pem");
  uint8_t *der1_raw = nullptr;
  uint8_t *der2_raw = nullptr;
  long der1_len = 0;
  long der2_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem1.c_str(), &der1_raw, &der1_len));
  ASSERT_TRUE(PEM_to_DER(pem2.c_str(), &der2_raw, &der2_len));
  bssl::UniquePtr<uint8_t> der1(der1_raw);
  bssl::UniquePtr<uint8_t> der2(der2_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer1(
      CRYPTO_BUFFER_new(der1.get(), der1_len, nullptr));
  bssl::UniquePtr<CRYPTO_BUFFER> buffer2(
      CRYPTO_BUFFER_new(der2.get(), der2_len, nullptr));
  ASSERT_TRUE(buffer1);
  ASSERT_TRUE(buffer2);
  bssl::UniquePtr<X509> x5091(X509_parse_from_buffer(buffer1.get()));
  bssl::UniquePtr<X509> x5092(X509_parse_from_buffer(buffer2.get()));
  ASSERT_TRUE(x5091);
  ASSERT_TRUE(x5092);

  x5091->view.subject = x5091->view.signature;
  x5092->view.subject = x5092->view.signature;
  EXPECT_NE(0, X509_cmp(x5091.get(), x5092.get()));
  EXPECT_EQ(static_cast<uint32_t>(EXFLAG_SET | EXFLAG_INVALID),
            x5091->ex_flags & (EXFLAG_SET | EXFLAG_INVALID));
  EXPECT_EQ(static_cast<uint32_t>(EXFLAG_SET | EXFLAG_INVALID),
            x5092->ex_flags & (EXFLAG_SET | EXFLAG_INVALID));
  EXPECT_NE(Bytes(x5091->cert_hash, sizeof(x5091->cert_hash)),
            Bytes(x5092->cert_hash, sizeof(x5092->cert_hash)));
}

#if defined(OPENSSL_THREADS)
TEST(X509ViewParserTest, ConcurrentFirstMaterialization) {
  const std::string pem =
      GetTestData("crypto/x509/test/basic_constraints_ca.pem");
  uint8_t *der_raw = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(pem.c_str(), &der_raw, &der_len));
  bssl::UniquePtr<uint8_t> der(der_raw);

  bssl::UniquePtr<CRYPTO_BUFFER> buffer(
      CRYPTO_BUFFER_new(der.get(), der_len, nullptr));
  ASSERT_TRUE(buffer);
  bssl::UniquePtr<X509> x509(X509_parse_from_buffer(buffer.get()));
  ASSERT_TRUE(x509);
  ASSERT_EQ(nullptr, x509->cert_info);

  constexpr size_t kThreadCount = 8;
  std::atomic<size_t> ready{0};
  std::atomic<bool> start{false};
  std::array<const ASN1_INTEGER *, kThreadCount> results;
  results.fill(nullptr);
  std::array<std::thread, kThreadCount> threads;
  for (size_t i = 0; i < kThreadCount; i++) {
    threads[i] = std::thread([&, i] {
      ready.fetch_add(1, std::memory_order_release);
      while (!start.load(std::memory_order_acquire)) {
        std::this_thread::yield();
      }
      results[i] = X509_get0_serialNumber(x509.get());
    });
  }

  while (ready.load(std::memory_order_acquire) != kThreadCount) {
    std::this_thread::yield();
  }
  start.store(true, std::memory_order_release);
  for (std::thread &thread : threads) {
    thread.join();
  }

  for (const ASN1_INTEGER *result : results) {
    EXPECT_NE(nullptr, result);
    EXPECT_EQ(results[0], result);
  }
  EXPECT_EQ(nullptr, x509->cert_info);
  EXPECT_EQ(results[0], x509->view_serial);
}
#endif  // OPENSSL_THREADS

// A leading byte-order mark is rejected by |ASN1_mbstring_ncopy| during
// |X509_NAME| canonicalization, which the legacy decoder always runs for
// BMPString and UniversalString. The view parser must reject it too: otherwise
// |d2i_X509| accepts a certificate whose issuer and subject can never be
// materialized, and every name accessor returns NULL for a parsed certificate.
TEST(X509ViewParserTest, RejectsLeadingByteOrderMarkInNameValue) {
  // 221 bytes
  static const uint8_t kBmpBom[] = {
      0x30, 0x81, 0xda, 0x30, 0x81, 0xc0, 0xa0, 0x03, 0x02, 0x01, 0x02, 0x02,
      0x01, 0x01, 0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04,
      0x03, 0x02, 0x30, 0x0f, 0x31, 0x0d, 0x30, 0x0b, 0x06, 0x03, 0x55, 0x04,
      0x03, 0x1e, 0x04, 0xfe, 0xff, 0x00, 0x41, 0x30, 0x1e, 0x17, 0x0d, 0x32,
      0x35, 0x30, 0x31, 0x30, 0x31, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x5a,
      0x17, 0x0d, 0x33, 0x35, 0x30, 0x31, 0x30, 0x31, 0x30, 0x30, 0x30, 0x30,
      0x30, 0x30, 0x5a, 0x30, 0x0f, 0x31, 0x0d, 0x30, 0x0b, 0x06, 0x03, 0x55,
      0x04, 0x03, 0x1e, 0x04, 0xfe, 0xff, 0x00, 0x41, 0x30, 0x59, 0x30, 0x13,
      0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01, 0x06, 0x08, 0x2a,
      0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07, 0x03, 0x42, 0x00, 0x04, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0xa3, 0x0d, 0x30, 0x0b, 0x30, 0x09, 0x06, 0x03, 0x55,
      0x1d, 0x13, 0x04, 0x02, 0x30, 0x00, 0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86,
      0x48, 0xce, 0x3d, 0x04, 0x03, 0x02, 0x03, 0x09, 0x00, 0x30, 0x06, 0x02,
      0x01, 0x01, 0x02, 0x01, 0x01,
  };
  // 229 bytes
  static const uint8_t kUnivBom[] = {
      0x30, 0x81, 0xe2, 0x30, 0x81, 0xc8, 0xa0, 0x03, 0x02, 0x01, 0x02, 0x02,
      0x01, 0x01, 0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04,
      0x03, 0x02, 0x30, 0x13, 0x31, 0x11, 0x30, 0x0f, 0x06, 0x03, 0x55, 0x04,
      0x03, 0x1c, 0x08, 0x00, 0x00, 0xfe, 0xff, 0x00, 0x00, 0x00, 0x41, 0x30,
      0x1e, 0x17, 0x0d, 0x32, 0x35, 0x30, 0x31, 0x30, 0x31, 0x30, 0x30, 0x30,
      0x30, 0x30, 0x30, 0x5a, 0x17, 0x0d, 0x33, 0x35, 0x30, 0x31, 0x30, 0x31,
      0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x5a, 0x30, 0x13, 0x31, 0x11, 0x30,
      0x0f, 0x06, 0x03, 0x55, 0x04, 0x03, 0x1c, 0x08, 0x00, 0x00, 0xfe, 0xff,
      0x00, 0x00, 0x00, 0x41, 0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2a, 0x86,
      0x48, 0xce, 0x3d, 0x02, 0x01, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d,
      0x03, 0x01, 0x07, 0x03, 0x42, 0x00, 0x04, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0xa3,
      0x0d, 0x30, 0x0b, 0x30, 0x09, 0x06, 0x03, 0x55, 0x1d, 0x13, 0x04, 0x02,
      0x30, 0x00, 0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04,
      0x03, 0x02, 0x03, 0x09, 0x00, 0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01,
      0x01,
  };

  struct {
    const char *name;
    const uint8_t *der;
    size_t der_len;
  } kCases[] = {
      {"BMPString", kBmpBom, sizeof(kBmpBom)},
      {"UniversalString", kUnivBom, sizeof(kUnivBom)},
  };

  for (const auto &t : kCases) {
    SCOPED_TRACE(t.name);
    AWSLC_X509_CERTIFICATE_VIEW view = ZeroedView();
    EXPECT_NE(AWSLC_X509_PARSE_OK,
              x509_parse_der_view(t.der, t.der_len, /*exact=*/1, &view));

    // The legacy decoder rejects it as well, so acceptance is unchanged.
    const uint8_t *legacy_cursor = t.der;
    bssl::UniquePtr<X509> legacy(reinterpret_cast<X509 *>(ASN1_item_d2i(
        nullptr, &legacy_cursor, t.der_len, ASN1_ITEM_rptr(X509))));
    EXPECT_FALSE(legacy);

    const uint8_t *cursor = t.der;
    bssl::UniquePtr<X509> x509(d2i_X509(nullptr, &cursor, t.der_len));
    EXPECT_FALSE(x509);
    ERR_clear_error();
  }
}


// Assembles a minimal v3 certificate whose issuer and subject are both |name|,
// so a test case only has to supply the Name it wants to exercise.
static std::vector<uint8_t> CertWithName(bssl::Span<const uint8_t> name) {
  static const char kVersionSerialAlg[] = "a003020102020101300a06082a8648ce3d040302";
  static const char kValidity[] = "301e170d3235303130313030303030305a170d3335303130313030303030305a";
  static const char kSpki[] = "3059301306072a8648ce3d020106082a8648ce3d0301070342000411111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111";
  static const char kExtensions[] = "a30d300b30090603551d1304023000";
  static const char kSigAlgAndSignature[] = "300a06082a8648ce3d0403020309003006020101020101";

  std::vector<uint8_t> prefix, validity, spki, extensions, suffix;
  BSSL_CHECK(DecodeHex(&prefix, kVersionSerialAlg));
  BSSL_CHECK(DecodeHex(&validity, kValidity));
  BSSL_CHECK(DecodeHex(&spki, kSpki));
  BSSL_CHECK(DecodeHex(&extensions, kExtensions));
  BSSL_CHECK(DecodeHex(&suffix, kSigAlgAndSignature));

  std::vector<uint8_t> tbs_body;
  auto append = [&tbs_body](bssl::Span<const uint8_t> s) {
    tbs_body.insert(tbs_body.end(), s.begin(), s.end());
  };
  append(prefix);
  append(name);
  append(validity);
  append(name);
  append(spki);
  append(extensions);

  // DER header for a SEQUENCE. Every body here is well under 64 KiB.
  auto header = [](size_t len) {
    std::vector<uint8_t> out = {0x30};
    if (len < 0x80) {
      out.push_back(static_cast<uint8_t>(len));
    } else if (len < 0x100) {
      out.push_back(0x81);
      out.push_back(static_cast<uint8_t>(len));
    } else {
      out.push_back(0x82);
      out.push_back(static_cast<uint8_t>(len >> 8));
      out.push_back(static_cast<uint8_t>(len));
    }
    return out;
  };

  std::vector<uint8_t> tbs = header(tbs_body.size());
  tbs.insert(tbs.end(), tbs_body.begin(), tbs_body.end());

  std::vector<uint8_t> cert_body = tbs;
  cert_body.insert(cert_body.end(), suffix.begin(), suffix.end());
  std::vector<uint8_t> cert = header(cert_body.size());
  cert.insert(cert.end(), cert_body.begin(), cert_body.end());
  return cert;
}

// Exercises the Name validators the view parser applies: DER SET OF ordering
// for multi-valued RDNs, and the UTF8String / BMPString / UniversalString
// content checks. Each case also re-asserts the subset invariant, so a parser
// that starts accepting something the legacy decoder rejects fails here rather
// than surfacing later as a NULL from X509_get_subject_name.
TEST(X509ViewParserTest, ValidatesNameValueEncodings) {
  struct {
    const char *description;
    const char *name_hex;
    bool view_accepts;
  } kCases[] = {
      {"multi-valued RDN in DER order",
       "302631243009060355040613025553300a060355040a13034f7267300b060355040313044c656166",
       true},
      {"multi-valued RDN out of order",
       "30263124300b060355040313044c656166300a060355040a13034f72673009060355040613025553",
       false},
      {"UTF8String two-byte sequence",
       "3010310e300c06035504030c05636166c3a9",
       true},
      {"UTF8String three-byte sequence",
       "3011310f300d06035504030c06e4b8ade69687",
       true},
      {"UTF8String four-byte sequence",
       "300f310d300b06035504030c04f09f9880",
       true},
      {"UTF8String overlong encoding",
       "300d310b300906035504030c02c080",
       false},
      {"UTF8String bad continuation byte",
       "300e310c300a06035504030c03e228a1",
       false},
      {"UTF8String truncated sequence",
       "300d310b300906035504030c02e282",
       false},
      {"UTF8String surrogate code point",
       "300e310c300a06035504030c03eda080",
       false},
      {"BMPString non-ASCII",
       "30133111300f06035504031e0800630061006600e9",
       true},
      {"BMPString odd length",
       "300e310c300a06035504031e03004100",
       false},
      {"BMPString surrogate code point",
       "300d310b300906035504031e02d800",
       false},
      {"BMPString noncharacter",
       "300d310b300906035504031e02fffe",
       false},
      {"UniversalString non-ASCII",
       "301b3119301706035504031c10000000630000006100000066000000e9",
       true},
      {"UniversalString length not a multiple of four",
       "3010310e300c06035504031c050000004100",
       false},
      {"UniversalString code point out of range",
       "300f310d300b06035504031c0400110000",
       false},
  };

  for (const auto &t : kCases) {
    SCOPED_TRACE(t.description);
    std::vector<uint8_t> name;
    ASSERT_TRUE(DecodeHex(&name, t.name_hex));
    const std::vector<uint8_t> cert = CertWithName(name);

    AWSLC_X509_CERTIFICATE_VIEW view = ZeroedView();
    const uint32_t result =
        x509_parse_der_view(cert.data(), cert.size(), /*exact=*/1, &view);
    EXPECT_EQ(t.view_accepts, result == AWSLC_X509_PARSE_OK);

    // Subset invariant: anything the view parser accepts, the legacy object
    // model must accept too, or the parsed certificate would have fields that
    // can never be materialized.
    const uint8_t *legacy_cursor = cert.data();
    bssl::UniquePtr<X509> legacy(reinterpret_cast<X509 *>(ASN1_item_d2i(
        nullptr, &legacy_cursor, cert.size(), ASN1_ITEM_rptr(X509))));
    if (result == AWSLC_X509_PARSE_OK) {
      EXPECT_TRUE(legacy);
    }
    ERR_clear_error();

    // d2i_X509 falls back to the legacy decoder, so acceptance overall is
    // whatever the legacy decoder says.
    const uint8_t *cursor = cert.data();
    bssl::UniquePtr<X509> x509(d2i_X509(nullptr, &cursor, cert.size()));
    if (x509) {
      EXPECT_TRUE(X509_get_subject_name(x509.get()));
      EXPECT_TRUE(X509_get_issuer_name(x509.get()));
    }
    ERR_clear_error();
  }
}

}  // namespace
