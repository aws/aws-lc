// Copyright (c) 2016, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/x509.h>

#include "../crypto/x509/internal.h"
#include "../crypto/x509/x509_view.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  AWSLC_X509_CERTIFICATE_VIEW view;
  OPENSSL_memset(&view, 0, sizeof(view));
  if (x509_parse_der_view(buf, len, /*exact=*/1, &view) ==
      AWSLC_X509_PARSE_OK) {
    const uint8_t *legacy_cursor = buf;
    bssl::UniquePtr<X509> legacy(reinterpret_cast<X509 *>(
        ASN1_item_d2i(nullptr, &legacy_cursor, len, ASN1_ITEM_rptr(X509))));
    // View-backed objects defer these same legacy decodes. A view parse must
    // therefore never accept an input that the legacy object model rejects.
    BSSL_CHECK(legacy != nullptr);
    BSSL_CHECK(legacy_cursor == buf + len);
  }

  bssl::UniquePtr<X509> x509(d2i_X509(nullptr, &buf, len));
  if (x509 != nullptr) {
    // Extract the public key.
    EVP_PKEY_free(X509_get_pubkey(x509.get()));

    // Fuzz some deferred parsing.
    x509v3_cache_extensions(x509.get());

    // Fuzz every supported extension.
    for (int i = 0; i < X509_get_ext_count(x509.get()); i++) {
      const X509_EXTENSION *ext = X509_get_ext(x509.get(), i);
      void *parsed = X509V3_EXT_d2i(ext);
      if (parsed != nullptr) {
        int nid = OBJ_obj2nid(X509_EXTENSION_get_object(ext));
        BSSL_CHECK(nid != NID_undef);

        // Reserialize the extension. This should succeed if we were able to
        // parse it.
        // TODO(crbug.com/boringssl/352): Ideally we would also assert that
        // |new_ext| is identical to |ext|, but our parser is not strict enough.
        bssl::UniquePtr<X509_EXTENSION> new_ext(
            X509V3_EXT_i2d(nid, X509_EXTENSION_get_critical(ext), parsed));
        BSSL_CHECK(new_ext != nullptr);

        // This can only fail if |ext| was not a supported type, but then
        // |X509V3_EXT_d2i| should have failed.
        BSSL_CHECK(X509V3_EXT_free(nid, parsed));
      }
    }

    // Reserialize |x509|. This should succeed if we were able to parse it.
    // TODO(crbug.com/boringssl/352): Ideally we would also assert the output
    // matches the input, but our parser is not strict enough.
    uint8_t *der = nullptr;
    int der_len = i2d_X509(x509.get(), &der);
    BSSL_CHECK(der_len > 0);
    OPENSSL_free(der);

    // Reserialize |x509|'s TBSCertificate without reusing the cached encoding.
    // TODO(crbug.com/boringssl/352): Ideally we would also assert the output
    // matches the input TBSCertificate, but our parser is not strict enough.
    der = nullptr;
    der_len = i2d_re_X509_tbs(x509.get(), &der);
    BSSL_CHECK(der_len > 0);
    OPENSSL_free(der);

    BIO *bio = BIO_new(BIO_s_mem());
    X509_print(bio, x509.get());
    BIO_free(bio);
  }
  ERR_clear_error();
  return 0;
}
