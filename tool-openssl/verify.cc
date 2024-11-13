// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/x509.h>
#include <openssl/pem.h>
#include "internal.h"

static const argument_t kArguments[] = {
        { "-help", kBooleanArgument, "Display option summary" },
        { "-CAfile", kOptionalArgument, "A file of trusted certificates. The "
                "file should contain one or more certificates in PEM format." },
        { "", kOptionalArgument, "" }
};

// setup_verification_store sets up an X509 certificate store for verification.
// It configures the store with file and directory lookups. It loads the
// specified CA file if provided and otherwise uses default locations.
static X509_STORE *setup_verification_store(std::string CAfile) {
  X509_STORE *store = X509_STORE_new();
  X509_LOOKUP *lookup;

  if (!store) {
    goto end;
  }

  lookup = X509_STORE_add_lookup(store, X509_LOOKUP_file());
  if (!lookup) {
    goto end;
  }

  if (!CAfile.empty()) {
    if (!X509_LOOKUP_load_file(lookup, CAfile.c_str(), X509_FILETYPE_PEM)) {
      fprintf(stderr, "Error loading file %s\n", CAfile.c_str());
      goto end;
    }
  } else {
    if (!X509_LOOKUP_load_file(lookup, NULL, X509_FILETYPE_DEFAULT)) {
      goto end;
    }
  }

  lookup = X509_STORE_add_lookup(store, X509_LOOKUP_hash_dir());
  if (lookup == NULL) {
    goto end;
  }
  if (!X509_LOOKUP_add_dir(lookup, NULL, X509_FILETYPE_DEFAULT)) {
    goto end;
  }

  return store;

end:
  X509_STORE_free(store);
  return nullptr;
}

static int cb(int ok, X509_STORE_CTX *ctx) {
  int cert_error = X509_STORE_CTX_get_error(ctx);
  X509 *current_cert = X509_STORE_CTX_get_current_cert(ctx);

  if (!ok) {
    if (current_cert != NULL) {
      X509_NAME_print_ex_fp(stderr,
                         X509_get_subject_name(current_cert),
                         0, XN_FLAG_ONELINE);
      fprintf(stderr, "\n");
    }
    fprintf(stderr, "%serror %d at %d depth lookup: %s\n",
               X509_STORE_CTX_get0_parent_ctx(ctx) ? "[CRL path] " : "",
               cert_error,
               X509_STORE_CTX_get_error_depth(ctx),
               X509_verify_cert_error_string(cert_error));

    /*
     * Pretend that some errors are ok, so they don't stop further
     * processing of the certificate chain.  Setting ok = 1 does this.
     * After X509_verify_cert() is done, we verify that there were
     * no actual errors, even if the returned value was positive.
     */
    switch (cert_error) {
      case X509_V_ERR_NO_EXPLICIT_POLICY:
        /* fall thru */
      case X509_V_ERR_CERT_HAS_EXPIRED:
        /* Continue even if the leaf is a self-signed cert */
      case X509_V_ERR_DEPTH_ZERO_SELF_SIGNED_CERT:
        /* Continue after extension errors too */
      case X509_V_ERR_UNABLE_TO_GET_ISSUER_CERT_LOCALLY:
      case X509_V_ERR_INVALID_CA:
      case X509_V_ERR_INVALID_NON_CA:
      case X509_V_ERR_PATH_LENGTH_EXCEEDED:
      case X509_V_ERR_CRL_HAS_EXPIRED:
      case X509_V_ERR_CRL_NOT_YET_VALID:
      case X509_V_ERR_UNHANDLED_CRITICAL_EXTENSION:
        /* errors due to strict conformance checking (-x509_strict) */
      case X509_V_ERR_INVALID_PURPOSE:
        ok = 1;
    }
  }
  return ok;
}

static int check(X509_STORE *ctx, const char *file) {
  bssl::UniquePtr<X509> x;
  int i = 0, ret = 0;
  X509_STORE_CTX *store_ctx;

  if (file) {
    ScopedFILE cert_file(fopen(file, "rb"));
    if (!cert_file) {
      fprintf(stderr, "error %s: reading certificate failed\n", file);
    }
    x.reset(PEM_read_X509(cert_file.get(), nullptr, nullptr, nullptr));

  } else {
    bssl::UniquePtr<BIO> input(BIO_new_fp(stdin, BIO_CLOSE));
    x.reset(PEM_read_bio_X509(input.get(), nullptr, nullptr, nullptr));
  }

  if (x.get() == nullptr) {
    return 0;
  }

  store_ctx = X509_STORE_CTX_new();
  if (store_ctx == nullptr) {
    fprintf(stderr, "error %s: X.509 store context allocation failed\n",
               (file == nullptr) ? "stdin" : file);
    return 0;
  }

  if (!X509_STORE_CTX_init(store_ctx, ctx, x.get(), nullptr)) {
    X509_STORE_CTX_free(store_ctx);
    fprintf(stderr,
               "error %s: X.509 store context initialization failed\n",
               (file == nullptr) ? "stdin" : file);
    return 0;
  }

  i = X509_verify_cert(store_ctx);
  if (i > 0 && X509_STORE_CTX_get_error(store_ctx) == X509_V_OK) {
    fprintf(stdout, "%s: OK\n", (file == nullptr) ? "stdin" : file);
    ret = 1;
  } else {
    fprintf(stderr,
               "error %s: verification failed\n",
               (file == nullptr) ? "stdin" : file);
  }
  X509_STORE_CTX_free(store_ctx);

  return ret;
}

bool VerifyTool(const args_list_t &args) {
  std::string cafile;
  bssl::UniquePtr<X509_STORE> store;
  int ret;
  size_t i = 0;

  if (args.size() == 1 && args[0] == "-help") {
    fprintf(stderr, "Usage: verify [options] cert.pem...\n"
                    "Certificates must be in PEM format and specified in a file.\n"
                    "We do not support reading from stdin yet. \n\n "
                    "Valid options are:\n");
    PrintUsage(kArguments);
    return false;
  } else if (args.size() > 1 && args[0] == "-CAfile") {
    cafile = args[1];
    i += 2;
  }

  store.reset(setup_verification_store(cafile));

  // Initialize certificate verification store
  if (!store.get()) {
    fprintf(stderr, "Error: Unable to setup certificate verification store.");
    return false;
  }
  X509_STORE_set_verify_cb(store.get(), cb);

  ERR_clear_error();

  ret = 1;

  // No additional file or certs provided, read from stdin
  if (args.size() == i) {
    if (check(store.get(), NULL) != 1) {
      ret = 0;
    }
  } else {
    // Certs provided as files
    for (; i < args.size(); i++) {
      if (check(store.get(), args[i].c_str()) != 1) {
        ret = 0;
      }
    }
  }

  if (!ret) {
    return false;
  }
  return true;
}
