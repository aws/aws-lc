// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/x509.h>
#include <openssl/pem.h>
#include "internal.h"

// TO-DO: We do not support using a default trust store, therefore -CAfile must
// be a required argument. Once support for default trust stores is added,
// make it an optional argument.
static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-CAfile", kRequiredArgument,
     "A file of trusted certificates. The "
     "file should contain one or more certificates in PEM format."},
    {"-untrusted", kOptionalArgument,
     "A file of untrusted certificates to be used for chain building. The "
     "file should contain one or more certificates in PEM format."},
    {"-x509_strict", kBooleanArgument,
     "This argument is a no-op. AWS-LC is always strict."},
    {"", kOptionalArgument, ""}};

// setup_verification_store sets up an X509 certificate store for verification.
// It configures the store with file and directory lookups. It loads the
// specified CA file if provided and otherwise uses default locations.
static X509_STORE *setup_verification_store(std::string CAfile) {
  bssl::UniquePtr<X509_STORE> store(X509_STORE_new());
  X509_LOOKUP *lookup;

  if (!store) {
    return nullptr;
  }

  if (!CAfile.empty()) {
    lookup = X509_STORE_add_lookup(store.get(), X509_LOOKUP_file());
    if (!lookup || !X509_LOOKUP_load_file(lookup, CAfile.c_str(), X509_FILETYPE_PEM)) {
      fprintf(stderr, "Error loading file %s\n", CAfile.c_str());
      return nullptr;
    }
  }

  // Add default dir path
  lookup = X509_STORE_add_lookup(store.get(), X509_LOOKUP_hash_dir());
  if (!lookup || !X509_LOOKUP_add_dir(lookup, NULL, X509_FILETYPE_DEFAULT)) {
    return nullptr;
  }

  return store.release();
}

static int cb(int ok, X509_STORE_CTX *ctx) {
  if (!ok) {
    int cert_error = X509_STORE_CTX_get_error(ctx);
    X509 *current_cert = X509_STORE_CTX_get_current_cert(ctx);

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

static int check(X509_STORE *ctx, const char* chainfile, const char *certfile) {
  bssl::UniquePtr<STACK_OF(X509)> chain(sk_X509_new_null());
  bssl::UniquePtr<X509> cert;
  int i = 0, ret = 0;

  if (chainfile) {
    ScopedFILE chain_file(fopen(chainfile, "rb"));
    if (!chain_file) {
      fprintf(stderr, "error %s: reading certificate failed\n", certfile);
      return 0;
    }
    bssl::UniquePtr<BIO> chain_bio(BIO_new_fp(chain_file.get(), BIO_NOCLOSE));
    size_t count = 0;
    while(1) {
      bssl::UniquePtr<X509> chain_cert(PEM_read_bio_X509(chain_bio.get(), NULL, NULL, NULL));
      if (chain_cert.get() == nullptr) {
        uint32_t error = ERR_peek_last_error();
        if (ERR_GET_LIB(error) == ERR_LIB_PEM &&
            ERR_GET_REASON(error) == PEM_R_NO_START_LINE && count > 0) {
          ERR_clear_error();
          break;
        }
        fprintf(stderr, "error %s: reading chain certificates failed\n",
                chainfile);
        return 0;
      }
      if(!sk_X509_push(chain.get(), chain_cert.release())) {
        return 0;
      }
      count++;
    }
  }

  if (certfile) {
    ScopedFILE cert_file(fopen(certfile, "rb"));
    if (!cert_file) {
      fprintf(stderr, "error %s: reading certificate failed\n", certfile);
      return 0;
    }
    cert.reset(PEM_read_X509(cert_file.get(), nullptr, nullptr, nullptr));

  } else {
    bssl::UniquePtr<BIO> input(BIO_new_fp(stdin, BIO_CLOSE));
    cert.reset(PEM_read_bio_X509(input.get(), nullptr, nullptr, nullptr));
  }

  if (cert.get() == nullptr) {
    return 0;
  }

  bssl::UniquePtr<X509_STORE_CTX> store_ctx(X509_STORE_CTX_new());
  if (store_ctx == nullptr || store_ctx.get() == nullptr) {
    fprintf(stderr, "error %s: X.509 store context allocation failed\n",
               (certfile == nullptr) ? "stdin" : certfile);
    return 0;
  }

  if (!X509_STORE_CTX_init(store_ctx.get(), ctx, cert.get(), chain.get())) {
    fprintf(stderr,
               "error %s: X.509 store context initialization failed\n",
               (certfile == nullptr) ? "stdin" : certfile);
    return 0;
  }

  i = X509_verify_cert(store_ctx.get());
  if (i > 0 && X509_STORE_CTX_get_error(store_ctx.get()) == X509_V_OK) {
    fprintf(stdout, "%s: OK\n", (certfile == nullptr) ? "stdin" : certfile);
    ret = 1;
  } else {
    fprintf(stderr,
               "error %s: verification failed\n",
               (certfile == nullptr) ? "stdin" : certfile);
  }

  return ret;
}

bool VerifyTool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  if (parsed_args.count("-help") || parsed_args.size() == 0) {
    fprintf(stderr,
            "Usage: verify [options] [cert.pem...]\n"
            "Certificates must be in PEM format. They can be specified in one or more files.\n"
            "If no files are specified, the tool will read from stdin.\n\n"
            "Valid options are:\n");
    PrintUsage(kArguments);
    return false;
  }

  std::string cafile = parsed_args["-CAfile"];

  bssl::UniquePtr<X509_STORE> store(setup_verification_store(cafile));
  // Initialize certificate verification store
  if (!store.get()) {
    fprintf(stderr, "Error: Unable to setup certificate verification store.");
    return false;
  }
  X509_STORE_set_verify_cb(store.get(), cb);

  ERR_clear_error();

  int ret = 1;

  const char *chain = parsed_args.count("-untrusted") ? parsed_args["-untrusted"].c_str() : NULL;

  // No additional file or certs provided, read from stdin
  if (extra_args.size() == 0) {
    ret &= check(store.get(), chain, NULL);
  } else {
    // Certs provided as files
    for (size_t i = 0; i < extra_args.size(); i++) {
      ret &= check(store.get(), chain, extra_args[i].c_str());
    }
  }

  return ret == 1;
}
