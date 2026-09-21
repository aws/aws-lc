// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/pem.h>
#include <openssl/x509.h>
#include <sys/stat.h>
#include <algorithm>
#include <iostream>
#include <string>
#include "internal.h"

// OpenSSL's verify exits with 2 when any input certificate fails to load or
// verify, and with 1 for option or trust store setup errors (including an
// unreadable -untrusted file).
static const int kVerifyExitFailure = 2;

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-CAfile", kOptionalArgument,
     "A file of trusted certificates. The "
     "file should contain one or more certificates in PEM format."},
    {"-CApath", kOptionalArgument,
     "A directory of trusted PEM certificates, indexed by subject hash"},
    {"-no-CAfile", kBooleanArgument,
     "Do not load the default trusted certificate file"},
    {"-no-CApath", kBooleanArgument,
     "Do not load the default trusted certificate directory"},
    {"-purpose", kOptionalArgument,
     "Check certificate purpose (e.g. sslserver or sslclient)"},
    {"-verbose", kBooleanArgument,
     "This argument is a no-op. Accepted for compatibility with OpenSSL."},
    {"-untrusted", kOptionalArgument,
     "A file of untrusted certificates to be used for chain building. The "
     "file should contain one or more certificates in PEM format."},
    {"-x509_strict", kBooleanArgument,
     "This argument is a no-op. AWS-LC is always strict."},
    {"", kOptionalArgument, ""}};

// IsDirectory returns true if |path| names an existing directory.
// |X509_LOOKUP_add_dir| only records the path and defers all filesystem access
// to lookup time, so a missing -CApath would otherwise surface as a chain
// building failure (exit 2) instead of a setup error (exit 1) as in OpenSSL.
static bool IsDirectory(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0) {
    return false;
  }
#if defined(S_ISDIR)
  return S_ISDIR(st.st_mode);
#else
  return (st.st_mode & _S_IFMT) == _S_IFDIR;
#endif
}

// Explicit paths replace their corresponding defaults. As in OpenSSL,
// failure to load a default location is not fatal. Loading a missing default
// leaves |X509_R_LOADING_DEFAULTS| or |X509_R_LOADING_CERT_DIR| on the error
// queue; the caller clears it before verifying.
static X509_STORE *setup_verification_store(const char *cafile,
                                            const char *capath, bool no_cafile,
                                            bool no_capath) {
  bssl::UniquePtr<X509_STORE> store(X509_STORE_new());
  if (!store) {
    return nullptr;
  }

  if (cafile != nullptr || !no_cafile) {
    X509_LOOKUP *lookup =
        X509_STORE_add_lookup(store.get(), X509_LOOKUP_file());
    if (!lookup) {
      return nullptr;
    }
    if (cafile != nullptr) {
      if (!X509_LOOKUP_load_file(lookup, cafile, X509_FILETYPE_PEM)) {
        fprintf(stderr, "Error loading file %s\n", cafile);
        return nullptr;
      }
    } else {
      X509_LOOKUP_load_file(lookup, nullptr, X509_FILETYPE_DEFAULT);
    }
  }

  if (capath != nullptr || !no_capath) {
    X509_LOOKUP *lookup =
        X509_STORE_add_lookup(store.get(), X509_LOOKUP_hash_dir());
    if (!lookup) {
      return nullptr;
    }
    if (capath != nullptr) {
      if (!IsDirectory(capath)) {
        fprintf(stderr, "verify: Not a directory: %s\n", capath);
        return nullptr;
      }
      if (!X509_LOOKUP_add_dir(lookup, capath, X509_FILETYPE_PEM)) {
        fprintf(stderr, "Error loading directory %s\n", capath);
        return nullptr;
      }
    } else {
      X509_LOOKUP_add_dir(lookup, nullptr, X509_FILETYPE_DEFAULT);
    }
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

// load_untrusted reads the PEM certificate bundle at |chainfile| into a new
// stack. It returns nullptr on error.
static bssl::UniquePtr<STACK_OF(X509)> load_untrusted(const char *chainfile) {
  bssl::UniquePtr<STACK_OF(X509)> chain(sk_X509_new_null());
  if (!chain) {
    return nullptr;
  }
  ScopedFILE chain_file(fopen(chainfile, "rb"));
  if (!chain_file) {
    fprintf(stderr, "error %s: reading chain certificates failed\n", chainfile);
    return nullptr;
  }
  bssl::UniquePtr<BIO> chain_bio(BIO_new_fp(chain_file.get(), BIO_NOCLOSE));
  if (!chain_bio) {
    return nullptr;
  }
  size_t count = 0;
  while (1) {
    bssl::UniquePtr<X509> chain_cert(
        PEM_read_bio_X509(chain_bio.get(), NULL, NULL, NULL));
    if (chain_cert.get() == nullptr) {
      uint32_t error = ERR_peek_last_error();
      if (ERR_GET_LIB(error) == ERR_LIB_PEM &&
          ERR_GET_REASON(error) == PEM_R_NO_START_LINE && count > 0) {
        ERR_clear_error();
        break;
      }
      fprintf(stderr, "error %s: reading chain certificates failed\n",
              chainfile);
      return nullptr;
    }
    if (!bssl::PushToStack(chain.get(), std::move(chain_cert))) {
      return nullptr;
    }
    count++;
  }
  return chain;
}

// check_impl verifies the certificate in |certfile| (or stdin if null) against
// |ctx|, using |chain| (which may be null) as untrusted intermediates. It
// returns 1 if the certificate verified and 0 otherwise, leaving any errors on
// the error queue.
static int check_impl(X509_STORE *ctx, STACK_OF(X509) *chain,
                      const char *certfile) {
  bssl::UniquePtr<X509> cert;
  int i = 0, ret = 0;

  if (certfile) {
    ScopedFILE cert_file(fopen(certfile, "rb"));
    if (!cert_file) {
      fprintf(stderr, "error %s: reading certificate failed\n", certfile);
      return 0;
    }
    cert.reset(PEM_read_X509(cert_file.get(), nullptr, nullptr, nullptr));

  } else {
    bssl::UniquePtr<BIO> input(BIO_new_fp(stdin, BIO_NOCLOSE));
    if (!input) {
      return 0;
    }
    cert.reset(PEM_read_bio_X509(input.get(), nullptr, nullptr, nullptr));
  }

  if (cert.get() == nullptr) {
    fprintf(stderr, "error %s: reading certificate failed\n",
            certfile == nullptr ? "stdin" : certfile);
    return 0;
  }

  bssl::UniquePtr<X509_STORE_CTX> store_ctx(X509_STORE_CTX_new());
  if (store_ctx == nullptr || store_ctx.get() == nullptr) {
    fprintf(stderr, "error %s: X.509 store context allocation failed\n",
               (certfile == nullptr) ? "stdin" : certfile);
    return 0;
  }

  if (!X509_STORE_CTX_init(store_ctx.get(), ctx, cert.get(), chain)) {
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

// check wraps |check_impl| and, as in OpenSSL's verify, prints the error queue
// for a failed input immediately so that it is reported before the next input
// is checked.
static int check(X509_STORE *ctx, STACK_OF(X509) *chain, const char *certfile) {
  ERR_clear_error();
  int ret = check_impl(ctx, chain, certfile);
  if (ret != 1) {
    ERR_print_errors_fp(stderr);
  }
  return ret;
}

int VerifyTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args, kArguments)) {
    PrintUsage(kArguments);
    return kToolExitFailure;
  }

  if (HasArgument(parsed_args, "-help")) {
    fprintf(stderr,
            "Usage: verify [options] [cert.pem...]\n"
            "Certificates must be in PEM format. They can be specified in one or more files.\n"
            "If no files are specified, the tool will read from stdin.\n\n"
            "Valid options are:\n");
    PrintUsage(kArguments);
    return kToolExitSuccess;
  }

  std::string cafile, capath, purpose;
  GetString(&cafile, "-CAfile", "", parsed_args);
  GetString(&capath, "-CApath", "", parsed_args);
  GetString(&purpose, "-purpose", "", parsed_args);

  int purpose_id = 0, trust_id = 0;
  if (HasArgument(parsed_args, "-purpose")) {
    // The short-name lookup returns a table index, not a purpose ID.
    const X509_PURPOSE *p =
        X509_PURPOSE_get0(X509_PURPOSE_get_by_sname(purpose.c_str()));
    if (!p) {
      fprintf(stderr, "Unknown certificate purpose: %s\n", purpose.c_str());
      return kToolExitFailure;
    }
    purpose_id = X509_PURPOSE_get_id(p);
    // The store-level purpose setter does not configure auxiliary trust.
    // "any" has no corresponding trust type, so retain the default for it.
    if (purpose_id != X509_PURPOSE_ANY) {
      trust_id = X509_PURPOSE_get_trust(p);
    }
  }

  bssl::UniquePtr<X509_STORE> store(setup_verification_store(
      HasArgument(parsed_args, "-CAfile") ? cafile.c_str() : nullptr,
      HasArgument(parsed_args, "-CApath") ? capath.c_str() : nullptr,
      HasArgument(parsed_args, "-no-CAfile"),
      HasArgument(parsed_args, "-no-CApath")));
  if (!store) {
    fprintf(stderr, "Error: Unable to setup certificate verification store.\n");
    return kToolExitFailure;
  }
  if ((purpose_id != 0 && !X509_STORE_set_purpose(store.get(), purpose_id)) ||
      (trust_id != 0 && !X509_STORE_set_trust(store.get(), trust_id))) {
    return kToolExitFailure;
  }
  X509_STORE_set_verify_cb(store.get(), cb);

  // Discard any errors from loading absent default trust locations.
  ERR_clear_error();

  bool all_ok = true;

  std::string chain_file;
  GetString(&chain_file, "-untrusted", "", parsed_args);
  bssl::UniquePtr<STACK_OF(X509)> chain;
  if (HasArgument(parsed_args, "-untrusted")) {
    chain = load_untrusted(chain_file.c_str());
    if (!chain) {
      return kToolExitFailure;
    }
  }

  // No additional file or certs provided, read from stdin
  if (extra_args.size() == 0) {
    all_ok = check(store.get(), chain.get(), NULL) == 1;
  } else {
    // Certs provided as files
    for (size_t i = 0; i < extra_args.size(); i++) {
      all_ok &= check(store.get(), chain.get(), extra_args[i].c_str()) == 1;
    }
  }

  return all_ok ? kToolExitSuccess : kVerifyExitFailure;
}
