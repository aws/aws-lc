// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/x509.h>
#include "internal.h"

static const argument_t kArguments[] = {
        { "-help", kBooleanArgument, "Display option summary" },
        { "-CAfile", kOptionalArgument, "A file of trusted certificates. The "
                "file should contain one or more certificates in PEM format." },
        { "", kOptionalArgument, "" }
};

// setup_verification_store sets up an X509 certificate store for verification.
// It configures te store with file and directory lookups. It loads the
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
    X509_LOOKUP_load_file(lookup, NULL, X509_FILETYPE_DEFAULT);
  }

  lookup = X509_STORE_add_lookup(store, X509_LOOKUP_hash_dir());
  if (lookup == NULL) {
    goto end;
  }
  X509_LOOKUP_add_dir(lookup, NULL, X509_FILETYPE_DEFAULT);

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

static int check(X509_STORE *store, const char *file) {
//  X509 *x = NULL;
//  int i = 0, ret = 0;
//  X509_STORE_CTX *csc;
//  STACK_OF(X509) *chain = NULL;
//  int num_untrusted;
//
//  x = load_cert(file, FORMAT_UNDEF, "certificate file");
//  if (x == NULL)
//    goto end;
//
//  if (opts != NULL) {
//    for (i = 0; i < sk_OPENSSL_STRING_num(opts); i++) {
//      char *opt = sk_OPENSSL_STRING_value(opts, i);
//      if (x509_ctrl_string(x, opt) <= 0) {
//        BIO_printf(bio_err, "parameter error \"%s\"\n", opt);
//        ERR_print_errors(bio_err);
//        X509_free(x);
//        return 0;
//      }
//    }
//  }
//
//  csc = X509_STORE_CTX_new();
//  if (csc == NULL) {
//    BIO_printf(bio_err, "error %s: X.509 store context allocation failed\n",
//               (file == NULL) ? "stdin" : file);
//    goto end;
//  }
//
//  X509_STORE_set_flags(ctx, vflags);
//  if (!X509_STORE_CTX_init(csc, ctx, x, uchain)) {
//    X509_STORE_CTX_free(csc);
//    BIO_printf(bio_err,
//               "error %s: X.509 store context initialization failed\n",
//               (file == NULL) ? "stdin" : file);
//    goto end;
//  }
//  if (tchain != NULL)
//    X509_STORE_CTX_set0_trusted_stack(csc, tchain);
//  if (crls != NULL)
//    X509_STORE_CTX_set0_crls(csc, crls);
//  i = X509_verify_cert(csc);
//  if (i > 0 && X509_STORE_CTX_get_error(csc) == X509_V_OK) {
//    BIO_printf(bio_out, "%s: OK\n", (file == NULL) ? "stdin" : file);
//    ret = 1;
//    if (show_chain) {
//      int j;
//
//      chain = X509_STORE_CTX_get1_chain(csc);
//      num_untrusted = X509_STORE_CTX_get_num_untrusted(csc);
//      BIO_printf(bio_out, "Chain:\n");
//      for (j = 0; j < sk_X509_num(chain); j++) {
//        X509 *cert = sk_X509_value(chain, j);
//        BIO_printf(bio_out, "depth=%d: ", j);
//        X509_NAME_print_ex_fp(stdout,
//                              X509_get_subject_name(cert),
//                              0, get_nameopt());
//        if (j < num_untrusted)
//          BIO_printf(bio_out, " (untrusted)");
//        BIO_printf(bio_out, "\n");
//      }
//      sk_X509_pop_free(chain, X509_free);
//    }
//  } else {
//    BIO_printf(bio_err,
//               "error %s: verification failed\n",
//               (file == NULL) ? "stdin" : file);
//  }
//  X509_STORE_CTX_free(csc);
//
//  end:
//  if (i <= 0)
//    ERR_print_errors(bio_err);
//  X509_free(x);
//
//  return ret;
  return 0;
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

  ret = 0;
  fprintf(stderr, "general args size %d\n", (int)args.size());
  fprintf(stderr, "i size is = %d\n", (int)i);

  // No additional file or certs provided, read from stdin
  if (args.size() == i) {
    fprintf(stderr, "need to read from stdin\n");
    if (check(store.get(), NULL) != 1) {
      ret = -1;
    }
  } else {
    // Certs provided as files
    for (; i < args.size(); i++) {
      fprintf(stderr, "we are in loop %d\n", (int)args.size());
      if (check(store.get(), args[i].c_str()) != 1)
        ret = -1;
    }
  }

  printf("%s\n", OPENSSL_VERSION_TEXT);
  if (!ret) {
    return false;
  }
  return true;
}
