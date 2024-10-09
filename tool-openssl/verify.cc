// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/x509.h>
#include "internal.h"

static const argument_t kArguments[] = {
        { "-help", kBooleanArgument, "Display option summary" },
        { "-CAfile", kBooleanArgument, "A file of trusted certificates. The "
                "file should contain one or more certificates in PEM format. If"
                "this argument is not provided, " },
        { "", kOptionalArgument, "" }
};

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

bool VerifyTool(const args_list_t &args) {
  args_map_t parsed_args;
  if (!ParseKeyValueArguments(&parsed_args, args, kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  bssl::UniquePtr<X509_STORE> store;
  std::string cafile;
  bool help;

  GetBoolArgument(&help, "-help", parsed_args);
  GetString(&cafile, "-CAfile", "", parsed_args);

  // Display verify tool option summary
  if (help) {
    fprintf(stderr, "Usage: verify [options] cert.pem...\n"
                    "If no certificates are given, verify will attempt to "
                    "read a certificate from standard input. "
                    "Certificates must be in PEM format.\n\n "
                    "Valid options are:\n");
    PrintUsage(kArguments);
    return false;
  }

  store.reset(setup_verification_store(cafile));

  // Initialize certificate verification store
  if (!store.get()) {
    fprintf(stderr, "Error: Unable to setup certificate verification store.");
    return false;
  }

 // X509_STORE_set_verify_cb
//  ret = 0;
//  if (argc < 1) {
//    if (check(store, NULL, untrusted, trusted, crls, show_chain) != 1)
//      ret = -1;
//  } else {
//    for (i = 0; i < argc; i++)
//      if (check(store, argv[i], untrusted, trusted, crls,
//                show_chain) != 1)
//        ret = -1;
//  }
// Need to write checking logic and verify stdinput works





  printf("%s\n", OPENSSL_VERSION_TEXT);
  return true;
}
