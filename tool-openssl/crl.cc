// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/pem.h>
#include <openssl/x509.h>
#include <algorithm>
#include <ctime>
#include <iostream>
#include <string>
#include "internal.h"

static const argument_t kArguments[] = {
        { "-help", kBooleanArgument, "Display option summary" },
        { "-in", kOptionalArgument, "Input file, default stdin" },
        { "-hash", kBooleanArgument, "Print hash value" },
        { "-fingerprint", kBooleanArgument, "Print CRL fingerprint" },
        { "-noout", kBooleanArgument, "No CRL output" },
        { "", kOptionalArgument, "" }
};

static bool handleHash(X509_CRL *crl) {
  fprintf(stdout, "%08x\n", X509_NAME_hash(X509_CRL_get_issuer(crl)));
  return true;
}

static bool handleFingerprint(X509_CRL *crl) {
  int j;
  unsigned int n;
  unsigned char md[EVP_MAX_MD_SIZE];

  if (!X509_CRL_digest(crl, EVP_sha1(), md, &n)) {
    fprintf(stderr, "unable to get encoding of CRL\n");
    return false;
  }
  fprintf(stdout, "%s Fingerprint=", OBJ_nid2sn(EVP_MD_type(EVP_sha1())));

  for (j = 0; j < (int)n; j++) {
    fprintf(stdout, "%02X%c", md[j], (j + 1 == (int)n) ? '\n' : ':');
  }
  return true;
}

static bool ProcessArgument(const std::string &arg_name, X509_CRL *crl) {
  if (arg_name == "-hash") {
    return handleHash(crl);
  }
  if (arg_name == "-fingerprint") {
    return handleFingerprint(crl);
  }
  return true;
}

bool CRLTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in;
  bool help = false, noout = false;

  GetBoolArgument(&help, "-help", parsed_args);
  GetString(&in, "-in", "", parsed_args);
  GetBoolArgument(&noout, "-noout", parsed_args);

  // Display crl tool option summary
  if (help) {
    PrintUsage(kArguments);
    return true;
  }

  // Read from stdin if no -in path provided
  ScopedFILE in_file;
  if (in.empty()) {
    in_file.reset(stdin);
  } else {
    in_file.reset(fopen(in.c_str(), "rb"));
    if (!in_file) {
      fprintf(stderr, "unable to load CRL\n");
      return false;
    }
  }

  bssl::UniquePtr<X509_CRL> crl(PEM_read_X509_CRL(in_file.get(), NULL, NULL, NULL));

  if (crl == NULL) {
    fprintf(stderr, "unable to load CRL\n");
    return false;
  }

  // Process arguments in the order they were provided
  for (const auto &arg_pair : parsed_args) {
    const std::string &arg_name = arg_pair.first;

    // Skip non-output arguments
    if (arg_name == "-in" || arg_name == "-noout" || arg_name == "-help") {
      continue;
    }

    if (!ProcessArgument(arg_name, crl.get())) {
      return false;
    }
  }

  if (!noout) {
    if(!PEM_write_X509_CRL(stdout, crl.get())) {
      fprintf(stderr, "unable to write CRL\n");
      return false;
    }
  }

  return true;
}
