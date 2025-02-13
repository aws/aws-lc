// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"
#include <openssl/x509.h>
#include <openssl/pem.h>
#include <ctime>

static const argument_t kArguments[] = {
        { "-help", kBooleanArgument, "Display option summary" },
        { "-in", kOptionalArgument, "Input file, default stdin" },
        { "-hash", kBooleanArgument, "Print hash value" },
        { "-fingerprint", kBooleanArgument, "Print CRL fingerprint" },
        { "-noout", kBooleanArgument, "No CRL output" },
        { "", kOptionalArgument, "" }
};

bool CRLTool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in;
  bool help = false, hash = false, fingerprint = false, noout = false;

  GetBoolArgument(&help, "-help", parsed_args);
  GetString(&in, "-in", "", parsed_args);
  GetBoolArgument(&hash, "-hash", parsed_args);
  GetBoolArgument(&fingerprint, "-fingerprint", parsed_args);
  GetBoolArgument(&noout, "-noout", parsed_args);

  // Display crl tool option summary
  if (help) {
    PrintUsage(kArguments);
    return false;
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

  if (hash) {
    fprintf(stdout, "%08x\n", X509_NAME_hash(X509_CRL_get_issuer(crl.get())));
  }

  if (fingerprint) {
    int j;
    unsigned int n;
    unsigned char md[EVP_MAX_MD_SIZE];

    if (!X509_CRL_digest(crl.get(), EVP_sha1(), md, &n)) {
      fprintf(stderr, "unable to get encoding of CRL\n");
      return false;
    }
    fprintf(stdout, "%s Fingerprint=", OBJ_nid2sn(EVP_MD_type(EVP_sha1())));

    for (j = 0; j < (int)n; j++) {
      fprintf(stdout, "%02X%c", md[j], (j + 1 == (int)n) ? '\n' : ':');
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
