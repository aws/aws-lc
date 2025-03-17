// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/pem.h>
#include "internal.h"
#include "../tool/internal.h"
#include <openssl/evp.h>
#include <openssl/err.h>
#include <openssl/bio.h>
#include <openssl/rsa.h>
#include <string.h>
#include <stdio.h>

#define DEFAULT_KEY_LENGTH 2048
#define MIN_KEY_LENGTH 512

// Notes: -x509 option assumes -new when -in is not passed in with OpenSSL. We do not support -in as of now, so -new
// is implied with -x509.
static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-new", kBooleanArgument, "Generates a new certificate request." \
                    "It will prompt the user for the relevant field values." \
                    "If the -newkey option is not given it will generate a new " \
                    "private key with 2048 bits length" },
  { "-newkey", kOptionalArgument, "This option is used to generate a new private " \
    				"key. This option supports RSA keys in the format [rsa:]nbits. " \
     				"If nbits is not given, i.e. -newkey rsa is specified, 2048 " \
           			"bits length is used. This implies -new unless used with -x509." },
  { "-days", kOptionalArgument, "When -x509 is in use this specifies the number of " \
					"days from today to certify the certificate for, otherwise it " \
     				"is ignored. n should be a positive integer. The default is" \
     				"30 days." },
  { "-nodes", kBooleanArgument, "If this option is specified then if a private " \
                    "key is created it will not be encrypted." },
  { "-x509", kBooleanArgument, "This option outputs a certificate instead of" \
                    "a certificate request. If the -newkey option is not given it " \
        			"will generate a new private key with 2048 bits length" },
  { "-subj", kOptionalArgument, "Sets subject name for new request. The arg must " \
                     "be formatted as /type0=value0/type1=value1/type2=.... " \
     				 "Keyword characters may be escaped by \\ (backslash), and " \
     				 "whitespace is retained." },
  { "-keyout", kOptionalArgument, "This specifies the output filename for the " \
                     " private key or writes to standard output by default." },
  { "-out", kOptionalArgument, "This specifies the output filename to write to or " \
                     "standard output by default." },
  { "", kOptionalArgument, "" }
};


// Parse key specification string and generate key
static EVP_PKEY *generate_key(const char *keyspec) {
    EVP_PKEY_CTX *ctx = NULL;
    EVP_PKEY *pkey = NULL;
    long keylen;
    int pkey_type = EVP_PKEY_RSA;

    // Parse keyspec
    if (keyspec != NULL) {
      if (strcasecmp(keyspec, "rsa") == 0) {
		keylen = DEFAULT_KEY_LENGTH;
      } else if (strncasecmp(keyspec, "rsa:", 4) == 0) {
      	keylen = atol(keyspec + 4);
      } else {
        fprintf(stderr, "Unknown key specification: %s\n", keyspec);
        return NULL;
      }
    }

    // Validate key length
    if (keylen < MIN_KEY_LENGTH) {
        fprintf(stderr, "Key length too short (minimum %d bits)\n", MIN_KEY_LENGTH);
        return NULL;
    }

    // Create key generation context
    ctx = EVP_PKEY_CTX_new_id(pkey_type, NULL);
    if (ctx == NULL) {
      return NULL;
    }

	if (EVP_PKEY_keygen_init(ctx) <= 0 || EVP_PKEY_CTX_set_rsa_keygen_bits(ctx, keylen) <= 0
        || EVP_PKEY_keygen(ctx, &pkey) <= 0) {
    	EVP_PKEY_CTX_free(ctx);
        return NULL;
    }

    EVP_PKEY_CTX_free(ctx);
    return pkey;
}

bool reqTool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string newkey, days, subj, keyout, out;
  bool help = false, new_flag = false, x509_flag = false, nodes = false;

  GetBoolArgument(&help, "-help", parsed_args);
  GetBoolArgument(&new_flag, "-new", parsed_args);
  GetBoolArgument(&x509_flag, "-x509", parsed_args);
  GetBoolArgument(&nodes, "-nodes", parsed_args);

  GetString(&newkey, "-newkey", "", parsed_args);
  GetString(&days, "-days", "" , parsed_args);
  GetString(&subj, "-subj", "" , parsed_args);
  GetString(&keyout, "-keyout", "" , parsed_args);
  GetString(&out, "-out", "" , parsed_args);

   if (help) {
     PrintUsage(kArguments);
     return false;
   }

  if (!new_flag && !x509_flag && newkey.empty()) {
    fprintf(stderr, "Error: Missing required options, -x509, -new, or -newkey must be specified. \n");
    return false;
  }

  if (new_flag && x509_flag) {
  	fprintf(stderr, "Error: Only one of -x509 or -req may be specified. \n");
    return false;
  }

  std::string keyspec = "rsa:2048";
  if (!newkey.empty()) {
	keyspec = newkey;
  }

  bssl::UniquePtr<EVP_PKEY> pkey(generate_key(keyspec.c_str()));
  if (!pkey) {
    fprintf(stderr, "Error: Failed to generate private key.\n");
    return false;
  }

  EVP_CIPHER *cipher = NULL;
  if (!nodes) {
	cipher = (EVP_CIPHER*)EVP_des_ede3_cbc();
  }

  bssl::UniquePtr<BIO> out_bio(BIO_new_fp(stdout, BIO_CLOSE));
  if (!keyout.empty()) {
  	fprintf(stderr, "Writing public key to %s\n", keyout.c_str());
    out_bio.reset(BIO_new_file(keyout.c_str(), "w"));
  }

  if (out_bio || !PEM_write_bio_PrivateKey(out_bio.get(), pkey.get(), cipher, NULL, 0, NULL, NULL)) {
	fprintf(stderr, "Failed to write private key.\n");
    return false;
  }







  return true;
}
