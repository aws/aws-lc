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
#define DEFAULT_CHAR_TYPE MBSTRING_ASC

// Notes: -x509 option assumes -new when -in is not passed in with OpenSSL. We do not support -in as of now, so -new
// is implied with -x509.
//
// In general, OpenSSL supports a default config file which it defaults to when user input is
// not provided. We do not support this interface. Therefore, -keyout defaults to privkey.pem when
// user input is not provided.
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
                    " private key or writes to a file called privkey.pem in the current directory." },
  { "-out", kOptionalArgument, "This specifies the output filename to write to or " \
                    "standard output by default." },
  { "", kOptionalArgument, "" }
};


// Parse key specification string and generate key
// Could be rsa:2048, rsa, or any other string
static EVP_PKEY *generate_key(const char *keyspec) {
    EVP_PKEY_CTX *ctx = NULL;
    EVP_PKEY *pkey = NULL;
    long keylen = DEFAULT_KEY_LENGTH;
    int pkey_type = EVP_PKEY_RSA;

    // Parse keyspec
    if (strncasecmp(keyspec, "rsa:", 4) == 0) {
      keylen = atol(keyspec + 4);
    } else if (strcasecmp(keyspec, "rsa") == 0) {
	    keylen = DEFAULT_KEY_LENGTH;
    } else {
      fprintf(stderr, "Unknown key specification: %s, using RSA key with 2048 bit length\n", keyspec);
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

X509_NAME* parse_subject_name(std::string &subject_string) {
  const char *subject_name_ptr = subject_string.c_str();

  if (*subject_name_ptr++ != '/') {
    fprintf(stderr, "name is expected to be in the format "
                    "/type0=value0/type1=value1/type2=... where characters may "
                    "be escaped by \\. This name is not in that format: '%s'\n",
                   --subject_name_ptr);
    return nullptr;
  }

  // Create new X509_NAME
  X509_NAME* name = X509_NAME_new();
  if (!name) {
    return nullptr;
  }

  std::string type;
  std::string value;

  while (*subject_name_ptr) {
    // Reset strings for new iteration
    type.clear();
    value.clear();

    // Parse type
    while (*subject_name_ptr && *subject_name_ptr != '=') {
      type += *subject_name_ptr++;
    }

    if (!*subject_name_ptr) {
      fprintf(stderr, "Hit end of string before finding the equals.\n");
      X509_NAME_free(name);
      return nullptr;
    }

    // Skip '='
    subject_name_ptr++;

    // Parse value
    while (*subject_name_ptr && *subject_name_ptr != '/') {
      if (*subject_name_ptr == '\\' && *(subject_name_ptr + 1)) {
        // Handle escaped character
        subject_name_ptr++;
        value += *subject_name_ptr++;
      } else {
        value += *subject_name_ptr++;
      }
    }

    // Skip trailing '/' if present
    if (*subject_name_ptr == '/') {
      subject_name_ptr++;
    }

    // Convert type to NID, skip unknown attributes
    int nid = OBJ_txt2nid(type.c_str());
    if (nid == NID_undef) {
      fprintf(stderr, "Warning: Skipping unknown attribute \"%s\"\n", type.c_str());
      // Skip unknown attributes
      continue;
    }

    // Skip empty values
    if (value.empty()) {
      fprintf(stderr, "Warning: No value specified for attribute \"%s\", Skipped\n", type.c_str());
      continue;
    }

    // Add entry to the name
    if (!X509_NAME_add_entry_by_NID(name, nid, DEFAULT_CHAR_TYPE,
                                   (unsigned char*)value.c_str(),
                                   -1, -1, 0)) {
      OPENSSL_PUT_ERROR(X509, ERR_R_X509_LIB);
      X509_NAME_free(name);
      return nullptr;
    }
  }

  return name;
}
//
// X509_NAME* prompt_user_subject_name() {
//   return nullptr;
// }
//
// static int make_certificate_request(X509_REQ *req, EVP_PKEY *pkey, std::string &subject_name) {
//   X509_NAME *name;
//
//   // Set version
//   if (!X509_REQ_set_version(req, 0L))  // version 1
//     return 0;
//
//   if (subject_name.empty()) {// Prompt the user
//     name = prompt_user_subject_name();
//   } else { // Parse user provided string
//     name = parse_subject_name(subject_name);
//     if (!name) {
//       return 0;
//     }
//   }
//
//
//   if (!X509_REQ_set_subject_name(req, name)) {
//     X509_NAME_free(name);
//     return 0;
//   }
//   X509_NAME_free(name);
//
//   // Set public key
//   if (!X509_REQ_set_pubkey(req, pkey)) {
//     return 0;
//   }
//
//   return 1;
// }

bool reqTool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string newkey, subj, keyout, out;
  unsigned int days;
  bool help = false, new_flag = false, x509_flag = false, nodes = false;

  GetBoolArgument(&help, "-help", parsed_args);
  GetBoolArgument(&new_flag, "-new", parsed_args);
  GetBoolArgument(&x509_flag, "-x509", parsed_args);
  GetBoolArgument(&nodes, "-nodes", parsed_args);

  GetString(&newkey, "-newkey", "", parsed_args);
  GetUnsigned(&days, "-days", 30u, parsed_args);
  GetString(&subj, "-subj", "", parsed_args);
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
  // NEED PASSWORD PROMPTING STUFF HERE, THAT TIES INTO PEM_DEF CALLBACK. I
  // BELIEVE YOU NEED EITHER A PASSWORD OR CIPHER TO DO THE PRIV KEY CREATION.
  // NEED TO FIGURE THIS OUT.

  // Generate and write private key
  EVP_CIPHER *cipher = NULL;
  if (!nodes) {
	cipher = (EVP_CIPHER*)EVP_des_ede3_cbc();
  }

  bssl::UniquePtr<BIO> out_bio;
  if (!keyout.empty()) {
    fprintf(stderr, "Writing private key to %s\n", keyout.c_str());
    out_bio.reset(BIO_new_file(keyout.c_str(), "w"));
  } else {
    // Default to privkey.pem in the current directory
    const char* default_keyfile = "privkey.pem";
    fprintf(stderr, "Writing private key to %s (default)\n", default_keyfile);
    out_bio.reset(BIO_new_file(default_keyfile, "w"));
  }

  if (!out_bio || !PEM_write_bio_PrivateKey(out_bio.get(), pkey.get(), cipher, NULL, 0, NULL, NULL)) {
	  fprintf(stderr, "Failed to write private key.\n");
    return false;
  }

  // At this point, one of -new -newkey or -x509 must be defined
  // Like OpenSSL, generate CSR first - then convert to cert if needed
//  bssl::UniquePtr<X509_REQ> req(X509_REQ_new());
//  X509 *cert = NULL;
//  int ret = 0;

//  // Always create a CSR first
//  if (req == NULL || !make_certificate_request(req.get(), pkey.get(), &subj)) {
//    fprintf(stderr, "Failed to create certificate request\n");
//    goto end;
//  }
//
//    if (params->is_x509) {
//        // Convert CSR to certificate
//        cert = X509_new();
//        if (cert == NULL) {
//            fprintf(stderr, "Failed to create X509 structure\n");
//            goto end;
//        }
//
//        // Set version
//        if (!X509_set_version(cert, params->version)) {
//            fprintf(stderr, "Failed to set certificate version\n");
//            goto end;
//        }
//
//        // Generate random serial number
//        if (!generate_serial(cert)) {
//            fprintf(stderr, "Failed to generate serial number\n");
//            goto end;
//        }
//
//        // Set subject and issuer from CSR
//        if (!X509_set_subject_name(cert, X509_REQ_get_subject_name(req)) ||
//            !X509_set_issuer_name(cert, X509_REQ_get_subject_name(req))) {
//            fprintf(stderr, "Failed to set subject/issuer\n");
//            goto end;
//        }
//
//        // Set validity period
//        time_t now = time(NULL);
//        if (!X509_time_adj_ex(X509_getm_notBefore(cert), 0, 0, &now) ||
//            !X509_time_adj_ex(X509_getm_notAfter(cert), params->days, 0, &now)) {
//            fprintf(stderr, "Failed to set validity period\n");
//            goto end;
//        }
//
//        // Copy public key from CSR
//        EVP_PKEY *tmppkey = X509_REQ_get0_pubkey(req);
//        if (!tmppkey || !X509_set_pubkey(cert, tmppkey)) {
//            fprintf(stderr, "Failed to set public key\n");
//            goto end;
//        }
//
//        // Sign the certificate
//        if (!X509_sign(cert, pkey, EVP_sha256())) {
//            fprintf(stderr, "Failed to sign certificate\n");
//            goto end;
//        }
//    } else {
//      // do other processing for CSR and then sign it
//      // Sign the request
// 	  if (!X509_REQ_sign(req, pkey, EVP_sha256())) {
//   		return 0;
//  	  }
//
//    }
//
//    // Set output parameters
//    if (params->is_x509) {
//        *cert_out = cert;
//        cert = NULL;
//    } else {
//        *req_out = req;
//        req = NULL;
//    }
//
//    ret = 1;
//
//end:
//    X509_REQ_free(req);
//    X509_free(cert);
//    return ret;







  return true;
}
