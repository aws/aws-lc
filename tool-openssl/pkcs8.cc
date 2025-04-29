// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/pkcs8.h>
#include <openssl/err.h>
#include <openssl/rand.h>
#include <openssl/x509.h>
#include <cstring>
#include "internal.h"

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-in", kOptionalArgument, "Input file" },
  { "-out", kOptionalArgument, "Output file" },
  { "-topk8", kBooleanArgument, "Convert traditional format to PKCS#8" },
  { "-nocrypt", kBooleanArgument, "Use unencrypted private key" },
  { "-v2", kOptionalArgument, "Use PKCS#5 v2.0 and specified cipher" },
  { "-v2prf", kOptionalArgument, "Use specified PRF algorithm with PKCS#5 v2.0" },
  { "-passin", kOptionalArgument, "Input file passphrase source" },
  { "-passout", kOptionalArgument, "Output file passphrase source" },
  { "", kOptionalArgument, "" }
};

// Helper function to print OpenSSL errors
static void print_errors() {
  ERR_print_errors_fp(stderr);
}

// Helper function to read a private key in any format
static bssl::UniquePtr<EVP_PKEY> read_private_key(FILE* in_file, const char* passin) {
  bssl::UniquePtr<EVP_PKEY> pkey;

  // First try reading as encrypted PKCS#8
  rewind(in_file);
  bssl::UniquePtr<X509_SIG> p8(PEM_read_PKCS8(in_file, nullptr, nullptr, nullptr));
  if (p8) {
    if (passin) {
      bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(
          PKCS8_decrypt(p8.get(), passin, strlen(passin)));
      if (p8inf) {
        pkey.reset(EVP_PKCS82PKEY(p8inf.get()));
        if (pkey) {
          return pkey;
        }
      }
    }
    // Don't print error here - we'll try other formats first
    ERR_clear_error();
  }

  // Try unencrypted PKCS#8
  rewind(in_file);
  bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(
      PEM_read_PKCS8_PRIV_KEY_INFO(in_file, nullptr, nullptr, nullptr));
  if (p8inf) {
    pkey.reset(EVP_PKCS82PKEY(p8inf.get()));
    if (pkey) {
      return pkey;
    }
    ERR_clear_error();
  }

  // Finally try traditional format
  rewind(in_file);
  EVP_PKEY *raw_pkey = nullptr;
  if (PEM_read_PrivateKey(in_file, &raw_pkey, nullptr,
                         const_cast<char*>(passin))) {
    pkey.reset(raw_pkey);
    return pkey;
  }

  // If we get here, all attempts failed
  return nullptr;
}

bool pkcs8Tool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  bool help = false;
  GetBoolArgument(&help, "-help", parsed_args);
  if (help) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in_path, out_path;
  std::string v2_cipher, v2_prf;
  std::string passin_arg, passout_arg;
  bool topk8 = false, nocrypt = false;

  GetString(&in_path, "-in", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetBoolArgument(&topk8, "-topk8", parsed_args);
  GetBoolArgument(&nocrypt, "-nocrypt", parsed_args);
  GetString(&v2_cipher, "-v2", "", parsed_args);
  GetString(&v2_prf, "-v2prf", "", parsed_args);
  GetString(&passin_arg, "-passin", "", parsed_args);
  GetString(&passout_arg, "-passout", "", parsed_args);

  if (in_path.empty()) {
    fprintf(stderr, "Error: missing required argument '-in'\n");
    return false;
  }

  ScopedFILE in_file(fopen(in_path.c_str(), "rb"));
  if (!in_file) {
    fprintf(stderr, "Error: unable to open input file '%s'\n", in_path.c_str());
    return false;
  }

  ScopedFILE out_file;
  if (!out_path.empty()) {
    out_file.reset(fopen(out_path.c_str(), "wb"));
    if (!out_file) {
      fprintf(stderr, "Error: unable to open output file '%s'\n", out_path.c_str());
      return false;
    }
  }
  FILE *out = out_file.get() ? out_file.get() : stdout;

  // Extract password from pass:xxx format if present
  const char* passin = nullptr;
  const char* passout = nullptr;

  if (!passin_arg.empty()) {
    if (passin_arg.compare(0, 5, "pass:") == 0) {
      passin = passin_arg.c_str() + 5;
    } else {
      passin = passin_arg.c_str();
    }
  }

  if (!passout_arg.empty()) {
    if (passout_arg.compare(0, 5, "pass:") == 0) {
      passout = passout_arg.c_str() + 5;
    } else {
      passout = passout_arg.c_str();
    }
  }

  // Read the private key using the improved method
  bssl::UniquePtr<EVP_PKEY> pkey = read_private_key(in_file.get(), passin);
  if (!pkey) {
    fprintf(stderr, "Error: Failed to read private key from '%s'\n", in_path.c_str());
    fprintf(stderr, "Check that the file contains a valid key and the password (if any) is correct\n");
    print_errors();
    return false;
  }

  bool result = false;

  if (topk8) {
    bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(EVP_PKEY2PKCS8(pkey.get()));
    if (!p8inf) {
      fprintf(stderr, "Error: Failed to convert key to PKCS#8 format\n");
      print_errors();
      return false;
    }

    if (nocrypt) {
      result = PEM_write_PKCS8_PRIV_KEY_INFO(out, p8inf.get());
    } else {
      const EVP_CIPHER *cipher = nullptr;
      if (!v2_cipher.empty()) {
        cipher = EVP_get_cipherbyname(v2_cipher.c_str());
        if (!cipher) {
          fprintf(stderr, "Error: Unknown cipher %s\n", v2_cipher.c_str());
          return false;
        }
      } else {
        cipher = EVP_aes_256_cbc();
      }

      if (!v2_prf.empty()) {
        int pbe_nid = OBJ_txt2nid(v2_prf.c_str());
        if (pbe_nid == NID_undef) {
          fprintf(stderr, "Error: Unknown PRF algorithm %s\n", v2_prf.c_str());
          return false;
        }
        if (pbe_nid != NID_hmacWithSHA1) {
          fprintf(stderr, "Error: AWS-LC only supports hmacWithSHA1 as the PRF algorithm\n");
          fprintf(stderr, "PRF specified: %s\n", v2_prf.c_str());
          return false;
        }
      }

      if (!passout) {
        fprintf(stderr, "Error: -passout must be provided for encryption\n");
        return false;
      }

      bssl::UniquePtr<X509_SIG> p8_enc(
          PKCS8_encrypt(-1, cipher, passout, strlen(passout),
                       nullptr, 0, PKCS12_DEFAULT_ITER, p8inf.get()));

      if (!p8_enc) {
        fprintf(stderr, "Error: Failed to encrypt private key using PKCS#5 v2.0\n");
        print_errors();
        return false;
      }

      result = PEM_write_PKCS8(out, p8_enc.get());
    }
  } else {
    result = PEM_write_PrivateKey(out, pkey.get(), nullptr, nullptr, 0, nullptr, nullptr);
  }

  if (!result) {
    fprintf(stderr, "Error: Failed to write private key\n");
    print_errors();
    return false;
  }

  return true;
}
