// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/pkcs8.h>
#include <openssl/err.h>
#include <cstring>
#include "internal.h"

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-in", kOptionalArgument, "Input file" },
  { "-out", kOptionalArgument, "Output file" },
  { "-inform", kOptionalArgument, "Input format (DER or PEM)" },
  { "-outform", kOptionalArgument, "Output format (DER or PEM)" },
  { "-topk8", kBooleanArgument, "Convert traditional format to PKCS#8" },
  { "-nocrypt", kBooleanArgument, "Use unencrypted private key" },
  { "-v2", kOptionalArgument, "Use PKCS#5 v2.0 and specified cipher" },
  { "-v2prf", kOptionalArgument, "Use specified PRF algorithm with PKCS#5 v2.0" },
  { "-passin", kOptionalArgument, "Input file passphrase source" },
  { "-passout", kOptionalArgument, "Output file passphrase source" },
  { "", kOptionalArgument, "" }
};

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

  // Parse options
  std::string in_path, out_path, inform, outform;
  std::string v2_cipher, v2prf;
  std::string passin_arg, passout_arg;
  bool topk8 = false, nocrypt = false;

  GetString(&in_path, "-in", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetString(&inform, "-inform", "PEM", parsed_args);
  GetString(&outform, "-outform", "PEM", parsed_args);
  GetBoolArgument(&topk8, "-topk8", parsed_args);
  GetBoolArgument(&nocrypt, "-nocrypt", parsed_args);
  GetString(&v2_cipher, "-v2", "", parsed_args);
  GetString(&v2prf, "-v2prf", "", parsed_args);
  GetString(&passin_arg, "-passin", "", parsed_args);
  GetString(&passout_arg, "-passout", "", parsed_args);

  // Check required arguments
  if (in_path.empty()) {
    fprintf(stderr, "Error: missing required argument '-in'\n");
    return false;
  }

  // Convert format strings to uppercase for consistent comparison
  for (auto &c : inform) c = toupper(c);
  for (auto &c : outform) c = toupper(c);

  // Validate formats
  if (inform != "PEM" && inform != "DER") {
    fprintf(stderr, "Error: Invalid input format. Must be PEM or DER.\n");
    return false;
  }
  if (outform != "PEM" && outform != "DER") {
    fprintf(stderr, "Error: Invalid output format. Must be PEM or DER.\n");
    return false;
  }

  // Open input file
  ScopedFILE in_file(fopen(in_path.c_str(), "rb"));
  if (!in_file) {
    fprintf(stderr, "Error: unable to open input file '%s'\n", in_path.c_str());
    return false;
  }

  // Prepare output file
  ScopedFILE out_file;
  if (!out_path.empty()) {
    out_file.reset(fopen(out_path.c_str(), "wb"));
    if (!out_file) {
      fprintf(stderr, "Error: unable to open output file '%s'\n", out_path.c_str());
      return false;
    }
  }
  FILE *out = out_file.get() ? out_file.get() : stdout;

  // Get passwords if needed
  char *passin = nullptr, *passout = nullptr;
  if (!passin_arg.empty()) {
    passin = OPENSSL_strdup(passin_arg.c_str());
    if (!passin) {
      fprintf(stderr, "Error: memory allocation failure\n");
      return false;
    }
  }
  
  if (!passout_arg.empty()) {
    passout = OPENSSL_strdup(passout_arg.c_str());
    if (!passout) {
      OPENSSL_free(passin);
      fprintf(stderr, "Error: memory allocation failure\n");
      return false;
    }
  }

  // Read the private key
  EVP_PKEY *pkey = nullptr;
  if (inform == "PEM") {
    pkey = PEM_read_PrivateKey(in_file.get(), nullptr, nullptr, passin);
  } else {  // DER
    uint8_t *data = nullptr;
    long len;
    if (fseek(in_file.get(), 0, SEEK_END) != 0 ||
        (len = ftell(in_file.get())) < 0 ||
        fseek(in_file.get(), 0, SEEK_SET) != 0) {
      OPENSSL_free(passin);
      OPENSSL_free(passout);
      fprintf(stderr, "Error: failed to determine input file size\n");
      return false;
    }
    
    data = (uint8_t *)OPENSSL_malloc(len);
    if (!data || fread(data, 1, len, in_file.get()) != (size_t)len) {
      OPENSSL_free(data);
      OPENSSL_free(passin);
      OPENSSL_free(passout);
      fprintf(stderr, "Error: failed to read input file\n");
      return false;
    }
    
    const uint8_t *p = data;
    pkey = d2i_AutoPrivateKey(nullptr, &p, len);  // Support for all key types
    OPENSSL_free(data);
  }
  
  if (!pkey) {
    OPENSSL_free(passin);
    OPENSSL_free(passout);
    fprintf(stderr, "Error: Failed to read private key from '%s'\n", in_path.c_str());
    fprintf(stderr, "Check that the file contains a valid key and the password (if any) is correct\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  // Process according to options
  bool result = false;
  if (topk8) {
    // Convert to PKCS#8
    if (nocrypt) {
      // Unencrypted PKCS#8
        PKCS8_PRIV_KEY_INFO *p8inf = EVP_PKEY2PKCS8(pkey);
        if (!p8inf) {
          fprintf(stderr, "Error: Failed to convert key to PKCS#8 format\n");
          fprintf(stderr, "The key type may not be supported for PKCS#8 conversion\n");
          ERR_print_errors_fp(stderr);
      } else {
        // Write the output
        if (outform == "PEM") {
          result = PEM_write_PKCS8_PRIV_KEY_INFO(out, p8inf);
        } else {  // DER
          result = i2d_PKCS8_PRIV_KEY_INFO_fp(out, p8inf);
        }
        PKCS8_PRIV_KEY_INFO_free(p8inf);
      }
    } else {
      // Encrypted PKCS#8
      if (!v2_cipher.empty()) {
        // Use PKCS#5 v2.0
        const EVP_CIPHER *cipher = EVP_get_cipherbyname(v2_cipher.c_str());
        if (!cipher) {
          fprintf(stderr, "Error: Unknown cipher %s\n", v2_cipher.c_str());
          EVP_PKEY_free(pkey);
          OPENSSL_free(passin);
          OPENSSL_free(passout);
          return false;
        }
        
        // Handle PRF algorithm if specified
        // Note: While OpenSSL supports explicit PRF selection, AWS-LC uses its default PRF
        // implementation for PKCS#8 encryption. The -v2prf parameter is accepted for
        // command-line compatibility but does not affect the actual PRF used.
        if (!v2prf.empty()) {
          // In AWS-LC, we'll validate that it's one of the known values to maintain compatibility
          if (v2prf != "hmacWithSHA1" && 
              v2prf != "hmacWithSHA256" && 
              v2prf != "hmacWithSHA512") {
            fprintf(stderr, "Error: Unknown PRF %s\n", v2prf.c_str());
            EVP_PKEY_free(pkey);
            OPENSSL_free(passin);
            OPENSSL_free(passout);
            return false;
          }
          // The PRF specification is validated but not used by AWS-LC implementation
        }
        
        // Convert and encrypt
        X509_SIG *p8 = nullptr;
        if (passout) {
          PKCS8_PRIV_KEY_INFO *p8inf = EVP_PKEY2PKCS8(pkey);
          if (!p8inf) {
            fprintf(stderr, "Error: Failed to convert key to PKCS#8 format\n");
            ERR_print_errors_fp(stderr);
          } else {
            // Always use the default PRF (-1) with the specified cipher
            // AWS-LC's implementation ignores explicit PRF specifications
            p8 = PKCS8_encrypt(-1, cipher, passout, strlen(passout), 
                              NULL, 0, PKCS12_DEFAULT_ITER, p8inf);
            if (!p8) {
              fprintf(stderr, "Error: Failed to encrypt private key\n");
              fprintf(stderr, "Encryption parameters may be invalid or unsupported\n");
              ERR_print_errors_fp(stderr);
            }
            PKCS8_PRIV_KEY_INFO_free(p8inf);
          }
        }
        
        if (p8) {
          // Write the output
          if (outform == "PEM") {
            result = PEM_write_PKCS8(out, p8);
          } else {  // DER
            result = i2d_PKCS8_fp(out, p8);
          }
          X509_SIG_free(p8);
        }
      } else {
        fprintf(stderr, "Error: Encryption requested but no cipher specified with -v2\n");
      }
    }
  } else {
    // Just convert between PEM and DER without changing format
    if (outform == "PEM") {
      result = PEM_write_PrivateKey(out, pkey, nullptr, nullptr, 0, nullptr, nullptr);
    } else {  // DER
      result = i2d_PrivateKey_fp(out, pkey);
    }
  }

  // Clean up
  EVP_PKEY_free(pkey);
  OPENSSL_free(passin);
  OPENSSL_free(passout);
  
  if (!result) {
    fprintf(stderr, "Error: Failed to write private key\n");
    fprintf(stderr, "Check file permissions and available disk space\n");
    ERR_print_errors_fp(stderr);
    return false;
  }
  
  return true;
}
