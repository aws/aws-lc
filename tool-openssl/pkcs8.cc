// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
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
  OpenSSLPointer<char> passin_ptr;
  OpenSSLPointer<char> passout_ptr;
  char *passin = nullptr, *passout = nullptr;

  if (!passin_arg.empty()) {
    passin_ptr.reset(OPENSSL_strdup(passin_arg.c_str()));
    if (!passin_ptr) {
      fprintf(stderr, "Error: memory allocation failure\n");
      return false;
    }
    passin = passin_ptr.get();
  }
  
  if (!passout_arg.empty()) {
    passout_ptr.reset(OPENSSL_strdup(passout_arg.c_str()));
    if (!passout_ptr) {
      fprintf(stderr, "Error: memory allocation failure\n");
      return false;
    }
    passout = passout_ptr.get();
  }

  // Read the private key
  bssl::UniquePtr<EVP_PKEY> pkey;
  
  if (inform == "PEM") {
    // Check if this might be a PKCS#8 encrypted key first
    bool is_pkcs8_encrypted = false;
    char line[100];
    long pos = ftell(in_file.get());
    
    // Check the header to determine if it's an encrypted PKCS#8 key
    if (fgets(line, sizeof(line), in_file.get())) {
      is_pkcs8_encrypted = (strstr(line, "-----BEGIN ENCRYPTED PRIVATE KEY-----") != nullptr);
      fprintf(stderr, "DEBUG: Key format detection - PKCS#8 encrypted? %s\n", is_pkcs8_encrypted ? "Yes" : "No");
    }
    fseek(in_file.get(), pos, SEEK_SET); // Reset position
    
    if (is_pkcs8_encrypted && passin != nullptr) {
      fprintf(stderr, "DEBUG: Attempting to process PKCS#8 encrypted key with password\n");
      
      // Handle encrypted PKCS#8 format using a more direct approach
      long pos_before_read = ftell(in_file.get());
      X509_SIG *p8 = PEM_read_PKCS8(in_file.get(), NULL, NULL, NULL);
      
      if (p8) {
        fprintf(stderr, "DEBUG: Successfully read PKCS#8 encrypted structure\n");
        
        // Print algorithm OID if available
        const X509_ALGOR *algor = NULL;
        const ASN1_OCTET_STRING *oct = NULL;
        X509_SIG_get0(p8, &algor, &oct);
        if (algor && algor->algorithm) {
          int pbe_nid = OBJ_obj2nid(algor->algorithm);
          const char *pbe_name = OBJ_nid2sn(pbe_nid);
          fprintf(stderr, "DEBUG: Encryption algorithm: %s (NID: %d)\n", 
                  pbe_name ? pbe_name : "Unknown", pbe_nid);
        }
        
        // For PBES2 specifically, implement a more direct method if needed
        fprintf(stderr, "DEBUG: Attempting decryption with password (length: %zu)\n", 
                passin ? strlen(passin) : 0);
                
        // First try the standard decryption
        PKCS8_PRIV_KEY_INFO *p8inf = PKCS8_decrypt(p8, passin, strlen(passin));
        
        // If standard decryption fails for PBES2, reset and try manual PEM parsing approach
        if (!p8inf && algor && algor->algorithm && 
            OBJ_obj2nid(algor->algorithm) == NID_pbes2) {
          fprintf(stderr, "DEBUG: Standard PBES2 decryption failed, trying alternative approach\n");
          
          // Rewind file and try raw data read
          fseek(in_file.get(), pos_before_read, SEEK_SET);
            
          // Manual approach to read and parse the PEM data
          // Reset position to beginning of file and try standard PEM private key read
          // This may work because some implementations can handle PKCS#8 directly
          pkey.reset(PEM_read_PrivateKey(in_file.get(), nullptr, nullptr, passin));
          if (pkey) {
            fprintf(stderr, "DEBUG: Successfully decrypted using direct PEM_read_PrivateKey\n");
            X509_SIG_free(p8);
            return true; // We have a key, continue with normal flow
          }
          
          // If we get here, return to original position for fallback
          fseek(in_file.get(), pos_before_read, SEEK_SET);
        }
        
        if (!p8inf) {
          fprintf(stderr, "DEBUG: PKCS8_decrypt failed. Error stack:\n");
          ERR_print_errors_fp(stderr);
        }
        
        X509_SIG_free(p8);
        
        if (p8inf) {
          // Successfully decrypted, convert to EVP_PKEY
          fprintf(stderr, "DEBUG: Successfully decrypted PKCS#8 structure\n");
          pkey.reset(EVP_PKCS82PKEY(p8inf));
          
          if (!pkey) {
            fprintf(stderr, "DEBUG: EVP_PKCS82PKEY failed. Error stack:\n");
            ERR_print_errors_fp(stderr);
          } else {
            fprintf(stderr, "DEBUG: Successfully converted to EVP_PKEY\n");
          }
          
          PKCS8_PRIV_KEY_INFO_free(p8inf);
        } else {
          // Reset file position to try the regular method
          fprintf(stderr, "DEBUG: Failed to decrypt PKCS#8 structure, trying fallback method\n");
          fseek(in_file.get(), pos, SEEK_SET);
        }
      } else {
        // Reset file position to try the regular method
        fprintf(stderr, "DEBUG: Failed to read PKCS#8 structure, trying fallback method\n");
        fprintf(stderr, "DEBUG: Error stack:\n");
        ERR_print_errors_fp(stderr);
        fseek(in_file.get(), pos, SEEK_SET);
      }
    }
    
    // If we don't have a key yet, try the regular PEM reader
    if (!pkey) {
      // TODO: Use EVP_read_pw_string once implemented in AWS-LC
      // to prompt for password if not provided and key is encrypted
      pkey.reset(PEM_read_PrivateKey(in_file.get(), nullptr, nullptr, passin));
    }
  } else {  // DER
    long len;
    if (fseek(in_file.get(), 0, SEEK_END) != 0 ||
        (len = ftell(in_file.get())) < 0 ||
        fseek(in_file.get(), 0, SEEK_SET) != 0) {
      fprintf(stderr, "Error: failed to determine input file size\n");
      return false;
    }
    
    OpenSSLPointer<uint8_t> data((uint8_t*)OPENSSL_malloc(len));
    if (!data || fread(data.get(), 1, len, in_file.get()) != (size_t)len) {
      fprintf(stderr, "Error: failed to read input file\n");
      return false;
    }
    
    const uint8_t *p = data.get();
    
    // First try to detect and decrypt PKCS#8 format
    bssl::UniquePtr<BIO> mem_bio(BIO_new_mem_buf(data.get(), len));
    if (mem_bio) {
      X509_SIG *p8 = d2i_PKCS8_bio(mem_bio.get(), NULL);
      
      if (p8 && passin != nullptr) {
        // We have a valid PKCS#8 encrypted structure, attempt decryption
        PKCS8_PRIV_KEY_INFO *p8inf = PKCS8_decrypt(p8, passin, strlen(passin));
        X509_SIG_free(p8);
        
        if (p8inf) {
          // Successfully decrypted, convert to EVP_PKEY
          pkey.reset(EVP_PKCS82PKEY(p8inf));
          PKCS8_PRIV_KEY_INFO_free(p8inf);
        }
      } else if (p8) {
        X509_SIG_free(p8);
      }
    }
    
    // If we couldn't get the key via PKCS#8, try the regular method
    if (!pkey) {
      p = data.get();  // Reset pointer
      pkey.reset(d2i_AutoPrivateKey(nullptr, &p, len));  // Support for all key types
    }
  }
  
  if (!pkey) {
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
      bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(EVP_PKEY2PKCS8(pkey.get()));
      if (!p8inf) {
        fprintf(stderr, "Error: Failed to convert key to PKCS#8 format\n");
        fprintf(stderr, "The key type may not be supported for PKCS#8 conversion\n");
        ERR_print_errors_fp(stderr);
      } else {
        // Write the output
        if (outform == "PEM") {
          result = PEM_write_PKCS8_PRIV_KEY_INFO(out, p8inf.get());
        } else {  // DER
          result = i2d_PKCS8_PRIV_KEY_INFO_fp(out, p8inf.get());
        }
      }
    } else {
      // Encrypted PKCS#8
      const EVP_CIPHER *cipher = nullptr;
      
      // Get cipher from -v2 option or default to aes-256-cbc
      if (!v2_cipher.empty()) {
        // User specified a cipher with -v2
        cipher = EVP_get_cipherbyname(v2_cipher.c_str());
        if (!cipher) {
          fprintf(stderr, "Error: Unknown cipher %s\n", v2_cipher.c_str());
          return false;
        }
      } else {
        // Default to aes-256-cbc for OpenSSL 1.1.1 compatibility
        cipher = EVP_aes_256_cbc();
      }
      
      // Handle PRF algorithm if specified
      // Note: AWS-LC only supports hmacWithSHA1 for PKCS#8 v2 encryption.
      // For compatibility with OpenSSL, the -v2prf parameter is accepted but
      // must be set to "hmacWithSHA1" or omitted.
      if (!v2prf.empty()) {
        if (v2prf != "hmacWithSHA1") {
          fprintf(stderr, "Error: AWS-LC only supports hmacWithSHA1 as the PRF algorithm\n");
          fprintf(stderr, "PRF specified: %s\n", v2prf.c_str());
          return false;
        }
        // The PRF specification is validated to ensure it's hmacWithSHA1
      }
      
      // Convert and encrypt
      bssl::UniquePtr<X509_SIG> p8;
      
      // TODO: Use EVP_read_pw_string once implemented in AWS-LC
      // If no password is provided, prompt for one (twice for verification)
      // char password_buf[256];
      // if (!passout) {
      //   if (EVP_read_pw_string(password_buf, sizeof(password_buf), "Enter Encryption Password:", 1) != 0) {
      //     fprintf(stderr, "Error: Failed to read password\n");
      //     return false;
      //   }
      //   passout = password_buf;
      // }
      
      if (!passout)
      {
        fprintf(stderr, "Error: -passout must be provided for encryption\n");
          ERR_print_errors_fp(stderr);
      }
      else {
        bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(EVP_PKEY2PKCS8(pkey.get()));
        if (!p8inf) {
          fprintf(stderr, "Error: Failed to convert key to PKCS#8 format\n");
          ERR_print_errors_fp(stderr);
        } else {
          // Always use the default PRF (-1) with the specified cipher
          // AWS-LC only supports hmacWithSHA1 (which is what -1 selects)
          p8.reset(PKCS8_encrypt(-1, cipher, passout, strlen(passout),
                         NULL, 0, PKCS12_DEFAULT_ITER, p8inf.get()));
          if (!p8) {
            fprintf(stderr, "Error: Failed to encrypt private key\n");
            fprintf(stderr, "Encryption parameters may be invalid or unsupported\n");
            ERR_print_errors_fp(stderr);
          }
        }
      }
      
      
      
      if (p8) {
        // Write the output
        if (outform == "PEM") {
          result = PEM_write_PKCS8(out, p8.get());
        } else {  // DER
          result = i2d_PKCS8_fp(out, p8.get());
        }
      }
    }
  } else {
    // Handle non-PKCS#8 format
    if (parsed_args.count("-v2") > 0) {
      // Encryption requested without -topk8
      const EVP_CIPHER *cipher = nullptr;
      
      // Get the cipher
      if (!v2_cipher.empty()) {
        cipher = EVP_get_cipherbyname(v2_cipher.c_str());
        if (!cipher) {
          fprintf(stderr, "Error: Unknown cipher %s\n", v2_cipher.c_str());
          return false;
        }
      } else {
        // Default to aes-256-cbc
        cipher = EVP_aes_256_cbc();
      }
      
      // Encrypt the private key
      if (outform == "PEM") {
        result = PEM_write_PrivateKey(out, pkey.get(), cipher, nullptr, 0, nullptr, passout);
      } else {  // DER
        fprintf(stderr, "Error: Encrypted DER format is not supported without -topk8\n");
        return false;
      }
    } else {
      // Just convert between PEM and DER without changing format or encrypting
      if (outform == "PEM") {
        result = PEM_write_PrivateKey(out, pkey.get(), nullptr, nullptr, 0, nullptr, nullptr);
      } else {  // DER
        result = i2d_PrivateKey_fp(out, pkey.get());
      }
    }
  }

  // Smart pointers handle cleanup automatically
  
  if (!result) {
    fprintf(stderr, "Error: Failed to write private key\n");
    fprintf(stderr, "Check file permissions and available disk space\n");
    ERR_print_errors_fp(stderr);
    return false;
  }
  
  return true;
}
