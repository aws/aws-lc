// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <fcntl.h>
#include <string.h>
#include <iostream>

#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/pem.h>

#include "internal.h"

// MD5 command currently only supports stdin
static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-binary", kBooleanArgument, "Output in binary form"},
    {"-hex", kBooleanArgument, "Output as hex dump"},
    {"-md5", kExclusiveBooleanArgument, "Supported digest function"},
    {"-ripemd160", kExclusiveBooleanArgument, "Supported digest function"},
    {"-sha1", kExclusiveBooleanArgument, "Supported digest function"},
    {"-sha256", kExclusiveBooleanArgument,
     "Supported digest function (default)"},
    {"-sha224", kExclusiveBooleanArgument, "Supported digest function"},
    {"-sha384", kExclusiveBooleanArgument, "Supported digest function"},
    {"-sha512", kExclusiveBooleanArgument, "Supported digest function"},
    {"-hmac", kOptionalArgument,
     "Create a hashed MAC with the corresponding key"},
    {"-sigopt", kDuplicateArgument, "Signature parameter in n:v form"},
    {"-passin", kOptionalArgument, "Input file pass phrase source"},
    {"-sign", kOptionalArgument, "Sign digest using private key"},
    {"-out", kOptionalArgument, "Output to filename rather than stdout"},
    {"-verify", kOptionalArgument, "Verify a signature using public key"},
    {"-signature", kOptionalArgument, "File with signature to verify"},
    {"-keyform", kOptionalArgument, "key file format (only PEM is supported)"},
    {"", kOptionalArgument, ""}};

static bool LoadPrivateKey(const std::string &key_file_path,
                           Password &passin,
                           bssl::UniquePtr<EVP_PKEY> &pkey) {
  ScopedFILE key_file(fopen(key_file_path.c_str(), "rb"));

  if (!key_file) {
    fprintf(stderr, "Failed to open %s", key_file_path.c_str());
    return false;
  }

  if (!passin.empty() && !pass_util::ExtractPassword(passin)) {
    fprintf(stderr, "Error: Failed to extract password\n");
    return false;
  }

  pkey.reset(PEM_read_PrivateKey(key_file.get(), nullptr, nullptr,
                                 const_cast<char *>(passin.get().c_str())));

  if (!pkey) {
    fprintf(stderr, "Failed to read private key from %s",
            key_file_path.c_str());
    return false;
  }

  return true;
}

static bool LoadPublicKey(const std::string &key_file_path,
                          bssl::UniquePtr<EVP_PKEY> &pkey) {
  ScopedFILE key_file(fopen(key_file_path.c_str(), "rb"));

  if (!key_file) {
    fprintf(stderr, "Failed to open %s", key_file_path.c_str());
    return false;
  }

  pkey.reset(PEM_read_PUBKEY(key_file.get(), nullptr, nullptr, nullptr));

  if (!pkey) {
    fprintf(stderr, "Failed to read public key from %s", key_file_path.c_str());
    return false;
  }

  return true;
}

static std::string GetSigName(int nid) {
  switch (nid) {
    case EVP_PKEY_RSA:
      return "RSA";

    case EVP_PKEY_RSA_PSS:
      return "RSA-PSS";

    case EVP_PKEY_EC:
      return "ECDSA";

    default: {
      /* Try to output provider-registered sig alg name */
      const char *name = OBJ_nid2sn(nid);
      return name ? std::string(name) : "UNKNOWN";
    }
  }
}

static bool GenerateHash(FILE *in_file, const std::string &in_path,
                         const EVP_MD *digest, std::vector<uint8_t> &hash) {
  bssl::ScopedEVP_MD_CTX ctx;

  if (!EVP_DigestInit_ex(ctx.get(), digest, nullptr)) {
    fprintf(stderr, "Failed to initialize digest context.\n");
    return false;
  }

  uint8_t buf[4096];
  for (;;) {
    if (feof(in_file)) {
      break;
    }

    size_t n = fread(buf, 1, sizeof(buf), in_file);

    if (ferror(in_file)) {
      fprintf(stderr, "Error reading from '%s'.\n", in_path.c_str());
      return false;
    }

    if (!EVP_DigestUpdate(ctx.get(), buf, n)) {
      fprintf(stderr, "Failed to update signature.\n");
      return false;
    }
  }

  unsigned hash_len = hash.size();

  if (!EVP_DigestFinal_ex(ctx.get(), hash.data(), &hash_len)) {
    fprintf(stderr, "Failed to finish signature.\n");
    return false;
  }

  hash.resize(hash_len);

  return true;
}

static bool GenerateHMAC(FILE *in_file, const std::string &in_path,
                         const char *hmac_key, const size_t hmac_key_len,
                         const EVP_MD *digest, std::vector<uint8_t> &mac) {
  bssl::ScopedHMAC_CTX ctx;
  if (!HMAC_Init_ex(ctx.get(), hmac_key, hmac_key_len, digest, nullptr)) {
    fprintf(stderr, "Failed to initialize HMAC_Init_ex.\n");
    return false;
  }

  uint8_t buf[4096];
  for (;;) {
    if (feof(in_file)) {
      break;
    }

    size_t n = fread(buf, 1, sizeof(buf), in_file);

    if (ferror(in_file)) {
      fprintf(stderr, "Error reading from '%s'.\n", in_path.c_str());
      return false;
    }

    if (!HMAC_Update(ctx.get(), buf, n)) {
      fprintf(stderr, "Failed to update HMAC.\n");
      return false;
    }
  }

  unsigned mac_len = mac.size();
  if (!HMAC_Final(ctx.get(), mac.data(), &mac_len)) {
    fprintf(stderr, "Failed to finalize HMAC.\n");
    return false;
  }

  mac.resize(mac_len);

  return true;
}

static bool GenerateSignature(EVP_PKEY *pkey, FILE *in_file,
                              const std::string &in_path, const EVP_MD *digest,
                              const std::vector<std::string> &sigopts,
                              std::vector<uint8_t> &signature) {
  bssl::ScopedEVP_MD_CTX ctx;
  EVP_PKEY_CTX *pctx = nullptr;

  if (!EVP_DigestSignInit(ctx.get(), &pctx, digest, nullptr, pkey)) {
    fprintf(stderr, "Failed to initialize digest context.\n");
    return false;
  }

  if (sigopts.size() > 0) {
    for (const auto &sigopt : sigopts) {
      if (!ApplyPkeyCtrlString(pctx, sigopt.c_str())) {
        fprintf(stderr, "Signature parameter error \"%s\"\n", sigopt.c_str());
        return false;
      }
    }
  }

  uint8_t buf[4096];
  for (;;) {
    if (feof(in_file)) {
      break;
    }

    size_t n = fread(buf, 1, sizeof(buf), in_file);

    if (ferror(in_file)) {
      fprintf(stderr, "Error reading from '%s'.\n", in_path.c_str());
      return false;
    }

    if (!EVP_DigestSignUpdate(ctx.get(), buf, n)) {
      fprintf(stderr, "Failed to update signature.\n");
      return false;
    }
  }

  size_t signature_len = signature.size();

  if (!EVP_DigestSignFinal(ctx.get(), signature.data(), &signature_len)) {
    fprintf(stderr, "Failed to finish signature.\n");
    return false;
  }

  signature.resize(signature_len);

  return true;
}

static bool VerifySignature(EVP_PKEY *pkey, FILE *in_file,
                            const std::string &in_path, const EVP_MD *digest,
                            const std::vector<std::string> &sigopts,
                            const std::string &signature_file_path,
                            BIO *out_bio) {
  bssl::ScopedEVP_MD_CTX ctx;
  EVP_PKEY_CTX *pctx = nullptr;

  if (!EVP_DigestVerifyInit(ctx.get(), &pctx, digest, nullptr, pkey)) {
    fprintf(stderr, "Failed to initialize digest context.\n");
    return false;
  }

  if (sigopts.size() > 0) {
    for (const auto &sigopt : sigopts) {
      if (!ApplyPkeyCtrlString(pctx, sigopt.c_str())) {
        fprintf(stderr, "Signature parameter error \"%s\"\n", sigopt.c_str());
        return false;
      }
    }
  }

  uint8_t buf[4096];
  for (;;) {
    if (feof(in_file)) {
      break;
    }

    size_t n = fread(buf, 1, sizeof(buf), in_file);

    if (ferror(in_file)) {
      fprintf(stderr, "Error reading from '%s'.\n", in_path.c_str());
      return false;
    }

    if (!EVP_DigestVerifyUpdate(ctx.get(), buf, n)) {
      fprintf(stderr, "Failed to update signature.\n");
      return false;
    }
  }
  std::vector<uint8_t> signature;
  ScopedFILE signature_file(fopen(signature_file_path.c_str(), "rb"));
  if (!signature_file) {
    fprintf(stderr, "Error opening signature file %s.\n",
            signature_file_path.c_str());
    return false;
  }

  if (!ReadAll(&signature, signature_file.get())) {
    fprintf(stderr, "Error reading from signature file %s.\n",
            signature_file_path.c_str());
    return false;
  }

  int result =
      EVP_DigestVerifyFinal(ctx.get(), signature.data(), signature.size());

  if (result > 0) {
    if (BIO_printf(out_bio, "Verified OK\n") <= 0) {
      goto end;
    }
  } else if (result == 0) {
    if (BIO_printf(out_bio, "Verification failure\n") <= 0) {
      goto end;
    }
  } else {
    if (BIO_printf(out_bio, "Error verifying data\n") <= 0) {
      goto end;
    }
  }

  return true;

end:
  fprintf(stderr, "Error writing output to %s.\n", in_path.c_str());
  return false;
}

static bool WriteOutput(BIO *out_bio, const std::vector<uint8_t> &data,
                        const std::string &sig_name,
                        const std::string &digest_name,
                        const std::string &in_path, bool out_bin) {
  if (out_bin) {
    if (BIO_write(out_bio, data.data(), data.size()) <= 0) {
      goto end;
    }
  } else {
    if (!sig_name.empty()) {
      if (BIO_printf(out_bio, "%s-%s", sig_name.c_str(), digest_name.c_str()) <=
          0) {
        goto end;
      }
    } else {
      if (BIO_printf(out_bio, "%s", digest_name.c_str()) <= 0) {
        goto end;
      }
    }

    if (!in_path.empty()) {
      if (BIO_printf(out_bio, "(%s)=", in_path.c_str()) <= 0) {
        goto end;
      }
    } else {
      if (BIO_printf(out_bio, "(stdin)=") <= 0) {
        goto end;
      }
    }

    for (size_t i = 0; i < data.size(); i++) {
      if (BIO_printf(out_bio, "%02x", data[i]) <= 0) {
        goto end;
      }
    }

    if (BIO_printf(out_bio, "\n") <= 0) {
      goto end;
    }
  }

  return true;

end:
  fprintf(stderr, "Error writing output to %s.\n", in_path.c_str());
  return false;
}

static bool dgstToolInternal(const args_list_t &args, const EVP_MD *digest) {
  std::vector<std::string> in_files;

  using namespace ordered_args;
  ordered_args_map_t parsed_args;

  if (!ParseOrderedKeyValueArguments(parsed_args, in_files, args, kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  std::string hmac, digest_name, sign_key_file, out_path, verify_key_file,
      signature_file, keyform;
  std::vector<std::string> sigopts;
  Password passin;
  bool out_bin = false, binary = false, hex = false;

  if (HasArgument(parsed_args, "-help")) {
    PrintUsage(kArguments);
    return true;
  }

  GetBoolArgument(&binary, "-binary", parsed_args);
  GetBoolArgument(&hex, "-hex", parsed_args);
  GetString(&hmac, "-hmac", "", parsed_args);
  GetString(&passin.get(), "-passin", "", parsed_args);
  GetString(&sign_key_file, "-sign", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetString(&verify_key_file, "-verify", "", parsed_args);
  GetString(&signature_file, "-signature", "", parsed_args);
  GetString(&keyform, "-keyform", "PEM", parsed_args);
  FindAll(sigopts, "-sigopt", parsed_args);

  // Validate arguments
  if (HasArgument(parsed_args, "-hex") && HasArgument(parsed_args, "-binary")) {
    fprintf(stderr, "Error: -hex and -binary cannot both be specified");
    return false;
  }

  if ((!verify_key_file.empty() + !sign_key_file.empty() + !hmac.empty()) > 1) {
    fprintf(stderr,
            "Error: -verify, -sign, and -hmac cannot be used together\n");
    return false;
  }

  if (!verify_key_file.empty() && signature_file.empty()) {
    fprintf(stderr,
            "Error: No signature to verify: use the -signature option\n");
    return false;
  }

  if (keyform != "PEM") {
    fprintf(stdout, "keyform=%s\n", keyform.c_str());
    fprintf(stderr, "Error: -keyform only accepts type PEM\n");
    return false;
  }

  // Default digest is SHA-256.
  if (digest == nullptr) {
    GetExclusiveBoolArgument(&digest_name, kArguments, "-sha256", parsed_args);
    digest = EVP_get_digestbyname(digest_name.substr(1).c_str());
  }

  if (hex) {
    out_bin = false;
  } else if (binary || !sign_key_file.empty() || !verify_key_file.empty()) {
    out_bin = true;
  }

  bssl::UniquePtr<BIO> out_bio;
  if (out_path.empty()) {
    out_bio.reset(
        BIO_new_fp(stdout, BIO_NOCLOSE | (out_bin ? 0 : BIO_FP_TEXT)));
  } else {
    out_bio.reset(BIO_new_file(out_path.c_str(), (out_bin ? "wb" : "w")));

    if (!out_bio) {
      fprintf(stderr, "Error: Failed to open output file: %s\n",
              out_path.c_str());
      return false;
    }
  }

  bssl::UniquePtr<EVP_PKEY> pkey;
  size_t i = 0;
  do {
    ScopedFILE in_file;
    std::string in_path;
    if (in_files.empty()) {
      in_path = "stdin";
      in_file.reset(stdin);
    } else {
      in_path = in_files[i++];
      in_file.reset(fopen(in_path.c_str(), "rb"));
      if (!in_file) {
        fprintf(stderr, "Error: unable to open input file '%s'\n",
                in_path.c_str());
        return false;
      }
    }

    if (!hmac.empty()) {
      const char *hmac_key = hmac.c_str();
      size_t hmac_key_len = hmac.length();

      std::vector<uint8_t> mac(EVP_MD_size(digest));

      if (!GenerateHMAC(in_file.get(), in_path, hmac_key, hmac_key_len, digest,
                        mac)) {
        return false;
      }

      WriteOutput(out_bio.get(), mac, "HMAC", EVP_MD_get0_name(digest), in_path,
                  out_bin);
    } else if (!verify_key_file.empty()) {
      if (!LoadPublicKey(verify_key_file, pkey)) {
        return false;
      }

      if (!VerifySignature(pkey.get(), in_file.get(), in_path, digest, sigopts,
                           signature_file, out_bio.get())) {
        return false;
      }
    } else if (!sign_key_file.empty()) {
      if (!LoadPrivateKey(sign_key_file, passin, pkey)) {
        return false;
      }

      std::vector<uint8_t> signature(EVP_PKEY_size(pkey.get()));
      if (!GenerateSignature(pkey.get(), in_file.get(), in_path, digest,
                             sigopts, signature)) {
        return false;
      }

      WriteOutput(out_bio.get(), signature, GetSigName(EVP_PKEY_id(pkey.get())),
                  EVP_MD_get0_name(digest), in_path, out_bin);
    } else {
      std::vector<uint8_t> hash(EVP_MAX_MD_SIZE);

      if (!GenerateHash(in_file.get(), in_path, digest, hash)) {
        return false;
      }

      WriteOutput(out_bio.get(), hash, "", EVP_MD_get0_name(digest), in_path,
                  out_bin);
    }

    if (in_files.empty()) {
      break;
    }
  } while (i < in_files.size());

  return true;
}

bool dgstTool(const args_list_t &args) {
  return dgstToolInternal(args, nullptr);
}
bool md5Tool(const args_list_t &args) {
  return dgstToolInternal(args, EVP_md5());
}
bool sha1Tool(const args_list_t &args) {
  return dgstToolInternal(args, EVP_sha1());
}
