// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/rand.h>
#include <stdio.h>
#include <string.h>
#include <algorithm>
#include <iostream>
#include "../tool/internal.h"
#include "internal.h"

#define BUF_SIZE 1024
#define SALT_SIZE 8

static const uint8_t kSaltMagic[] = {'S', 'a', 'l', 't', 'e', 'd', '_', '_'};

static const argument_t kArguments[] = {
    // General options
    {"-help", kBooleanArgument, "Display option summary"},
    {"-in", kOptionalArgument, "Input file, default stdin"},
    {"-out", kOptionalArgument, "Output file, default stdout"},
    {"-e", kBooleanArgument, "Encrypt"},
    {"-d", kBooleanArgument, "Decrypt"},
    {"-nopad", kBooleanArgument, "Disable standard block padding"},
    {"-nosalt", kBooleanArgument, "Do not use salt in key derivation"},
    {"-none", kExclusiveBooleanArgument,
     "Copy input without encryption (default)"},
    {"-K", kOptionalArgument, "Raw key to use, in hex form"},
    {"-iv", kOptionalArgument, "IV to use, in hex form"},
    {"-k", kOptionalArgument, "Passphrase"},
    {"-kfile", kOptionalArgument, "Read passphrase from file"},
    {"-pass", kOptionalArgument, "Passphrase source (pass:, file:, env:)"},
    {"-md", kOptionalArgument,
     "Message digest for key derivation (default sha256)"},
    {"-S", kOptionalArgument, "Salt in hex form"},
    {"-aes-128-cbc", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-128-cfb", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-128-ctr", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-128-ecb", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-128-ofb", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-192-cbc", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-192-cfb", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-192-ctr", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-192-ecb", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-192-ofb", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-256-cbc", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-256-cfb", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-256-ctr", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-256-ecb", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes-256-ofb", kExclusiveBooleanArgument, "Supported cipher"},
    {"-aes128", kExclusiveBooleanArgument, "Supported cipher alias"},
    {"-aes256", kExclusiveBooleanArgument, "Supported cipher alias"},
    {"-des-cbc", kExclusiveBooleanArgument, "Supported cipher"},
    {"-des-ede3-cbc", kExclusiveBooleanArgument, "Supported cipher"},
    {"", kOptionalArgument, ""}};

static bool HexToBinary(uint8_t *buffer, const std::string &hex_string,
                        size_t size) {
  const size_t hex_len = 2 * size;
  if (hex_string.size() < hex_len) {
    fprintf(stderr,
            "hex string is too short, padding with zero bytes to length\n");
  } else if (hex_string.size() > hex_len) {
    fprintf(stderr, "hex string is too long, ignoring excess\n");
  }

  // Like OpenSSL, zero-pad on the right (including an odd trailing nibble) and
  // validate only the retained prefix.
  memset(buffer, 0, size);
  for (size_t i = 0; i < std::min(hex_string.size(), hex_len); i++) {
    uint8_t digit = 0;
    if (!OPENSSL_fromxdigit(&digit, hex_string[i])) {
      return false;
    }
    buffer[i / 2] |= static_cast<uint8_t>(digit << (i % 2 == 0 ? 4 : 0));
  }
  return true;
}

static bool ReadPassphraseFromFile(const std::string &path,
                                   Password &passphrase) {
  ScopedFILE f(fopen(path.c_str(), "r"));
  if (!f) {
    fprintf(stderr, "Error: cannot open passphrase file '%s'\n", path.c_str());
    return false;
  }
  char buf[1024];
  if (!fgets(buf, sizeof(buf), f.get())) {
    fprintf(stderr, "Error: cannot read passphrase from '%s'\n", path.c_str());
    return false;
  }
  size_t len = strlen(buf);
  while (len > 0 && (buf[len - 1] == '\n' || buf[len - 1] == '\r')) {
    buf[--len] = '\0';
  }
  passphrase = Password(std::string(buf, len));
  OPENSSL_cleanse(buf, sizeof(buf));
  return true;
}

static bool ResolvePassphrase(const std::string &source,
                              Password &passphrase) {
  if (source.size() >= 5 && source.substr(0, 5) == "pass:") {
    passphrase = Password(source.substr(5));
    return true;
  }
  if (source.size() >= 5 && source.substr(0, 5) == "file:") {
    return ReadPassphraseFromFile(source.substr(5), passphrase);
  }
  if (source.size() >= 4 && source.substr(0, 4) == "env:") {
    const char *val = getenv(source.substr(4).c_str());
    if (!val) {
      fprintf(stderr, "Error: environment variable '%s' not set\n",
              source.substr(4).c_str());
      return false;
    }
    passphrase = Password(std::string(val));
    return true;
  }
  if (source == "stdin") {
    char buf[1024];
    if (!fgets(buf, sizeof(buf), stdin)) {
      fprintf(stderr, "Error: cannot read passphrase from stdin\n");
      return false;
    }
    size_t len = strlen(buf);
    while (len > 0 && (buf[len - 1] == '\n' || buf[len - 1] == '\r')) {
      buf[--len] = '\0';
    }
    passphrase = Password(std::string(buf, len));
    OPENSSL_cleanse(buf, sizeof(buf));
    return true;
  }
  fprintf(stderr, "Error: unknown passphrase source '%s'\n", source.c_str());
  return false;
}

int encTool(const args_list_t &args) {
  ordered_args::ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ordered_args::ParseOrderedKeyValueArguments(parsed_args, extra_args,
                                                   args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return kToolExitFailure;
  }

  using namespace ordered_args;
  if (HasArgument(parsed_args, "-help")) {
    PrintUsage(kArguments);
    return kToolExitSuccess;
  }

  std::string in_path, out_path;
  Password hex_key, hex_iv;
  GetLastString(&in_path, "-in", "", parsed_args);
  GetLastString(&out_path, "-out", "", parsed_args);
  GetLastString(&hex_key.get(), "-K", "", parsed_args);
  GetLastString(&hex_iv.get(), "-iv", "", parsed_args);
  const bool has_key = HasArgument(parsed_args, "-K");
  const bool has_iv = HasArgument(parsed_args, "-iv");
  const bool nopad = HasArgument(parsed_args, "-nopad");
  const bool nosalt = HasArgument(parsed_args, "-nosalt");
  const bool encode = GetLastOption({"-e", "-d"}, "-e", parsed_args) == "-e";
  // Unlike OpenSSL 1.1.1, which uses the last one, the parser rejects multiple
  // cipher options (including -none). OpenSSL 3.x interprets them differently,
  // and a mismatch could silently skip encryption.
  std::string cipher_name;
  GetExclusiveBoolArgument(&cipher_name, kArguments, "-none", parsed_args);
  cipher_name = cipher_name == "-none" ? "" : cipher_name.substr(1);

  std::string kfile_path, k_value, pass_source, md_name, hex_salt;
  GetLastString(&kfile_path, "-kfile", "", parsed_args);
  GetLastString(&k_value, "-k", "", parsed_args);
  GetLastString(&pass_source, "-pass", "", parsed_args);
  GetLastString(&md_name, "-md", "sha256", parsed_args);
  GetLastString(&hex_salt, "-S", "", parsed_args);

  Password passphrase;
  bool has_passphrase = false;
  if (!kfile_path.empty()) {
    if (!ReadPassphraseFromFile(kfile_path, passphrase)) {
      return kToolExitFailure;
    }
    has_passphrase = true;
  } else if (!k_value.empty()) {
    passphrase = Password(k_value);
    has_passphrase = true;
  } else if (!pass_source.empty()) {
    if (!ResolvePassphrase(pass_source, passphrase)) {
      return kToolExitFailure;
    }
    has_passphrase = true;
  }

  // As in OpenSSL, an absent path or "-" means stdin/stdout.
  ScopedFILE in_file;
  FILE *input = stdin;
  if (!in_path.empty() && in_path != "-") {
    in_file.reset(fopen(in_path.c_str(), "rb"));
    if (!in_file) {
      fprintf(stderr, "Error: unable to load data from '%s'\n",
              in_path.c_str());
      return kToolExitFailure;
    }
    input = in_file.get();
  }

  bssl::UniquePtr<EVP_CIPHER_CTX> ctx;
  uint8_t salt[SALT_SIZE] = {0};
  bool write_salt_header = false;

  if (!cipher_name.empty()) {
    const EVP_CIPHER *cipher = EVP_get_cipherbyname(cipher_name.c_str());
    if (cipher == nullptr) {
      fprintf(stderr, "Error: Unknown cipher %s\n", cipher_name.c_str());
      return kToolExitFailure;
    }

    const size_t key_length = EVP_CIPHER_key_length(cipher);
    const size_t iv_length = EVP_CIPHER_iv_length(cipher);
    uint8_t key[EVP_MAX_KEY_LENGTH] = {0};
    uint8_t iv[EVP_MAX_IV_LENGTH] = {0};

    if (has_key) {
      if (!HexToBinary(key, hex_key.get(), key_length)) {
        OPENSSL_cleanse(key, sizeof(key));
        fprintf(stderr, "Error: Invalid hex key value\n");
        return kToolExitFailure;
      }
      if (has_iv) {
        if (iv_length == 0) {
          fprintf(stderr, "Warning: IV is not used by cipher %s\n",
                  cipher_name.c_str());
        } else if (!HexToBinary(iv, hex_iv.get(), iv_length)) {
          OPENSSL_cleanse(key, sizeof(key));
          fprintf(stderr, "Error: Invalid hex IV value\n");
          return kToolExitFailure;
        }
      } else if (iv_length != 0) {
        fprintf(stderr, "Error: IV is required for cipher %s\n",
                cipher_name.c_str());
        OPENSSL_cleanse(key, sizeof(key));
        return kToolExitFailure;
      }
    } else if (has_passphrase) {
      const EVP_MD *md = EVP_get_digestbyname(md_name.c_str());
      if (!md) {
        fprintf(stderr, "Error: Unknown message digest '%s'\n",
                md_name.c_str());
        return kToolExitFailure;
      }

      bool use_salt = !nosalt;
      if (!hex_salt.empty()) {
        if (!HexToBinary(salt, hex_salt, SALT_SIZE)) {
          fprintf(stderr, "Error: Invalid hex salt value\n");
          return kToolExitFailure;
        }
        use_salt = true;
      } else if (use_salt) {
        if (encode) {
          RAND_bytes(salt, SALT_SIZE);
        } else {
          uint8_t salt_header[sizeof(kSaltMagic) + SALT_SIZE];
          if (fread(salt_header, 1, sizeof(salt_header), input) !=
              sizeof(salt_header)) {
            fprintf(stderr, "Error: failed to read salt header\n");
            return kToolExitFailure;
          }
          if (memcmp(salt_header, kSaltMagic, sizeof(kSaltMagic)) != 0) {
            fprintf(stderr, "Error: bad magic number\n");
            return kToolExitFailure;
          }
          memcpy(salt, salt_header + sizeof(kSaltMagic), SALT_SIZE);
        }
      }

      if (EVP_BytesToKey(cipher, md, use_salt ? salt : nullptr,
                         reinterpret_cast<const uint8_t *>(
                             passphrase.get().data()),
                         passphrase.get().size(), 1, key, iv) <= 0) {
        OPENSSL_cleanse(key, sizeof(key));
        fprintf(stderr, "Error: EVP_BytesToKey failed\n");
        return kToolExitFailure;
      }

      if (has_iv) {
        if (!HexToBinary(iv, hex_iv.get(), iv_length)) {
          OPENSSL_cleanse(key, sizeof(key));
          fprintf(stderr, "Error: Invalid hex IV value\n");
          return kToolExitFailure;
        }
      }

      if (encode && use_salt) {
        write_salt_header = true;
      }
    } else {
      fprintf(stderr,
              "Error: A raw key (-K) or passphrase (-kfile, -k, -pass) "
              "is required\n");
      return kToolExitFailure;
    }

    ctx.reset(EVP_CIPHER_CTX_new());
    const bool init_ok =
        ctx && EVP_CipherInit_ex(ctx.get(), cipher, nullptr, key, iv, encode);
    OPENSSL_cleanse(key, sizeof(key));
    if (!init_ok) {
      fprintf(stderr, "Error: Failed to initialize cipher\n");
      return kToolExitFailure;
    }
    if (nopad) {
      EVP_CIPHER_CTX_set_padding(ctx.get(), 0);
    }
  }

  bssl::UniquePtr<BIO> output_bio;
  if (out_path.empty() || out_path == "-") {
    output_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    output_bio.reset(BIO_new_file(out_path.c_str(), "wb"));
  }
  if (!output_bio) {
    fprintf(stderr, "Error: unable to write to '%s'\n", out_path.c_str());
    return kToolExitFailure;
  }

  if (write_salt_header) {
    if (!BIO_write_all(output_bio.get(), kSaltMagic, sizeof(kSaltMagic)) ||
        !BIO_write_all(output_bio.get(), salt, SALT_SIZE)) {
      fprintf(stderr, "Error: failed to write salt header\n");
      return kToolExitFailure;
    }
  }

  // Process the input file
  uint8_t inbuf[BUF_SIZE];
  uint8_t outbuf[BUF_SIZE + EVP_MAX_BLOCK_LENGTH];
  int inlen = 0, outlen = 0;

  for (;;) {
    if (feof(input)) {
      break;
    }

    inlen = fread(inbuf, 1, sizeof(inbuf), input);

    if (ferror(input)) {
      fprintf(stderr, "Error reading from '%s'.\n", in_path.c_str());
      return kToolExitFailure;
    }

    const uint8_t *output = inbuf;
    outlen = inlen;
    if (ctx) {
      if (!EVP_CipherUpdate(ctx.get(), outbuf, &outlen, inbuf, inlen)) {
        fprintf(stderr, "Error: Cipher update failed\n");
        return kToolExitFailure;
      }
      output = outbuf;
    }
    if (!BIO_write_all(output_bio.get(), output, outlen)) {
      fprintf(stderr, "Error: Error writing to '%s'\n", out_path.c_str());
      return kToolExitFailure;
    }
  }

  if (ctx) {
    if (!EVP_CipherFinal_ex(ctx.get(), outbuf, &outlen)) {
      fprintf(stderr, "Error: Cipher final failed\n");
      return kToolExitFailure;
    }
    if (!BIO_write_all(output_bio.get(), outbuf, outlen)) {
      fprintf(stderr, "Error: Error writing to '%s'\n", out_path.c_str());
      return kToolExitFailure;
    }
  }

  if (!BIO_flush(output_bio.get())) {
    fprintf(stderr, "Error: Error writing to '%s'\n", out_path.c_str());
    return kToolExitFailure;
  }

  return kToolExitSuccess;
}
