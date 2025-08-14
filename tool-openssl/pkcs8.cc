// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/evp.h>
#include <openssl/pkcs8.h>
#include <openssl/pem.h>
#include <openssl/err.h>
#include <openssl/bytestring.h>
#include <string>
#include <unordered_set>
#include <cstring>
#include "internal.h"

// Maximum size for crypto files to prevent loading excessively large files (1MB)
static constexpr long DEFAULT_MAX_CRYPTO_FILE_SIZE = 1024 * 1024;

// Maximum length limit for sensitive strings like passwords (4KB)
static constexpr size_t DEFAULT_MAX_SENSITIVE_STRING_LENGTH = 4096;

// Checks if BIO size is within allowed limits
static bool validate_bio_size(BIO* bio, long max_size = DEFAULT_MAX_CRYPTO_FILE_SIZE) {
    if (!bio) {
        return false;
    }
    const long current_pos = BIO_tell(bio);
    if (current_pos < 0) {
        return false;
    }
    if (BIO_seek(bio, 0) < 0) {
        return false;
    }
    long size = 0;
    char buffer[4096] = {};
    int bytes_read = 0;
    while ((bytes_read = BIO_read(bio, buffer, sizeof(buffer))) > 0) {
        size += bytes_read;
        if (size > max_size) {
            BIO_seek(bio, current_pos);
            fprintf(stderr, "File exceeds maximum allowed size\n");
            return false;
        }
    }
    if (BIO_seek(bio, current_pos) < 0) {
        return false;
    }
    return true;
}

// Validates input/output format is PEM or DER
static bool validate_format(const std::string& format) {
    if (format != "PEM" && format != "DER") {
        fprintf(stderr, "Format must be PEM or DER\n");
        return false;
    }
    return true;
}

// Supported cipher algorithms for key encryption
static const std::unordered_set<std::string> kSupportedCiphers = {
    "aes-128-cbc", "aes-192-cbc", "aes-256-cbc", 
    "des-ede3-cbc", 
    "des-cbc"      
};

// Checks if the cipher name is supported and can be initialized
static bool validate_cipher(const std::string& cipher_name) {
    if (kSupportedCiphers.find(cipher_name) == kSupportedCiphers.end()) {
        fprintf(stderr, "Unsupported cipher algorithm\n");
        return false;
    }
    const EVP_CIPHER* cipher = EVP_get_cipherbyname(cipher_name.c_str());
    if (!cipher) {
        fprintf(stderr, "Cannot initialize cipher\n");
        return false;
    }
    
    return true;
}

// Supported PRF algorithms for PKCS#5 v2.0
static const std::unordered_set<std::string> kSupportedPRFs = {
    "hmacWithSHA1"  // Currently the only supported PRF in AWS-LC
};

// Checks if the PRF algorithm name is supported
static bool validate_prf(const std::string& prf_name) {
    if (kSupportedPRFs.find(prf_name) == kSupportedPRFs.end()) {
        fprintf(stderr, "Only hmacWithSHA1 PRF is supported\n");
        return false;
    }
    return true;
}

// Extracts password from various sources (direct input, file, environment)
// Updates source string to contain the actual password
static bool extract_password(std::string& source) {
    // TODO Prompt user for password via EVP_read_pw_string 
    if (source.empty()) {
        return true;
    }

    if (source.compare(0, 5, "pass:") == 0) {
        std::string password = source.substr(5); 
        if (password.length() > DEFAULT_MAX_SENSITIVE_STRING_LENGTH) {
            fprintf(stderr, "Password exceeds maximum allowed length\n");
            return false;
        }
        source = password;
        return true;
    }

    if (source.compare(0, 5, "file:") == 0) {
        std::string path = source.substr(5);
        bssl::UniquePtr<BIO> bio(BIO_new_file(path.c_str(), "r"));
        if (!bio) {
            fprintf(stderr, "Cannot open password file\n");
            return false;
        }
        char buf[DEFAULT_MAX_SENSITIVE_STRING_LENGTH] = {};
        int len = BIO_gets(bio.get(), buf, sizeof(buf));
        if (len <= 0) {
            OPENSSL_cleanse(buf, sizeof(buf));
            fprintf(stderr, "Cannot read password file\n");
            return false;
        }
        const bool possible_truncation = (static_cast<size_t>(len) == DEFAULT_MAX_SENSITIVE_STRING_LENGTH - 1 && 
                                        buf[len - 1] != '\n' && buf[len - 1] != '\r');
        if (possible_truncation) {
            OPENSSL_cleanse(buf, sizeof(buf));
            fprintf(stderr, "Password file content too long\n");
            return false;
        }
        size_t buf_len = len;
        while (buf_len > 0 && (buf[buf_len-1] == '\n' || buf[buf_len-1] == '\r')) {
            buf[--buf_len] = '\0';
        }
        source = buf; 
        OPENSSL_cleanse(buf, sizeof(buf));
        return true;
    }

    if (source.compare(0, 4, "env:") == 0) {
        std::string env_var = source.substr(4);
        if (env_var.empty()) {
            fprintf(stderr, "Empty environment variable name\n");
            return false;
        }
        const char* env_val = getenv(env_var.c_str());
        if (!env_val) {
            fprintf(stderr, "Environment variable '%s' not set\n", env_var.c_str());
            return false;
        }
        size_t env_val_len = strlen(env_val);
        if (env_val_len == 0) {
            fprintf(stderr, "Environment variable '%s' is empty\n", env_var.c_str());
            return false;
        }
        if (env_val_len > DEFAULT_MAX_SENSITIVE_STRING_LENGTH) {
            fprintf(stderr, "Environment variable value too long\n");
            return false;
        }
        source = std::string(env_val);
        return true;
    }
    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return false;
}

// Custom deleter for sensitive strings that clears memory before deletion
static void SensitiveStringDeleter(std::string* str) {
    if (str && !str->empty()) {
        OPENSSL_cleanse(&(*str)[0], str->size());
        str->clear();
    }
    delete str;
}

BSSL_NAMESPACE_BEGIN
BORINGSSL_MAKE_DELETER(std::string, SensitiveStringDeleter)
BSSL_NAMESPACE_END

// Reads a private key from BIO in the specified format with optional password
static bssl::UniquePtr<EVP_PKEY> read_private_key(BIO* in_bio, const char* passin, 
                                                 const std::string& format) {
    if (!in_bio) {
        return nullptr;
    }
    
    bssl::UniquePtr<EVP_PKEY> pkey;

    if (passin) {
        if (format == "DER") {
            BIO_reset(in_bio);
            pkey.reset(d2i_PKCS8PrivateKey_bio(in_bio, nullptr, nullptr, const_cast<char*>(passin)));
            return pkey;
        } else {
            BIO_reset(in_bio);
            pkey.reset(PEM_read_bio_PrivateKey(in_bio, nullptr, nullptr, const_cast<char*>(passin)));
            return pkey;
        }
    }
    
    // If no password provided, try unencrypted paths
    if (format == "DER") {
        BIO_reset(in_bio);
        bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(d2i_PKCS8_PRIV_KEY_INFO_bio(in_bio, nullptr));
        if (p8inf) {
            pkey.reset(EVP_PKCS82PKEY(p8inf.get()));
            if (pkey) {
                return pkey;
            }
        }
        BIO_reset(in_bio);
        pkey.reset(d2i_PrivateKey_bio(in_bio, nullptr));
        return pkey;
    } else {
        BIO_reset(in_bio);
        pkey.reset(PEM_read_bio_PrivateKey(in_bio, nullptr, nullptr, nullptr));
        return pkey;
    }
}

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-in", kOptionalArgument, "Input file"},
    {"-out", kOptionalArgument, "Output file"},
    {"-inform", kOptionalArgument, "Input format (DER or PEM)"},
    {"-outform", kOptionalArgument, "Output format (DER or PEM)"},
    {"-topk8", kBooleanArgument, "Convert traditional format to PKCS#8"},
    {"-nocrypt", kBooleanArgument, "Use unencrypted private key"},
    {"-v2", kOptionalArgument, "Use PKCS#5 v2.0 and specified cipher"},
    {"-v2prf", kOptionalArgument, "Use specified PRF algorithm with PKCS#5 v2.0"},
    {"-passin", kOptionalArgument, "Input file passphrase source"},
    {"-passout", kOptionalArgument, "Output file passphrase source"},
    {"", kOptionalArgument, ""}
};

bool pkcs8Tool(const args_list_t& args) {
    using namespace ordered_args;
    ordered_args_map_t parsed_args;
    args_list_t extra_args;
    bool help = false;
    std::string in_path, out_path;
    std::string inform = "PEM", outform = "PEM";
    bool topk8 = false, nocrypt = false;
    
    // Sensitive strings will be automatically cleared on function exit
    bssl::UniquePtr<std::string> passin_arg(new std::string());
    bssl::UniquePtr<std::string> passout_arg(new std::string());
    
    bssl::UniquePtr<BIO> in;
    bssl::UniquePtr<BIO> out;
    bssl::UniquePtr<EVP_PKEY> pkey;
    const EVP_CIPHER* cipher = nullptr;
    bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf;
    
    if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args, kArguments)) {
        PrintUsage(kArguments);
        return false;
    }

    GetBoolArgument(&help, "-help", parsed_args);
    if (help) {
        PrintUsage(kArguments);
        return true;
    }

    GetString(&in_path, "-in", "", parsed_args);
    if (in_path.empty()) {
        fprintf(stderr, "Input file required\n");
        return false;
    }
    GetString(&out_path, "-out", "", parsed_args);

    GetString(&inform, "-inform", "PEM", parsed_args);
    GetString(&outform, "-outform", "PEM", parsed_args);
    if (!validate_format(inform) || !validate_format(outform)) {
        return false;
    }

    GetBoolArgument(&topk8, "-topk8", parsed_args);
    GetBoolArgument(&nocrypt, "-nocrypt", parsed_args);

    std::string v2_cipher;
    GetString(&v2_cipher, "-v2", "", parsed_args);
    if (!v2_cipher.empty() && !validate_cipher(v2_cipher)) {
        return false;
    }

    std::string v2_prf;
    GetString(&v2_prf, "-v2prf", "", parsed_args);
    if (!v2_prf.empty() && !validate_prf(v2_prf)) {
        return false;
    }
    
    GetString(passin_arg.get(), "-passin", "", parsed_args);
    GetString(passout_arg.get(), "-passout", "", parsed_args);
    if (!extract_password(*passin_arg)) {
        return false;
    }
    if (!extract_password(*passout_arg)) {
        return false;
    }
    
    // Check for contradictory arguments
    if (nocrypt && !passin_arg->empty() && !passout_arg->empty()) {
        fprintf(stderr, "Error: -nocrypt cannot be used with both -passin and -passout\n");
        return false;
    }
    
    in.reset(BIO_new_file(in_path.c_str(), "rb"));
    if (!in) {
        fprintf(stderr, "Cannot open input file\n");
        return false;
    }
    if (!validate_bio_size(in.get())) {
        return false;
    }
    
    if (!out_path.empty()) {
        out.reset(BIO_new_file(out_path.c_str(), "wb"));
    } else {
        out.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
    }
    if (!out) {
        fprintf(stderr, "Cannot open output file\n");
        return false;
    }
    
    pkey = read_private_key(
        in.get(),
        passin_arg->empty() ? nullptr : passin_arg->c_str(),
        inform
    );
    if (!pkey) {
        fprintf(stderr, "Unable to load private key\n");
        return false;
    }

    bool result = false;
    if (!topk8) {
        result = (outform == "PEM") ?
            PEM_write_bio_PrivateKey(out.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr) :
            i2d_PrivateKey_bio(out.get(), pkey.get());
    } else {
        // If passout is provided, always encrypt the output regardless of nocrypt
        if (nocrypt && passout_arg->empty()) {
            p8inf.reset(EVP_PKEY2PKCS8(pkey.get()));
            if (!p8inf) {
                fprintf(stderr, "Error converting to PKCS#8\n");
                return false;
            }
            
            result = (outform == "PEM") ?
                PEM_write_bio_PKCS8_PRIV_KEY_INFO(out.get(), p8inf.get()) :
                i2d_PKCS8_PRIV_KEY_INFO_bio(out.get(), p8inf.get());
        } else {
            if (passout_arg->empty()) {
                fprintf(stderr, "Password required for encryption\n");
                return false;
            }
            cipher = v2_cipher.empty() ? 
                EVP_aes_256_cbc() : EVP_get_cipherbyname(v2_cipher.c_str());
            if (outform == "PEM") {
                result = PEM_write_bio_PKCS8PrivateKey(
                    out.get(), pkey.get(), cipher,
                    passout_arg->c_str(), passout_arg->length(),
                    nullptr, nullptr);
            } else {
                result = i2d_PKCS8PrivateKey_bio(
                    out.get(), pkey.get(), cipher,
                    passout_arg->c_str(), passout_arg->length(),
                    nullptr, nullptr);
            }
        }
    }

    if (!result) {
        fprintf(stderr, "Error writing private key\n");
        return false;
    }

    BIO_flush(out.get());
    return true;
}
