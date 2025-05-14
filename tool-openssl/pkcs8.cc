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

// Maximum file size for cryptographic operations (1MB)
static constexpr long DEFAULT_MAX_CRYPTO_FILE_SIZE = 1024 * 1024;

// Maximum length for passwords
static constexpr size_t DEFAULT_MAX_SENSITIVE_STRING_LENGTH = 4096;

// Validate BIO size to prevent DoS from extremely large files
static bool validate_bio_size(BIO* bio, long max_size = DEFAULT_MAX_CRYPTO_FILE_SIZE) {
    if (!bio) return false;
    
    // Save current position
    const long current_pos = BIO_tell(bio);
    if (current_pos < 0) return false;
    
    // Get file size by seeking to end manually
    if (BIO_seek(bio, 0) < 0) return false;
    
    // Read through the file to determine size
    long size = 0;
    char buffer[4096];
    int bytes_read;
    
    while ((bytes_read = BIO_read(bio, buffer, sizeof(buffer))) > 0) {
        size += bytes_read;
        if (size > max_size) {
            // Restore position and return error
            BIO_seek(bio, current_pos);
            fprintf(stderr, "File exceeds maximum allowed size\n");
            return false;
        }
    }
    
    // Restore original position
    if (BIO_seek(bio, current_pos) < 0) return false;
    
    return true;
}

// Validation functions using literals
static bool validate_format(const std::string& format) {
    if (format != "PEM" && format != "DER") {
        fprintf(stderr, "Format must be PEM or DER\n");
        return false;
    }
    return true;
}

// Define a secure allowlist of ciphers
static const std::unordered_set<std::string> kSupportedCiphers = {
    "aes-128-cbc", "aes-192-cbc", "aes-256-cbc", 
    "des-ede3-cbc", // Triple DES
    "des-cbc"       // Single DES (not recommended for security-sensitive applications)
};

static bool validate_cipher(const std::string& cipher_name) {
    // Check if it's in our allowlist first
    if (kSupportedCiphers.find(cipher_name) == kSupportedCiphers.end()) {
        fprintf(stderr, "Unsupported cipher algorithm\n");
        return false;
    }
    
    // Then verify it can be initialized
    const EVP_CIPHER* cipher = EVP_get_cipherbyname(cipher_name.c_str());
    if (!cipher) {
        fprintf(stderr, "Cannot initialize cipher\n");
        return false;
    }
    
    return true;
}

static const std::unordered_set<std::string> kSupportedPRFs = {
    "hmacWithSHA1"  // Currently the only supported PRF in AWS-LC
};

static bool validate_prf(const std::string& prf_name) {
    if (kSupportedPRFs.find(prf_name) == kSupportedPRFs.end()) {
        fprintf(stderr, "Only hmacWithSHA1 PRF is supported\n");
        return false;
    }
    return true;
}

// Secure password handling - modified to update string in place
static bool extract_password(std::string& source) {
    if (source.empty()) {
        return true;
    }

    if (source.compare(0, 5, "pass:") == 0) {
        std::string password = source.substr(5);
        
        if (password.length() > DEFAULT_MAX_SENSITIVE_STRING_LENGTH) {
            fprintf(stderr, "Password exceeds maximum allowed length\n");
            return false;
        }
        
        source = password; // Replace source with just the password
        return true;
    }

    if (source.compare(0, 5, "file:") == 0) {
        std::string path = source.substr(5);
        bssl::UniquePtr<BIO> bio(BIO_new_file(path.c_str(), "r"));
        if (!bio) {
            fprintf(stderr, "Cannot open password file\n");
            return false;
        }

        char buf[DEFAULT_MAX_SENSITIVE_STRING_LENGTH];
        int len = BIO_gets(bio.get(), buf, sizeof(buf));
        if (len <= 0) {
            OPENSSL_cleanse(buf, sizeof(buf));
            fprintf(stderr, "Cannot read password file\n");
            return false;
        }
        
        // Check for potential truncation
        const bool possible_truncation = (static_cast<size_t>(len) == DEFAULT_MAX_SENSITIVE_STRING_LENGTH - 1 && 
                                        buf[len - 1] != '\n' && buf[len - 1] != '\r');
        if (possible_truncation) {
            OPENSSL_cleanse(buf, sizeof(buf));
            fprintf(stderr, "Password file content too long\n");
            return false;
        }
        
        // Remove trailing newline if present
        size_t buf_len = len;
        while (buf_len > 0 && (buf[buf_len-1] == '\n' || buf[buf_len-1] == '\r')) {
            buf[--buf_len] = '\0';
        }
        
        source = buf; // Replace source with contents from file
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
        
        // Create a new copy of the environment variable value
        source = std::string(env_val); // Replace source with environment variable value
        return true;
    }

    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return false;
}

// Secure password clearing
static void secure_clear(std::string& str) {
    if (!str.empty()) {
        OPENSSL_cleanse(&str[0], str.size());
        str.clear();
    }
}

// Comprehensive key reading function using library functions
static bssl::UniquePtr<EVP_PKEY> read_private_key(BIO* in_bio, const char* passin, 
                                                 const std::string& format) {
    if (!in_bio) return nullptr;
    
    bssl::UniquePtr<EVP_PKEY> pkey;
    
    if (format == "DER") {
        // First try as unencrypted PKCS8
        BIO_reset(in_bio);
        bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(d2i_PKCS8_PRIV_KEY_INFO_bio(in_bio, nullptr));
        if (p8inf) {
            pkey.reset(EVP_PKCS82PKEY(p8inf.get()));
            if (pkey) return pkey;
        }
        
        // Try as encrypted PKCS8 if password provided
        if (passin) {
            BIO_reset(in_bio);
            pkey.reset(d2i_PKCS8PrivateKey_bio(in_bio, nullptr, nullptr, const_cast<char*>(passin)));
            if (pkey) return pkey;
        }
        
        // Try as traditional format
        BIO_reset(in_bio);
        pkey.reset(d2i_PrivateKey_bio(in_bio, nullptr));
        if (pkey) return pkey;
    } else {
        // For PEM format input
        BIO_reset(in_bio);
        pkey.reset(PEM_read_bio_PrivateKey(in_bio, nullptr, nullptr, const_cast<char*>(passin)));
        if (pkey) return pkey;
    }
    
    return nullptr;
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
    {"", kOptionalArgument, ""}  // Terminator entry - must be the last one
};

bool pkcs8Tool(const args_list_t& args) {
    args_map_t parsed_args;
    args_list_t extra_args;
    if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments)) {
        PrintUsage(kArguments);
        return false;
    }

    bool help = false;
    GetBoolArgument(&help, "-help", parsed_args);
    if (help) {
        PrintUsage(kArguments);
        return true;
    }

    std::string in_path, out_path;
    GetString(&in_path, "-in", "", parsed_args);
    if (in_path.empty()) {
        fprintf(stderr, "Input file required\n");
        return false;
    }
    GetString(&out_path, "-out", "", parsed_args);

    std::string inform, outform;
    GetString(&inform, "-inform", "PEM", parsed_args);
    GetString(&outform, "-outform", "PEM", parsed_args);
    if (!validate_format(inform) || !validate_format(outform)) {
        return false;
    }

    bool topk8 = false, nocrypt = false;
    GetBoolArgument(&topk8, "-topk8", parsed_args);
    GetBoolArgument(&nocrypt, "-nocrypt", parsed_args);

    // Validate cipher and PRF directly from parsed_args
    if (parsed_args.count("-v2") > 0 && !parsed_args["-v2"].empty() && 
        !validate_cipher(parsed_args["-v2"])) {
        return false;
    }
    if (parsed_args.count("-v2prf") > 0 && !parsed_args["-v2prf"].empty() && 
        !validate_prf(parsed_args["-v2prf"])) {
        return false;
    }

    std::string passin_arg, passout_arg;
    GetString(&passin_arg, "-passin", "", parsed_args);
    GetString(&passout_arg, "-passout", "", parsed_args);
    
    if (!extract_password(passin_arg)) {
        return false;
    }
    if (!extract_password(passout_arg)) {
        secure_clear(passin_arg);
        return false;
    }

    bssl::UniquePtr<BIO> in(BIO_new_file(in_path.c_str(), "rb"));
    if (!in) {
        secure_clear(passin_arg);
        secure_clear(passout_arg);
        fprintf(stderr, "Cannot open input file\n");
        return false;
    }

    // Apply file size validation
    if (!validate_bio_size(in.get())) {
        secure_clear(passin_arg);
        secure_clear(passout_arg);
        return false;
    }

    bssl::UniquePtr<BIO> out;
    if (!out_path.empty()) {
        out.reset(BIO_new_file(out_path.c_str(), "wb"));
    } else {
        out.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
    }
    if (!out) {
        secure_clear(passin_arg);
        secure_clear(passout_arg);
        fprintf(stderr, "Cannot open output file\n");
        return false;
    }

    // Use enhanced key reading function with library support
    bssl::UniquePtr<EVP_PKEY> pkey = read_private_key(
        in.get(),
        passin_arg.empty() ? nullptr : passin_arg.c_str(),
        inform
    );

    if (!pkey) {
        secure_clear(passin_arg);
        secure_clear(passout_arg);
        fprintf(stderr, "Unable to load private key\n");
        return false;
    }

    bool success = false;
    if (!topk8) {
        // Traditional format output - no change here
        success = (outform == "PEM") ?
            PEM_write_bio_PrivateKey(out.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr) :
            i2d_PrivateKey_bio(out.get(), pkey.get());
    } else {
        if (nocrypt) {
            // Unencrypted PKCS8 output - no change here
            bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(EVP_PKEY2PKCS8(pkey.get()));
            if (!p8inf) {
                secure_clear(passin_arg);
                secure_clear(passout_arg);
                fprintf(stderr, "Error converting to PKCS#8\n");
                return false;
            }
            
            success = (outform == "PEM") ?
                PEM_write_bio_PKCS8_PRIV_KEY_INFO(out.get(), p8inf.get()) :
                i2d_PKCS8_PRIV_KEY_INFO_bio(out.get(), p8inf.get());
        } else {
            // Encrypted PKCS8 output - use library functions
            if (passout_arg.empty()) {
                secure_clear(passin_arg);
                fprintf(stderr, "Password required for encryption\n");
                return false;
            }

            // Get cipher directly from parsed_args
            const EVP_CIPHER* cipher = (parsed_args.count("-v2") == 0 || parsed_args["-v2"].empty()) ? 
                EVP_aes_256_cbc() : EVP_get_cipherbyname(parsed_args["-v2"].c_str());

            // Use library functions for encryption
            if (outform == "PEM") {
                success = PEM_write_bio_PKCS8PrivateKey(
                    out.get(), pkey.get(), cipher,
                    passout_arg.c_str(), passout_arg.length(),
                    nullptr, nullptr);
            } else {
                success = i2d_PKCS8PrivateKey_bio(
                    out.get(), pkey.get(), cipher,
                    passout_arg.c_str(), passout_arg.length(),
                    nullptr, nullptr);
            }
        }
    }

    secure_clear(passin_arg);
    secure_clear(passout_arg);

    if (!success) {
        fprintf(stderr, "Error writing private key\n");
        return false;
    }

    BIO_flush(out.get());
    return true;
}
