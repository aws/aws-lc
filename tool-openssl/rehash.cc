// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"
#include "../tool/internal.h"

#if !defined(OPENSSL_WINDOWS)
#include <regex.h>
#include <dirent.h>
#include <unistd.h>
#include <limits.h>
#include <errno.h>
#include <string.h>
#include <sys/stat.h>
#include <openssl/pem.h>
#include <openssl/x509.h>

#include "../crypto/internal.h"

#define MAX_BUCKET_ENTRIES 256

static const std::vector<std::string> valid_extensions = {".pem", ".crt",
                                                          ".cer", ".crl"};

// status_flag tracks if any errors were encountered during processing of the
// directory. Some errors are not fatal, therefore this flag tracks if we have
// encountered any errors to return at the end of processing.
// OpenSSL has slightly different behavior, they return the total # of errors
// encountered. We do not need this functionality, however, it should be easy
// to use this variable as a counter instead of a flag.
static bool status_flag = true;

// Each index may point to a list of |BUCKET|'s. Each |BUCKET| may point
// to a list of |HASH_ENTRY|'s.
// A |BUCKET| list may be created at an index when a collision occurs for a
// type + hash combo that does not already exist at that index. A |HASH_ENTRY|
// list may be created when the bucket for a type + hash combo has one
// or more |HASH_ENTRY|'s and the cert/crl doesn't already exist in the table.
// This table is initialized and processed in |process_directory|.
static BUCKET *hash_table[257];

static const size_t HASH_TABLE_SIZE = OPENSSL_ARRAY_SIZE(hash_table);
static size_t evpmdsize = EVP_MD_size(EVP_sha1());

BUCKET** get_table() {
  return hash_table;
}

// add_entry creates a mapping for |filename| in |hash_table|
void add_entry(enum Type type, uint32_t hash, const char *filename,
                     const uint8_t *digest) {
  BUCKET *bucket;
  HASH_ENTRY *entry = NULL;
  uint32_t hash_idx = (type + hash) % HASH_TABLE_SIZE;

  // Find an existing bucket if any for this |type| + |hash| combination at
  // |hash_idx|
  for (bucket = hash_table[hash_idx]; bucket; bucket = bucket->next) {
    if (bucket->type == type && bucket->hash == hash) {
      break;
    }
  }

  // If not found, create a new bucket at |hash_idx|
  if (bucket == NULL) {
    bucket = (BUCKET *)OPENSSL_zalloc(sizeof(*bucket));
    if (bucket == NULL) {
      fprintf(stderr, "ERROR: Failed to allocate new bucket\n");
      return;
    }
    // Insert new bucket as head of linked-list
    bucket->next = hash_table[hash_idx];
    bucket->type = type;
    bucket->hash = hash;
    hash_table[hash_idx] = bucket;
  }

  // Check for duplicates via fingerprint
  for (entry = bucket->first_entry; entry; entry = entry->next) {
    if (digest && OPENSSL_memcmp(digest, entry->digest, evpmdsize) == 0) {
      fprintf(stderr, "Warning: skipping duplicate %s in %s\n",
              type == TYPE_CERT ? "certificate" : "CRL", filename);
      return;
    }
  }

  // Create new entry
  if (bucket->num_entries >= MAX_BUCKET_ENTRIES) {
    fprintf(stderr, "Error: hash table overflow for %s\n", filename);
    status_flag = false;
    return;
  }

  entry = (HASH_ENTRY *)OPENSSL_zalloc(sizeof(*entry));
  if (entry == NULL) {
    fprintf(stderr, "ERROR: Failed to allocate new entry\n");
    return;
  }

  entry->filename = OPENSSL_strdup(filename);
  if (entry->filename == NULL) {
    fprintf(stderr, "ERROR: Failed to duplicate filename\n");
    OPENSSL_free(entry);
    return;
  }

  OPENSSL_memcpy(entry->digest, digest, evpmdsize);
  if (bucket->last_entry)
    bucket->last_entry->next = entry;
  if (bucket->first_entry == NULL)
    bucket->first_entry = entry;
  bucket->last_entry = entry;
  bucket->num_entries++;
}

// process_file checks if |filename| is valid and creates a mapping in
// |hash_table|
static void process_file(const std::string &filename,
                         const std::string &fullpath) {
  // Skip files with invalid extensions
  size_t dot_pos = filename.find_last_of('.');
  if (dot_pos == std::string::npos ||
    std::none_of(valid_extensions.begin(), valid_extensions.end(),
                [&filename, dot_pos](const std::string& ext) {
                    return strcasecmp(filename.c_str() + dot_pos, ext.c_str()) == 0;
                  })) {
    return;
  }

  // Ensure file contains X.509 data
  BIO* bio = BIO_new_file(fullpath.c_str(), "r");
  if (!bio) {
    fprintf(stderr, "Error: Cannot open file %s\n", filename.c_str());
    status_flag = false;
    return;
  }

  bssl::UniquePtr<STACK_OF(X509_INFO)> x509_info_stack(
    PEM_X509_INFO_read_bio(bio, nullptr, nullptr, nullptr));
  BIO_free(bio);

  // Ensure there is only one cert/CRL in the file, this is not an error
  if (!x509_info_stack) {
    fprintf(stderr, "Warning: Failed to parse file %s\n", filename.c_str());
    return;
  }

  if (sk_X509_INFO_num(x509_info_stack.get()) != 1) {
    fprintf(stderr, "Warning: Skipping %s as it does not contain exactly one "
                    "certificate or CRL\n", filename.c_str());
    return;
  }

  // Process single cert/CRL
  X509_INFO* x509_info = sk_X509_INFO_value(x509_info_stack.get(), 0);
  X509_NAME* x509_name;
  unsigned char digest[EVP_MAX_MD_SIZE];
  unsigned int digest_len;
  Type type;

  if (x509_info->x509) {
    // Handle certificate
    type = TYPE_CERT;
    if (!X509_digest(x509_info->x509, EVP_sha1(), digest, &digest_len)) {
      fprintf(stderr, "Error: Failed to generate digest for %s\n", filename.c_str());
      status_flag = false;
      return;
    }
    x509_name = X509_get_subject_name(x509_info->x509);

  } else if (x509_info->crl) {
    // Handle CRL
    type = TYPE_CRL;
    if (!X509_CRL_digest(x509_info->crl, EVP_sha1(), digest, &digest_len)) {
      fprintf(stderr, "Error: Failed to generate digest for %s\n", filename.c_str());
      status_flag = false;
      return;
    }
    x509_name = X509_CRL_get_issuer(x509_info->crl);
  } else {
    fprintf(stderr, "Error: No certificate or CRL found in %s\n", filename.c_str());
    status_flag = false;
    return;
  }

  add_entry(type, X509_NAME_hash(x509_name), filename.c_str(), digest);
}

// symlink_check determines if |filename| is a symbolic link matching the regex
// [0-9a-f]{8}.([r])?[0-9]+.
// If so, it deletes the symbolic link and sets |is_symlink| to true.
static void symlink_check(const std::string &filename, const std::string &fullpath,
                          bool &is_symlink, regex_t &regex) {
  struct stat path_stat;

  if (lstat(fullpath.c_str(), &path_stat) != 0) {
    fprintf(stderr, "Warning: Cannot stat '%s': %s\n", fullpath.c_str(), strerror(errno));
    status_flag = false;
    return;
  }

  // If it's a symlink and matches our pattern, remove it
  if (S_ISLNK(path_stat.st_mode)) {
    int ret = regexec(&regex, filename.c_str(), 0, NULL, 0);
    if (ret == 0) { // regex matched
      if (unlink(fullpath.c_str()) != 0) {
        fprintf(stderr, "Warning: Failed to remove symlink '%s': %s\n",
          fullpath.c_str(), strerror(errno));
        status_flag = false;
        return;
      }
    }
    is_symlink = true;
  }
}

static void generate_symlinks(const std::string &directory_path) {
  char prev_dir[PATH_MAX];
  if (getcwd(prev_dir, sizeof(prev_dir)) == NULL) {
    fprintf(stderr, "Error getting current directory: %s\n", strerror(errno));
    status_flag = false;
    return;
  }

  // Change to target directory
  if (chdir(directory_path.c_str()) != 0) {
    fprintf(stderr, "Warning: Error changing to directory %s: %s\n",
            directory_path.c_str(), strerror(errno));
    status_flag = false;
    return;
  }

  for (size_t i = 0; i < HASH_TABLE_SIZE; i++) {
    for (BUCKET* bucket = hash_table[i]; bucket; bucket = bucket->next) {
      // A given type + hash combo can only exist in one bucket. Therefore,
      // a counter per bucket is enough to determine suffix
      int count = 0;

      for (HASH_ENTRY* entry = bucket->first_entry; entry; entry = entry->next) {
        char link_name[PATH_MAX];

        // Format: <hash>.<count> for certs, <hash>.r<count> for CRLs
        if (bucket->type == TYPE_CERT) {
          snprintf(link_name, sizeof(link_name), "%08x.%d",
            bucket->hash, count);
        } else {  // TYPE_CRL
          snprintf(link_name, sizeof(link_name), "%08x.r%d",
            bucket->hash, count);
        }
        count++;

        if (symlink(entry->filename, link_name) != 0) {
          fprintf(stderr, "Warning: Error creating symlink '%s': %s\n",
                  link_name, strerror(errno));
          status_flag = false;
        }
      }
    }
  }

  if (chdir(prev_dir) != 0) {
    fprintf(stderr, "Warning: Error returning to original directory: %s\n",
            strerror(errno));
    status_flag = false;
  }
}

static void process_directory(const std::string &directory_path, regex_t &regex) {
  DIR* dir = opendir(directory_path.c_str());
  if (dir == nullptr) {
    fprintf(stderr, "Error opening directory '%s': %s\n",
      directory_path.c_str(), strerror(errno));
    status_flag = false;
    return;
  }
  OPENSSL_memset(hash_table, 0, sizeof(hash_table));

  // Process every file. Remove any symlinks matching the regex and create
  // mappings in the hashtable for any valid files.
  struct dirent* entry;
  while ((entry = readdir(dir)) != nullptr) {
    std::string filename(entry->d_name);

    // Skip hidden files
    if (filename == "." || filename == "..") {
      continue;
    }
    std::string full_path = directory_path + "/" + filename;

    // Check if it's a symlink matching the regex, continue processing even with
    // errors.
    bool is_symlink = false;
    symlink_check(filename, full_path, is_symlink, regex);
    if (is_symlink) {
      continue;
    }

    // If it's a valid file, add a mapping to hashtable. Continue
    // processing even if we encounter errors.
    process_file(filename, full_path);
  }

  // Pass 2: Process hash table to create symlinks.
  generate_symlinks(directory_path);
  closedir(dir);
}

void cleanup_hash_table() {
  for (size_t i = 0; i < HASH_TABLE_SIZE; i++) {
    BUCKET* current_bucket = hash_table[i];
    while (current_bucket) {
      HASH_ENTRY* current_entry = current_bucket->first_entry;
      while (current_entry) {
        HASH_ENTRY* next_entry = current_entry->next;
        OPENSSL_free(current_entry->filename);
        OPENSSL_free(current_entry);
        current_entry = next_entry;
      }
      BUCKET* next_bucket = current_bucket->next;
      OPENSSL_free(current_bucket);
      current_bucket = next_bucket;
    }

    hash_table[i] = nullptr;
  }
}

static const argument_t kArguments[] = {
        { "-help", kBooleanArgument, "Display option summary"},
        { "", kOptionalArgument, "Path to directory. "\
                    "then the SSL_CERT_DIR environmental variable will be \n" \
                    "consulted. If that is not set, then the default \n" \
                    "directory will be used. You must have write \n"\
                    "access to the directory." },
        { "", kOptionalArgument, "" }
};

bool RehashTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args,
    kArguments) || extra_args.size() > 1) {
    PrintUsage(kArguments);
    return false;
  }

  std::string directory_path;
  bool help = false;

  GetBoolArgument(&help, "-help", parsed_args);

  if (help) {
    fprintf(stderr, "Usage: openssl rehash [cert-directory]\n" \
      "This tool scans a directory and calculates a hash value of each \n" \
      "pem, .crt, .cer, or .crl file. It then creates a symbolic link \n"\
      "for each file, where the name of the link is the hash value. The \n" \
      "symlink follows the format HHHHHHHH.D, where each H is a \n" \
      "hexadecimal character and D is a whole number. This tool also \n" \
      "removes any existing symbolic links that match the regex \n" \
      "[0-9a-f]{8}.([r])?[0-9]+ in that directory. \n");
    PrintUsage(kArguments);
    return true;
  }

  if (extra_args.empty()) { // No directory path provided on command line
    const char* ssl_cert_dir = getenv("SSL_CERT_DIR");
    if (ssl_cert_dir != nullptr) {
      directory_path = ssl_cert_dir;
    } else {
      directory_path = X509_get_default_cert_dir();
    }
  } else {
    directory_path = extra_args[0];
  }

  // Get absolute path
  char resolved_path[PATH_MAX];
  if (realpath(directory_path.c_str(), resolved_path) == nullptr) {
    fprintf(stderr, "Error: Unable to resolve directory path: %s\n",
            strerror(errno));
    return false;
  }
  directory_path = resolved_path;

  // Verify that the path exists and is a directory
  struct stat path_stat;
  if (stat(directory_path.c_str(), &path_stat) != 0) {
    fprintf(stderr, "Error: Cannot access directory '%s': %s\n",
            directory_path.c_str(), strerror(errno));
    return false;
  }
  if (!S_ISDIR(path_stat.st_mode)) {
    fprintf(stderr, "Error: '%s' is not a directory\n",
            directory_path.c_str());
    return false;
  }

  // Verify write access to directory
  if (access(directory_path.c_str(), W_OK) != 0) {
    fprintf(stderr, "Error: Don't have write permission for '%s'\n",
            directory_path.c_str());
    return false;
  }

  regex_t regex;
  int ret = regcomp(&regex, "^[0-9a-fA-F]{8}\\.([r])?[0-9]+$", REG_EXTENDED | REG_NOSUB);
  if (ret) {
    regfree(&regex);
    fprintf(stderr, "Could not compile regex\n");
    return false;
  }
  // Process directory
  process_directory(directory_path, regex);

  regfree(&regex);
  cleanup_hash_table();

  return status_flag;
}

#else
#include <stdio.h>
#include <stdbool.h>

bool RehashTool(const args_list_t &args) {
  fprintf(stderr, "RehashTool: Not implemented for windows\n");
  return false;
}
#endif
