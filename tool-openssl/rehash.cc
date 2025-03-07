#include <regex>
#include <filesystem>
#include <dirent.h>
#include <unistd.h>
#include <stdio.h>
#include <limits.h>
#include <errno.h>
#include <string.h>
#include <ctype.h>
#include <sys/stat.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/x509.h>

#include "internal.h"

#ifndef PATH_MAX
#define PATH_MAX 4096
#endif
#ifndef NAME_MAX
#define NAME_MAX 255
#endif
#define MAX_COLLISIONS 256

#define NUM_ELEMENTS(x) (sizeof(x)/sizeof((x)[0]))

//typedef struct hentry_st {              // Represents a single certificate/CRL file
//    struct hentry_st *next;             // Links to next entry in same bucket
//    char *filename;                     // Actual filename
//    uint16_t old_id;                    // Previous numerical suffix if any
//    uint8_t need_symlink;               // Whether this entry needs a symbolic link
//    uint8_t digest[EVP_MAX_MD_SIZE];    // File's cryptographic digest
//} HENTRY;
//
//typedef struct bucket_st {      // Groups entries with same hash
//    struct bucket_st *next;     // Links to next bucket in hash table slot
//    HENTRY *first_entry;        // Start of entry list
//    HENTRY *last_entry;         // End of entry list
//    uint32_t hash;              // Hash value of the certificates/CRLs
//    uint16_t type;              // CERT or CRL
//    uint16_t num_needed;        // Count of entries needing symlinks
//} BUCKET;
//
//enum Type {
//    TYPE_CERT=0, TYPE_CRL=1
//};
//
//static int evpmdsize;
//static const EVP_MD *evpmd;
//static int remove_links = 1;
//static int verbose = 0;

// Each index may point to a list of |BUCKET|'s. Each |BUCKET| may point
// to a list of |HENTRY|'s.
// A new |BUCKET| is made when a
//static BUCKET *hash_table[257];
//
//static const char *suffixes[] = { "", "r" };
//static const char *extensions[] = { "pem", "crt", "cer", "crl" };

//// Utility functions for bit operations
//static void bit_set(uint8_t *set, uint32_t bit) {
//    set[bit >> 3] |= 1 << (bit & 0x7);
//}
//
//static int bit_isset(const uint8_t *set, uint32_t bit) {
//    return set[bit >> 3] & (1 << (bit & 0x7));
//}

// Add an entry to the hash table
//static int add_entry(enum Type type,        // CERT or CRL
//                    uint32_t hash,          // Hash of the name
//                    const char *filename,   // File to process
//                    const uint8_t *digest,  // File's digest
//                    int need_symlink,       // Whether symlink needed
//                    uint16_t old_id) {      // Previous ID if any
//
//    static BUCKET nilbucket;
//    static HENTRY nilhentry;
//    BUCKET *bucket;
//    HENTRY *entry, *found = NULL;
//    uint32_t hash_idx = (type + hash) % NUM_ELEMENTS(hash_table);
//
//    // Find an existing bucket if any for this |type| + |hash| combination at |hash_idx|
//    for (bucket = hash_table[hash_idx]; bucket; bucket = bucket->next) {
//        if (bucket->type == type && bucket->hash == hash) {
//            break;
//        }
//    }
//
//    // Create a new bucket at |hash_idx|
//    if (bucket == NULL) {
//        bucket = (BUCKET *)OPENSSL_malloc(sizeof(BUCKET));
//        *bucket = nilbucket;
//        // Store any previous bucket at the same index but with a different |type| + |hash| combination
//        bucket->next = hash_table[hash_idx];
//        bucket->type = type;
//        bucket->hash = hash;
//        hash_table[hash_idx] = bucket;
//    }
//
//    // Check for duplicates via fingerprint
//    for (entry = bucket->first_entry; entry; entry = entry->next) {
//        if (digest && memcmp(digest, entry->digest, evpmdsize) == 0) {
//            fprintf(stderr, "Warning: skipping duplicate %s in %s\n",
//                      type == TYPE_CERT ? "certificate" : "CRL", filename);
//            return 0;
//        }
//        if (strcmp(filename, entry->filename) == 0) {
//            found = entry;
//            if (digest == NULL) { break; }
//        }
//    }
//
//    // Create new entry if needed
//    if (found == NULL) {
//        if (bucket->num_needed >= MAX_COLLISIONS) {
//            fprintf(stderr, "Error: hash table overflow for %s\n", filename);
//            return 1;
//        }
//        entry = (HENTRY *)OPENSSL_malloc(sizeof(*entry));
//        *entry = nilhentry;
//        entry->old_id = ~0;
//        entry->filename = OPENSSL_strdup(filename);
//        if (bucket->last_entry)
//            bucket->last_entry->next = entry;
//        if (bucket->first_entry == NULL)
//            bucket->first_entry = entry;
//        bucket->last_entry = entry;
//    } else {
//        entry = found;
//    }
//
//    // Update entry
//    if (old_id < entry->old_id)
//        entry->old_id = old_id;
//    if (need_symlink && !entry->need_symlink) {
//        entry->need_symlink = 1;
//        bucket->num_needed++;
//        if (digest)
//            memcpy(entry->digest, digest, evpmdsize);
//    }
//    return 0;
//}

// returns one for all reasons such as not having a valid extension, or not being able to add to hashtable, and zero for error.
static int process_file(std::string filename, std::string fullpath) {

  return 1;
}

// symlink_check determines if |filename| is a symbolic link matching the regex [0-9a-f]{8}.([r])?[0-9]+.
// If so, it deletes the symbolic link and sets |is_symlink| to true.
// It returns one on success, and zero on failure.
static int symlink_check(std::string filename, std::string fullpath, const std::regex &pattern, bool &is_symlink) {
    struct stat path_stat;

    if (lstat(fullpath.c_str(), &path_stat) != 0) {
      fprintf(stderr, "Error: Cannot stat '%s': %s\n", fullpath.c_str(), strerror(errno));
      return 0;
    }

    // If it's a symlink and matches our pattern, remove it
    if (S_ISLNK(path_stat.st_mode) && std::regex_match(filename, pattern)) {
      if (unlink(fullpath.c_str()) != 0) {
        fprintf(stderr, "Error: Failed to remove symlink '%s': %s\n", fullpath.c_str(), strerror(errno));
        return 0;
      }
      is_symlink = true;
    }
    
    return 1;
}

static int process_directory(std::string directory_path) {
  // MAYBE COUPLE THE FILE PROCESSING. SO in one pass we idenitfy and remove any symlinks, and otherwise
  // we process an appropriate file and at least store the info in the hashtable. Then we can create them all at once.

  DIR* dir = opendir(directory_path.c_str());
  if (dir == nullptr) {
    fprintf(stderr, "Error opening directory '%s': %s\n", directory_path.c_str(), strerror(errno));
    return 0;
  }

  // Process every file. Remove any symlinks matching the regex.
  // Otherwise, process the file and store its info in the hashtable.
  struct dirent* entry;
  const std::regex symlink_pattern("[0-9a-f]{8}\\.(?:r)?[0-9]+");
  while ((entry = readdir(dir)) != nullptr) {
    std::string filename(entry->d_name);

    // Skip hidden files
    if (filename == "." || filename == "..") {
      continue;
    }
    std::string full_path = directory_path + "/" + filename;

    // Check if it's a symlink matching the regex
    bool is_symlink = false;
    if (!symlink_check(filename.c_str(), full_path.c_str(), symlink_pattern, is_symlink)) {
        return 0;
    }
    if (is_symlink) {
      continue;
    }

    // If its a valid file, add a symlink mapping to hashtable
    if (!process_file(full_path.c_str(), filename.c_str())) {
      return 0;
    }


  }

  // Pass 2: Process generated hash table to create new symlinks.

  closedir(dir);
  return 1;
}

static const argument_t kArguments[] = {
        { "-help", kBooleanArgument, "Usage: openssl rehash [cert-directory]\n" \
                                     "This tool scans a directory and calculates a hash value of each \n" \
                                     ".pem, .crt, .cer, or .crl file. It then creates a symbolic link for each file, \n"\
                                     "where the name of the link is the hash value. The symlink follows the format \n" \
                                     "HHHHHHHH.D, where each H is a hexadecimal character and D is a whole number. \n" \
                                     "This tool also removes any existing symbolic links that match the regex \n" \
                                     "[0-9a-f]{8}.([r])?[0-9]+ in that directory. \n" \
                                     "If any directory is not named on the command line, then the SSL_CERT_DIR \n"
                                     "environmental variable will be consulted. If that is not set, then the default \n"\
                                     "directory will be used. \n" },
        { "", kOptionalArgument, "Path to directory. If not provided, the default directory will be used." },
        { "", kOptionalArgument, "" }
};

bool RehashTool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments) || extra_args.size() > 1) {
    PrintUsage(kArguments);
    return false;
  }

  std::string directory_path;
  bool help = false;

  GetBoolArgument(&help, "-help", parsed_args);

  if (help) {
    fprintf(stderr, "Usage: openssl rehash [cert-directory]\n" \
                    "This tool scans a directory and calculates a hash value of each \n" \
                    ".pem, .crt, .cer, or .crl file. It then creates a symbolic link for each file, \n"\
                    "where the name of the link is the hash value. The symlink follows the format \n" \
                    "HHHHHHHH.D, where each H is a hexadecimal character and D is a whole number. \n" \
                    "This tool also removes any existing symbolic links that match the regex \n" \
                    "[0-9a-f]{8}.([r])?[0-9]+ in that directory. \n" \
                    "If any directory is not named on the command line, then the SSL_CERT_DIR \n"
                    "environmental variable will be consulted. If that is not set, then the default \n"\
                    "directory will be used. You must have write access to the directory. \n");
    PrintUsage(kArguments);
    return false;
  }

  if (extra_args.size() == 0) { // No directory path provided on command line
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
    fprintf(stderr, "Error: Unable to resolve directory path: %s\n", strerror(errno));
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

  // Process directory
  if (!process_directory(directory_path)) {
    fprintf(stderr, "Error: Unable while processing directory '%s'\n", directory_path.c_str());
    return false;
  }

  return true;
}
