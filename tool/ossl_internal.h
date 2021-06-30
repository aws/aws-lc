#pragma once
#include <map>
#include <vector>
#include <string>
#include <memory>

// These values are DER encoded, RSA private keys.
extern const uint8_t kDERRSAPrivate2048[];
extern const size_t kDERRSAPrivate2048Len;
extern const uint8_t kDERRSAPrivate4096[];
extern const size_t kDERRSAPrivate4096Len;

bool Speed(const std::vector<std::string> &args);

#define BM_ARRAY_SIZE(array) (sizeof(array) / sizeof((array)[0]))

enum ArgumentType {
  kRequiredArgument,
  kOptionalArgument,
  kBooleanArgument
};

typedef struct argument_t {
  const char *name;
  ArgumentType type;
  const char *description;
} argument_t;

typedef std::vector<std::string> args_list_t;
typedef std::map<std::string, std::string> args_map_t;

// ParseKeyValueArguments converts the list of strings |args| ["-filter", "RSA", "-Timeout", "10"] into a map in
// |out_args| of key value pairs {"-filter": "RSA", "-Timeout": "10"}. It uses |templates| to determine what arguments
// are option or required.
bool ParseKeyValueArguments(args_map_t *out_args, const args_list_t &args, const argument_t *templates);

// PrintUsage prints the description from the list of templates in |templates| to stderr.
void PrintUsage(const argument_t *templates);

// GetUnsigned assigns |out| the value of |arg_name| from the map |args| if it is present. If |arg_name| is not found
// in |args| it assigns |out| to the |default_value|.
bool GetUnsigned(unsigned *out, const std::string &arg_name, unsigned default_value, const args_map_t &args);

bool Sign(const args_list_t &args);
bool ReadAll(std::vector<uint8_t> *out, FILE *in);
bool Server(const std::vector<std::string> &args);
bool Rand(const std::vector<std::string> &args);
bool Ciphers(const std::vector<std::string> &args);
bool Client(const std::vector<std::string> &args);


struct FileCloser {
  void operator()(FILE *file) {
    fclose(file);
  }
};

using ScopedFILE = std::unique_ptr<FILE, FileCloser>;
