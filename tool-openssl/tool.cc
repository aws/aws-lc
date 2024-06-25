// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <string>
#include <vector>

#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/ssl.h>

#if defined(OPENSSL_WINDOWS)
#include <fcntl.h>
#include <io.h>
#else
#include <libgen.h>
#include <signal.h>
#endif

#include "../tool/internal.h"

extern bool X509Tool(const args_list_t &args);

typedef bool (*tool_func_t)(const std::vector<std::string> &args);

struct Tool {
  const char *name;
  tool_func_t func;
};

static const Tool kTools[] = {
  { "x509", X509Tool },
  { "", nullptr },
};

static void usage(const char *name) {
  printf("Usage: %s COMMAND\n", name);
  printf("\n");
  printf("Available commands:\n");

  for (size_t i = 0;; i++) {
    const Tool &tool = kTools[i];
    if (tool.func == nullptr) {
      break;
    }
    printf("    %s\n", tool.name);
  }
}

static tool_func_t FindTool(const std::string &name) {
  for (size_t i = 0;; i++) {
    const Tool &tool = kTools[i];
    if (tool.func == nullptr || name == tool.name) {
      return tool.func;
    }
  }
}

int main(int argc, char **argv) {
#if defined(OPENSSL_WINDOWS)
  // Read and write in binary mode. This makes bssl on Windows consistent with
  // bssl on other platforms, and also makes it consistent with MSYS's commands
  // like diff(1) and md5sum(1). This is especially important for the digest
  // commands.
  if (_setmode(_fileno(stdin), _O_BINARY) == -1) {
    perror("_setmode(_fileno(stdin), O_BINARY)");
    return 1;
  }
  if (_setmode(_fileno(stdout), _O_BINARY) == -1) {
    perror("_setmode(_fileno(stdout), O_BINARY)");
    return 1;
  }
  if (_setmode(_fileno(stderr), _O_BINARY) == -1) {
    perror("_setmode(_fileno(stderr), O_BINARY)");
    return 1;
  }
#else
  signal(SIGPIPE, SIG_IGN);
#endif

  CRYPTO_library_init();

  int starting_arg = 1;
  tool_func_t tool = nullptr;
#if !defined(OPENSSL_WINDOWS)
  tool = FindTool(basename(argv[0]));
#endif
  if (tool == nullptr) {
    starting_arg++;
    if (argc > 1) {
      tool = FindTool(argv[1]);
    }
  }
  if (tool == nullptr) {
    usage(argv[0]);
    return 1;
  }

  args_list_t args;
  for (int i = starting_arg; i < argc; i++) {
    args.push_back(argv[i]);
  }

  if (!tool(args)) {
    ERR_print_errors_fp(stderr);
    return 1;
  }

  return 0;
}
