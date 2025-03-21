// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/ssl.h>
#include <array>
#include <iostream>

#if defined(OPENSSL_WINDOWS)
#include <fcntl.h>
#include <io.h>
#else
#include <libgen.h>
#include <signal.h>
#endif

#include "./internal.h"

static const std::array<Tool, 10> kTools = {{
    {"crl", CRLTool},
    {"dgst", dgstTool},
    {"md5", md5Tool},
    {"rehash", RehashTool},
    {"req", reqTool},
    {"rsa", rsaTool},
    {"s_client", SClientTool},
    {"verify", VerifyTool},
    {"version", VersionTool},
    {"x509", X509Tool},
}};

static void usage(const std::string &name) {
  std::cout << "Usage: " << name << " COMMAND\n\n";
  std::cout << "Available commands:\n";

  for (const auto &tool : kTools) {
    if (tool.func == nullptr) {
      break;
    }
    std::cout << "    " << tool.name << "\n";
  }
}

static void initialize() {
#if defined(OPENSSL_WINDOWS)
  // Read and write in binary mode. This makes bssl on Windows consistent with
  // bssl on other platforms, and also makes it consistent with MSYS's commands
  // like diff(1) and md5sum(1). This is especially important for the digest
  // commands.
  if (_setmode(_fileno(stdin), _O_BINARY) == -1) {
    perror("_setmode(_fileno(stdin), O_BINARY)");
    exit(1);
  }
  if (_setmode(_fileno(stdout), _O_BINARY) == -1) {
    perror("_setmode(_fileno(stdout), O_BINARY)");
    exit(1);
  }
  if (_setmode(_fileno(stderr), _O_BINARY) == -1) {
    perror("_setmode(_fileno(stderr), O_BINARY)");
    exit(1);
  }
#else
  // Ignore SIGPIPE to prevent the process from terminating if it tries to
  // write to a pipe that has been closed by the reading end. SIGPIPE can be
  // received when writing to sockets or pipes that are no longer connected.
  signal(SIGPIPE, SIG_IGN);
#endif
}

tool_func_t FindTool(const std::string &name) {
  for (const auto &tool : kTools) {
    if (tool.name == name) {
      return tool.func;
    }
  }
  return nullptr;
}

tool_func_t FindTool(int argc, char **argv, int &starting_arg) {
#if !defined(OPENSSL_WINDOWS)
  tool_func_t tool = FindTool(basename(argv[0]));
  if (tool != nullptr) {
    return tool;
  }
#endif
  starting_arg++;
  if (argc > 1) {
    return FindTool(argv[1]);
  }
  return nullptr;
}

int main(int argc, char **argv) {
  initialize();
  CRYPTO_library_init();

  int starting_arg = 1;
  tool_func_t tool = FindTool(argc, argv, starting_arg);

  // Print help option menu.
  if (tool == nullptr) {
    usage(argv[0]);
    return 1;
  }

  args_list_t args;
  for (int i = starting_arg; i < argc; i++) {
    args.emplace_back(argv[i]);
  }

  if (!tool(args)) {
    ERR_print_errors_fp(stderr);
    return 1;
  }

  return 0;
}
