// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "internal.h"

namespace ordered_args {

bool ParseOrderedKeyValueArguments(ordered_args_map_t &out_args,
                                   args_list_t &extra_args,
                                   const args_list_t &args,
                                   const argument_t *templates) {
  out_args.clear();
  extra_args.clear();

  for (size_t i = 0; i < args.size(); i++) {
    const std::string &arg = args[i];
    const argument_t *templ = nullptr;
    for (size_t j = 0; templates[j].name[0] != 0; j++) {
      if (strcmp(arg.c_str(), templates[j].name) == 0) {
        templ = &templates[j];
        break;
      }
    }

    if (templ == nullptr) {
      if (::IsFlag(arg)) {
        fprintf(stderr, "Unknown flag: %s\n", arg.c_str());
        return false;
      }
      extra_args.push_back(arg);
      continue;
    }

    // Check for duplicate arguments - allowed for order preservation
    // but warn about it when debugging
#ifndef NDEBUG
    if (HasArgument(out_args, arg)) {
      fprintf(stderr, "Warning: Duplicate argument: %s\n", arg.c_str());
    }
#endif

    if (templ->type == kBooleanArgument) {
      out_args.push_back(std::pair<std::string, std::string>(arg, ""));
    } else {
      if (i + 1 >= args.size()) {
        fprintf(stderr, "Missing argument for option: %s\n", arg.c_str());
        return false;
      }
      out_args.push_back(std::pair<std::string, std::string>(arg, args[++i]));
    }
  }

  for (size_t j = 0; templates[j].name[0] != 0; j++) {
    const argument_t *templ = &templates[j];
    if (templ->type == kRequiredArgument &&
        !HasArgument(out_args, templ->name)) {
      fprintf(stderr, "Missing value for required argument: %s\n", templ->name);
      return false;
    }
  }

  return true;
}

bool GetUnsigned(unsigned *out, const std::string &arg_name,
                 unsigned default_value, const ordered_args_map_t &args) {
  auto it = FindArg(args, arg_name);
  if (it == args.end()) {
    *out = default_value;
    return true;
  }

  const std::string &value = it->second;
  if (value.empty()) {
    return false;
  }

  errno = 0;
  char *endptr = nullptr;
  unsigned long int num = strtoul(value.c_str(), &endptr, 10);
  if (num == ULONG_MAX && errno == ERANGE) {
    return false;
  }
  if (endptr == nullptr || endptr == value.c_str()) {
    return false;
  }
  if (*endptr != 0 || num > UINT_MAX) {
    return false;
  }
  *out = static_cast<unsigned>(num);

  return true;
}

bool GetString(std::string *out, const std::string &arg_name,
               std::string default_value, const ordered_args_map_t &args) {
  auto it = FindArg(args, arg_name);
  if (it == args.end()) {
    *out = default_value;
    return true;
  }

  const std::string &value = it->second;
  *out = value;

  return true;
}

bool GetBoolArgument(bool *out, const std::string &arg_name,
                     const ordered_args_map_t &args) {
  auto it = FindArg(args, arg_name);
  if (it == args.end()) {
    // Boolean argument not found
    *out = false;
  } else {
    *out = true;
  }

  return true;
}

}  // namespace ordered_args
