// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef INTERNAL_H
#define INTERNAL_H

#include "../tool/internal.h"
#include <string>
#include <vector>

typedef bool (*tool_func_t)(const std::vector<std::string> &args);

X509* CreateAndSignX509Certificate();
tool_func_t FindTool(const std::string &name);
tool_func_t FindTool(int argc, char **argv, int &starting_arg);

bool X509Tool(const args_list_t &args);

#endif //INTERNAL_H


