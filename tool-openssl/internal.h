// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef INTERNAL_H
#define INTERNAL_H

#include "../tool/internal.h"
#include <string>
#include <vector>
#include <fstream>
#include <iterator>
#include <string>
#include <iostream>

typedef bool (*tool_func_t)(const std::vector<std::string> &args);

bool IsNumeric(const std::string& str);

X509* CreateAndSignX509Certificate();

bool WriteSignedCertificate(X509 *x509, const std::string &out_path);

bool LoadPrivateKeyAndSignCertificate(X509 *x509, const std::string &signkey_path);

tool_func_t FindTool(const std::string &name);
tool_func_t FindTool(int argc, char **argv, int &starting_arg);

bool X509Tool(const args_list_t &args);
bool rsaTool(const args_list_t &args);
bool md5Tool(const args_list_t &args);

#endif //INTERNAL_H
