// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef INTERNAL_H
#define INTERNAL_H

#include "../tool/internal.h"

X509* CreateAndSignX509Certificate();

bool X509Tool(const args_list_t &args) ;

#endif //INTERNAL_H


