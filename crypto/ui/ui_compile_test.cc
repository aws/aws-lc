// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/asn1.h>
#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/crypto.h>
#include <openssl/dh.h>
#include <openssl/dsa.h>
#include <openssl/ec.h>
#include <openssl/engine.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/obj_mac.h>
#include <openssl/objects.h>
#include <openssl/opensslv.h>
#include <openssl/pem.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/ssl.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <openssl/x509v3.h>

// This is a compile-time check that the UI types are declared only by
// <openssl/ui.h>.
//
// ### Motivation
// When building against AWS-LC, pyca/cryptography defines
// |typedef void UI_METHOD;| after including the headers above, but not ui.h.
// If any of them declared |UI_METHOD|, the typedefs below would conflict and
// this file would fail to compile.
//
// This file must not include <openssl/ui.h>, and it intentionally does not
// contain any runtime tests.

typedef void UI;
typedef void UI_METHOD;
typedef void UI_STRING;
