// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// The provider entry point is deliberately unimplemented. Keeping the exported
// symbol in place lets the build and CI infrastructure verify the module shape
// without introducing provider behavior.

#include <openssl/core.h>
#include <openssl/core_dispatch.h>

#if defined(_WIN32)
#define AWSLC_PROV_ENTRY __declspec(dllexport)
#else
#define AWSLC_PROV_ENTRY __attribute__((visibility("default")))
#endif

AWSLC_PROV_ENTRY int OSSL_provider_init(const OSSL_CORE_HANDLE *handle,
                                        const OSSL_DISPATCH *in,
                                        const OSSL_DISPATCH **out,
                                        void **provctx) {
  (void)handle;
  (void)in;
  (void)out;
  (void)provctx;
  return 0;
}
