// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_BOUNDARY_NAMES_H
#define AWSLC_PROVIDER_BOUNDARY_NAMES_H

// Algorithm names as ':'-separated aliases, canonical name first. Each must
// equal the same-named PROV_NAMES_* in OpenSSL's
// providers/implementations/include/prov/names.h: the core matches fetches and
// cross-provider operations against these exact spellings.

#define AWSLC_PROV_NAMES_SHA2_224 \
  "SHA2-224:SHA-224:SHA224:2.16.840.1.101.3.4.2.4"
#define AWSLC_PROV_NAMES_SHA2_256 \
  "SHA2-256:SHA-256:SHA256:2.16.840.1.101.3.4.2.1"
#define AWSLC_PROV_NAMES_SHA2_384 \
  "SHA2-384:SHA-384:SHA384:2.16.840.1.101.3.4.2.2"
#define AWSLC_PROV_NAMES_SHA2_512 \
  "SHA2-512:SHA-512:SHA512:2.16.840.1.101.3.4.2.3"
#define AWSLC_PROV_NAMES_SHA2_512_224 \
  "SHA2-512/224:SHA-512/224:SHA512-224:2.16.840.1.101.3.4.2.5"
#define AWSLC_PROV_NAMES_SHA2_512_256 \
  "SHA2-512/256:SHA-512/256:SHA512-256:2.16.840.1.101.3.4.2.6"

#endif  // AWSLC_PROVIDER_BOUNDARY_NAMES_H
