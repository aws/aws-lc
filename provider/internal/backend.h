// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_BACKEND_H
#define AWSLC_PROVIDER_BACKEND_H

// ===========================================================================
// How this provider is put together.
// ===========================================================================
//
// OpenSSL and AWS-LC both install their public headers as openssl/*.h, and they
// define the same type names incompatibly. Including both in one translation
// unit is a compile error, not a warning. Which include path comes first decides
// which library wins, so a build that happens to compile is not evidence the
// right header was found.
//
// Every structural decision below follows from that one constraint. The provider
// is two disjoint sets of translation units, each seeing exactly one library:
//
//   frontend/   sees OpenSSL's provider interface, never an AWS-LC header.
//               Holds OSSL_provider_init, the dispatch tables, OSSL_PARAM
//               plumbing, and the registry that maps algorithm names to tables.
//
//   backend/    sees AWS-LC's crypto, never an OpenSSL provider header.
//               Holds the calls that actually compute, allocation, and AWS-LC
//               introspection.
//
// Each side is a separate CMake object library with a disjoint include path,
// which makes the separation a compile error rather than a convention someone
// has to remember.
//
// THIS HEADER IS THE INTERFACE BETWEEN THEM, and the one header any file on
// either side may include. That is why it may name nothing from either library:
// plain C types only, no typedef, macro, or struct borrowed from either side.
// The same rule binds every header under internal/backend/.
//
// Three consequences shape every algorithm added later:
//
//   - Sizes cross as function calls, not constants. The front side cannot see
//     sizeof(SHA256_CTX), so it asks and allocates into an opaque buffer.
//   - No library type appears in a signature. Not EVP_MD *, not SHA256_CTX *,
//     not OSSL_PARAM *. Contexts cross as void *, buffers as unsigned char *
//     with an explicit length.
//   - Each side needs its own test binary. A test can link one library or the
//     other, never both, for the same reason a translation unit cannot.
//
// Layout follows from keeping what scales with the algorithm count separate from
// what does not:
//
//   internal/backend.h                       this file: the contract
//   internal/backend/<class>.h               per-class backend entry points
//   internal/frontend/<class>.h              per-class frontend contract
//   frontend/operations/<class>/<class>.c    class-wide frontend behavior
//   frontend/operations/<class>/<family>.c   family helpers and dispatch slots
//   backend/operations/<class>/<family>.c    explicit AWS-LC bindings
//
// The two operations/ trees correspond one to one where the shape allows it.
//
// Anything the whole provider needs regardless of algorithm is declared in this
// file. Anything that arrives per algorithm belongs in internal/backend/<class>.h.
//
// Every function declared here or under internal/backend/ returns 1 on success
// and 0 on failure, matching AWS-LC's convention. The front side translates that
// into whatever the dispatch slot it is serving expects.

#include <stddef.h>

#if defined(__cplusplus)
extern "C" {
#endif

// Allocate a zeroed buffer of |size| bytes, or NULL on failure. Provided by the
// back side so provider allocations go through AWS-LC's allocator rather than the
// platform's, which keeps the two libcryptos' memory management separate without
// routing anything through OpenSSL's core upcalls.
void *awslc_prov_zalloc(size_t size);

// Free a buffer from awslc_prov_zalloc, cleansing |size| bytes first. Contexts
// hold plaintext residue and, for later operation classes, key material, so the
// wipe is not optional.
void awslc_prov_clear_free(void *ptr, size_t size);

// The AWS-LC version this provider is linked against, e.g. "AWS-LC 5.4.0". The
// returned string is static and outlives any caller. Reported through the
// provider's buildinfo parameter, which is the only way a consumer can tell which
// AWS-LC is underneath.
const char *awslc_prov_backend_version(void);

// Whether the AWS-LC linked here is a FIPS build. FIPS is a compile-time property
// of AWS-LC, so this is constant for the life of the process.
int awslc_prov_backend_is_fips(void);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_BACKEND_H
