// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_BOUNDARY_H
#define AWSLC_PROVIDER_BOUNDARY_H

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
// THIS HEADER IS THE INTERFACE BETWEEN THEM. A header's directory says who may
// include it:
//
//   boundary.h, boundary/**   either side. Plain C types only: no typedef,
//                             macro, or struct borrowed from either library.
//   frontend/**               the OpenSSL side only.
//   backend/**                the AWS-LC side only.
//
// Within frontend/ and backend/, a header sits next to the sources it pairs
// with.
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
// What scales with the algorithm count stays apart from what does not, the same
// way across the boundary and on each side:
//
//   provider-wide           this file across the boundary; on a side, next to
//                           that side's provider-wide sources.
//   operation-wide          shapes, declaring macros, and helpers shared by
//                           every family in an operation. Across the boundary,
//                           boundary/<operation>.h; on a side, next to
//                           operations/<operation>/<operation>.c.
//   operations/<family>.h   one family's declarations across every operation it
//                           serves, including the operation headers it uses.
//                           It sits directly under operations/, not inside an
//                           operation directory, because a family can span
//                           several operations.
//
// No umbrella includes. An operation header never includes its family headers;
// each consumer includes the family header it uses. frontend/operations/ and
// backend/operations/ correspond one to one where the shape allows it.
//
// Every function declared here or under boundary/ returns 1 on success and 0 on
// failure, matching AWS-LC's convention. The front side translates that into
// whatever the dispatch slot it is serving expects.

#include <stddef.h>
#include <stdint.h>

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

// Wipe |size| bytes at |ptr|. AWS-LC exports OPENSSL_cleanse, so a front-side
// call to it would bind to AWS-LC's libcrypto rather than the host's.
void awslc_prov_cleanse(void *ptr, size_t size);

// The AWS-LC version this provider is linked against, e.g. "AWS-LC 5.4.0". The
// returned string is static and outlives any caller. Reported through the
// provider's buildinfo parameter, which is the only way a consumer can tell which
// AWS-LC is underneath.
const char *awslc_prov_backend_version(void);

// Whether the linked AWS-LC reports FIPS mode through its public FIPS_mode()
// API. FIPS is a compile-time property of AWS-LC, so this is constant for the
// life of the process.
int awslc_prov_backend_is_fips(void);

// Bracket one complete AWS-LC service and report whether AWS-LC approved it.
uint64_t awslc_prov_service_indicator_before_call(void);
int awslc_prov_service_indicator_after_call(uint64_t before);

// Re-run AWS-LC's known-answer self-tests. Aborts on failure in FIPS mode.
int awslc_prov_backend_self_test(void);

// ===========================================================================
// Error translation.
// ===========================================================================
//
// The provider reports every error under its own private "awslc" error library.
//
// The reason code space has three disjoint ranges:
//
//   1 to 99                  AWS-LC's cross-library reasons. Any AWS-LC library
//                            can raise these and AWS-LC resolves them without
//                            consulting the library field, so neither do we.
//   100 to 4095              The provider's own reasons, AWSLC_PROV_R_* below.
//   4096+                    An AWS-LC library-specific reason, tagged with the
//                            library that raised it.
//
// AWS-LC layers on its own coded "libraries". e.g. ec, cipher, hmac...
// Each library numbers its reasons independently which we then remap onto the
// provider's own reason code namespace.
// A remapped library-specific reason code looks like this:
// [31:18] Used by OpenSSL, [17:12] AWS-LC library ID, [11:0] AWS-LC reason code

#define AWSLC_PROV_ERROR_LIB_SHIFT 12
#define AWSLC_PROV_ERROR_MAX_LIB 63
#define AWSLC_PROV_ERROR_FIRST_OWN_REASON 100

// The provider reason code for AWS-LC library |lib|'s reason |reason|.
#define AWSLC_PROV_ERROR_REASON(lib, reason) \
  ((uint32_t)((uint32_t)(lib) << AWSLC_PROV_ERROR_LIB_SHIFT) | (uint32_t)(reason))

// The provider's own reasons codes.
#define AWSLC_PROV_R_BACKEND_ERROR 100
#define AWSLC_PROV_R_INVALID_PARAMETER 101
#define AWSLC_PROV_R_UNAPPROVED_OPERATION 102

// Max length for the error detail string.
#define AWSLC_PROV_ERROR_DETAIL_SIZE 256

// One AWS-LC error record.
typedef struct {
  // The provider reason code, ready to hand to the core.
  uint32_t reason;
  // AWS-LC's origin file:line. A static literal AWS-LC owns, or NULL.
  const char *file;
  int line;
  // Human-readable detail that AWS-LC raised for the record, the reason
  // text AWS-LC itself resolves for it, and whatever per-record detail AWS-LC
  // attached.
  char detail[AWSLC_PROV_ERROR_DETAIL_SIZE];
} AWSLC_PROV_ERROR;

// Each dispatch call owns its thread's whole AWS-LC error queue: the provider
// assumes it is AWS-LC's only error-queue user in the process.
// Empty the AWS-LC queue.
void awslc_prov_error_clear(void);
// Pop one error off of the AWS-LC error-queue and write it to |out|
int awslc_prov_error_shift(AWSLC_PROV_ERROR *out);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_BOUNDARY_H
