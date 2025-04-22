# ML-KEM

The source code in this directory implements ML-KEM as defined in
the [FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard](https://csrc.nist.gov/pubs/fips/203/final).
It is imported from [mlkem-native](https://github.com/pq-code-package/mlkem-native)
using [importer.sh](importer.sh); see [META.yml](META.yml) for import details.

## Running the importer

To re-run the importer, do

```bash
rm -rf mlkem # Remove old mlkem source
./importer.sh
```

By default, the importer will not run if [mlkem](mlkem) already/still exists. To force removal of any existing [mlkem](mlkem), use `./importer.sh --force`.

The repository and branch to be used for the import can be configured through the environment variables `GITHUB_REPOSITORY` and `GITHUB_SHA`, respectively. The default is equivalent to

```bash
GITHUB_REPOSITORY=pq-code-package/mlkem-native.git GITHUB_SHA=main ./importer.sh
```

That is, by default importer.sh will clone and install the latest [main](https://github.com/pq-code-package/mlkem-native/tree/main) of mlkem-native.

After a successful import, [META.yml](META.yml) will reflect the source, branch, commit and timestamp of the import.

### Import Scope

mlkem-native has a C-only version as well as native 'backends' in AVX2 and
Neon for high performance. At present, [importer.sh](importer.sh) imports only
the C-only version.

mlkem-native offers its own FIPS-202 implementation, including fast
versions of batched FIPS-202. [importer.sh](importer.sh) does _not_ import those.
Instead, glue-code around AWS-LC's own FIPS-202 implementation is provided in
[fips202_glue.h](fips202_glue.h) and [fips202x4_glue.h](fips202x4_glue.h).

## Configuration and compatibility layer

mlkem-native is used with a custom configuration file [mlkem_native_config.h](mlkem_native_config.h). This file includes
a compatibility layer between AWS-LC/OpenSSL and mlkem-native, covering:

* FIPS/PCT: If `AWSLC_FIPS` is set, `MLK_CONFIG_KEYGEN_PCT` is
  enabled to includ a PCT.
* FIPS/PCT: If `BORINGSSL_FIPS_BREAK_TESTS` is set,
  `MLK_CONFIG_KEYGEN_PCT_BREAKAGE_TEST` is set and `mlk_break_pct`
  defined via `boringssl_fips_break_test("MLKEM_PWCT")`, to include
  runtime-breakage of the PCT for testing purposes.
* CT: If `BORINGSSL_CONSTANT_TIME_VALIDATION` is set, then
  `MLK_CONFIG_CT_TESTING_ENABLED` is set to enable valgrind testing.
* Zeroization: `MLK_CONFIG_CUSTOM_ZEROIZE` is set and `mlk_zeroize`
  mapped to `OPENSSL_cleanse` to use OpenSSL's zeroization function.
* Randombytes: `MLK_CONFIG_CUSTOM_RANDOMBYTES` is set and `mlk_randombytes`
  mapped to `RAND_bytes` to use AWS-LC's randombytes function.

## Build process

At the core, mlkem-native is a 'single-level' implementation of ML-KEM:
A build of the main source tree provides an implementation of
exactly one of ML-KEM-512/768/1024, depending on the MLK_CONFIG_PARAMETER_SET
parameter. All source files for a single-build of mlkem-native are bundled in
[mlkem_native_bcm.c](mlkem/mlkem_native_bcm.c), which is also imported from
mlkem-native.

To build all security levels, [mlkem_native_bcm.c](mlkem/mlkem_native_bcm.c)
is included three times into [ml_kem.c](ml_kem.c), once per security level.
Level-independent code is included only once and shared across the levels;
this is controlled through the configuration options
`MLK_CONFIG_MULTILEVEL_WITH_SHARED` and `MLK_CONFIG_MULTILEVEL_NO_SHARED`
used prior to importing the instances of [mlkem_native_bcm.c](mlkem/mlkem_native_bcm.c) into [ml_kem.c](ml_kem.c).

Note that the multilevel build process is entirely internal to `ml_kem.c`,
and does not affect the AWS-LC build otherwise.

## Formal Verification

All C-code imported by [importer.sh](importer.sh) is formally verified using the
C Bounded Model Checker ([CBMC](https://github.com/diffblue/cbmc/)) to be free of
various classes of undefined behaviour, including out-of-bounds memory accesses and
arithmetic overflow; the latter is of particular interest for ML-KEM because of
the use of lazy modular reduction for improved performance.

The heart of the CBMC proofs are function contract and loop annotations to
the C-code. Function contracts are denoted `__contract__(...)` clauses and
occur at the time of declaration, while loop contracts are denoted
`__loop__` and follow the `for` statement.

The function contract and loop statements are kept in the source, but
removed by the preprocessor so long as the CBMC macro is undefined. Keeping
them simplifies the import, and care has been taken to make them readable
to the non-expert, and thereby serve as precise documentation of
assumptions and guarantees upheld by the code.

## Testing

The KATs were obtained from an independent implementation of ML-KEM written
in SPARK Ada subset: https://github.com/awslabs/LibMLKEM.

## Side-channels

mlkem-native's CI uses a patched version of valgrind to check for various
compilers and compile flags that there are no secret-dependent memory
accesses, branches, or divisions. The relevant assertions are kept
and used if `MLK_CONFIG_CT_TESTING_ENABLED` is set, which is the case
if and only if `BORINGSSL_CONSTANT_TIME_VALIDATION` is set.

mlkem-native uses value barriers to block
potentially harmful compiler reasoning and optimization. Where standard
gcc/clang inline assembly is not available, mlkem-native falls back to a
slower 'opt blocker' based on a volatile global -- both are described in
[verify.h](https://github.com/aws/aws-lc/blob/df5b09029e27d54b2b117eeddb6abd983528ae15/crypto/fipsmodule/ml_kem/mlkem/verify.h).

## Comparison to reference implementation

mlkem-native is a fork of the ML-KEM [reference
implementation](https://github.com/pq-crystals/kyber).

The following gives an overview of the major changes:

- CBMC and debug annotations, and minor code restructurings or signature
  changes to facilitate the CBMC proofs. For example, `poly_add(x,a)` only
  comes in a destructive variant to avoid specifying aliasing constraints;
  `poly_rej_uniform` has an additional `offset` parameter indicating the
  position in the sampling buffer, to avoid passing shifted pointers).
- Introduction of 4x-batched versions of some functions from the reference
  implementation. This is to leverage 4x-batched Keccak-f1600 implementations
  if present. The batching happens at the C level even if no native backend
  for FIPS 202 is present.
- FIPS 203 compliance: Introduced PK (FIPS 203, Section 7.2, 'modulus
  check') and SK (FIPS 203, Section 7.3, 'hash check') check, as well as
  optional PCT (FIPS 203, Section 7.1, Pairwise Consistency). Also,
  introduced zeroization of stack buffers as required by (FIPS 203, Section
  3.3, Destruction of intermediate values).
- Introduction of native backend implementations. With the exception of the
  native backend for `poly_rej_uniform()`, which may fail and fall back to
  the C implementation, those are drop-in replacements for the corresponding
  C functions and dispatched at compile-time.
- Restructuring of files to separate level-specific from level-generic
  functionality. This is needed to enable a multi-level build of mlkem-native
  where level-generic code is shared between levels.
- More pervasive use of value barriers to harden constant-time primitives,
  even when Link-Time-Optimization (LTO) is enabled. The use of LTO can lead
  to insecure compilation in case of the reference implementation.
- Use of a multiplication cache ('mulcache') structure to simplify and
  speedup the base multiplication.
- Different placement of modular reductions: We reduce to _unsigned_
  canonical representatives in `poly_reduce()`, and _assume_ such in all
  polynomial compression functions. The reference implementation works with a
  _signed_ `poly_reduce()`, and embeds various signed->unsigned conversions
  in the compression functions.
- More inlining: Modular multiplication and primitives are in a header
  rather than a separate compilation unit.
