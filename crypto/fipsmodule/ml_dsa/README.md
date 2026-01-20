# ML-DSA

The source code in this directory implements ML-DSA as defined in
the [FIPS 204 Module-Lattice-Based Digital Signature Standard](https://csrc.nist.gov/pubs/fips/204/final).
It is imported from [mldsa-native](https://github.com/pq-code-package/mldsa-native)
using [importer.sh](importer.sh); see [META.yml](META.yml) for import details.

## Running the importer

To re-run the importer, do

```bash
rm -rf mldsa # Remove old mldsa source
./importer.sh
```

By default, the importer will not run if [mldsa](mldsa) already/still exists. To force removal of any existing [mldsa](mldsa), use `./importer.sh --force`.

The repository and branch to be used for the import can be configured through the environment variables `GITHUB_REPOSITORY` and `GITHUB_SHA`, respectively. The default is equivalent to

```bash
GITHUB_REPOSITORY=pq-code-package/mldsa-native.git GITHUB_SHA=main ./importer.sh
```

That is, by default importer.sh will clone and install the latest [main](https://github.com/pq-code-package/mldsa-native/tree/main) of mldsa-native.

After a successful import, [META.yml](META.yml) will reflect the source, branch, commit and timestamp of the import.

### Import Scope

mldsa-native has a C-only version as well as native 'backends' in AVX2 and
Neon for high performance. At present, [importer.sh](importer.sh) imports only
the C-only version.

mldsa-native offers its own FIPS-202 implementation, including fast
versions of batched FIPS-202. [importer.sh](importer.sh) does _not_ import those.
Instead, glue-code around AWS-LC's own FIPS-202 implementation is provided in
[fips202_glue.h](fips202_glue.h) and [fips202x4_glue.h](fips202x4_glue.h).

## Configuration and compatibility layer

mldsa-native is used with a custom configuration file [mldsa_native_config.h](mldsa_native_config.h). This file includes
a compatibility layer between AWS-LC/OpenSSL and mldsa-native, covering:

* FIPS/PCT: If `AWSLC_FIPS` is set, `MLD_CONFIG_KEYGEN_PCT` is
  enabled to include a PCT.
* FIPS/PCT: If `BORINGSSL_FIPS_BREAK_TESTS` is set,
  `MLD_CONFIG_KEYGEN_PCT_BREAKAGE_TEST` is set and `mld_break_pct`
  defined via `boringssl_fips_break_test("MLDSA_PWCT")`, to include
  runtime-breakage of the PCT for testing purposes.
* CT: If `BORINGSSL_CONSTANT_TIME_VALIDATION` is set, then
  `MLD_CONFIG_CT_TESTING_ENABLED` is set to enable valgrind testing.
* Zeroization: `MLD_CONFIG_CUSTOM_ZEROIZE` is set and `mld_zeroize`
  mapped to `OPENSSL_cleanse` to use OpenSSL's zeroization function.
* Randombytes: `MLD_CONFIG_CUSTOM_RANDOMBYTES` is set and `mld_randombytes`
  mapped to `RAND_bytes` to use AWS-LC's randombytes function.

## Build process

At the core, mldsa-native is a 'single-level' implementation of ML-DSA:
A build of the main source tree provides an implementation of
exactly one of ML-DSA-44/65/87, depending on the MLD_CONFIG_PARAMETER_SET
parameter. All source files for a single-build of mldsa-native are bundled in
[mldsa_native_bcm.c](mldsa/mldsa_native_bcm.c), which is also imported from
mldsa-native.

To build all security levels, [mldsa_native_bcm.c](mldsa/mldsa_native_bcm.c)
is included three times into [ml_dsa.c](ml_dsa.c), once per security level.
Level-independent code is included only once and shared across the levels;
this is controlled through the configuration options
`MLD_CONFIG_MULTILEVEL_WITH_SHARED` and `MLD_CONFIG_MULTILEVEL_NO_SHARED`
used prior to importing the instances of [mldsa_native_bcm.c](mldsa/mldsa_native_bcm.c) into [ml_dsa.c](ml_dsa.c).

Note that the multilevel build process is entirely internal to `ml_dsa.c`,
and does not affect the AWS-LC build otherwise.

## Formal Verification

All C-code imported by [importer.sh](importer.sh) is formally verified using the
C Bounded Model Checker ([CBMC](https://github.com/diffblue/cbmc/)) to be free of
various classes of undefined behaviour, including out-of-bounds memory accesses and
arithmetic overflow; the latter is of particular interest for ML-DSA because of
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

We test ML-DSA with Known Answer Test (KAT) vectors obtained from https://github.com/post-quantum-cryptography/KAT within `PQDSAParameterTest.KAT`. We select the KATs for the signing mode `hedged`, which derives the signing private random seed (rho) pseudorandomly from the signer's private key, the message to be signed, and a 256-bit string `rnd` which is generated at random. The `pure` variant of these KATs were used, as they provide test vector inputs for "pure" i.e., non-pre-hashed messages. The KAT files have been modified to insert linebreaks between each test vector set.

We also run the ACVP test vectors obtained from https://github.com/usnistgov/ACVP-Server within the three functions `PerMLDSATest.ACVPKeyGen`, `PerMLDSATest.ACVPSigGen` and `PerMLDSATest.ACVPSigVer`. These correspond to the tests found at [ML-DSA-keyGen-FIPS204](https://github.com/usnistgov/ACVP-Server/tree/master/gen-val/json-files/ML-DSA-keyGen-FIPS204), [ML-DSA-sigGen-FIPS204](https://github.com/usnistgov/ACVP-Server/tree/master/gen-val/json-files/ML-DSA-sigGen-FIPS204), and [ML-DSA-sigVer-FIPS204](https://github.com/usnistgov/ACVP-Server/tree/master/gen-val/json-files/ML-DSA-sigVer-FIPS204).
To test ML-DSA pure, non-deterministic mode, we use `tgId = 19, 21, 23` of sigGen and `tgId = 7, 9, 11` of sigVer.
To test ML-DSA ExternalMu, non-deterministic mode, we use `tgId = 20, 22, 24` of sigGen and `tgId = 8, 10, 12` of sigVer.

The test suite includes:

* Known Answer Tests (KAT) for all three parameter sets (ML-DSA-44/65/87)
* Functional tests for key generation, signing, and verification
* ExtMu (External Mu) variant tests for pre-hash modes
* ACVP (Automated Cryptographic Validation Protocol) test vectors
* Pairwise Consistency Test (PCT) validation when FIPS mode is enabled
* Key consistency tests including public key derivation from secret key

## Side-channels

mldsa-native's CI uses a patched version of valgrind to check for various
compilers and compile flags that there are no secret-dependent memory
accesses, branches, or divisions. The relevant assertions are kept
and used if `MLD_CONFIG_CT_TESTING_ENABLED` is set, which is the case
if and only if `BORINGSSL_CONSTANT_TIME_VALIDATION` is set.

mldsa-native uses value barriers to block
potentially harmful compiler reasoning and optimization. Where standard
gcc/clang inline assembly is not available, mldsa-native falls back to a
slower 'opt blocker' based on a volatile global -- both are described in
[ct.h](https://github.com/pq-code-package/mldsa-native/blob/main/mldsa/ct.h).

## Comparison to reference implementation

mldsa-native is a fork of the ML-DSA [reference
implementation](https://github.com/pq-crystals/dilithium) (Dilithium).

The following gives an overview of the major changes:

- CBMC and debug annotations, and minor code restructurings or signature
  changes to facilitate the CBMC proofs. For example, functions are structured
  to make loop bounds and memory access patterns explicit for formal verification.
- Introduction of 4x-batched versions of some functions from the reference
  implementation. This is to leverage 4x-batched Keccak-f1600 implementations
  if present. The batching happens at the C level even if no native backend
  for FIPS 202 is present.
- FIPS 204 compliance: Introduced optional PCT (FIPS 204, Section 4.4, Pairwise
  Consistency) and zeroization of stack buffers as required by (FIPS 204, 
  Section 3.6.3, Destruction of intermediate values).
- Restructuring of files to separate level-specific from level-generic
  functionality. This is needed to enable a multi-level build of mldsa-native
  where level-generic code is shared between levels.
- More pervasive use of value barriers to harden constant-time primitives,
  even when Link-Time-Optimization (LTO) is enabled. The use of LTO can lead
  to insecure compilation in case of the reference implementation.
