# AWS-LC ML-KEM readme file

The source code in this folder implements ML-KEM as defined in FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard ([link](https://csrc.nist.gov/pubs/fips/203/final).

**Source code origin and modifications.** The source code was imported from a branch of the official repository of the Crystals-Kyber team that follows the standard draft: https://github.com/pq-crystals/kyber/tree/standard. The code was taken at [commit](https://github.com/pq-crystals/kyber/commit/11d00ff1f20cfca1f72d819e5a45165c1e0a2816) as of 03/26/2024. At the moment, only the reference C implementation is imported.

The code was refactored in [this PR](https://github.com/aws/aws-lc/pull/1763) by parametrizing all functions that depend on values that are specific to a parameter set, i.e., that directly or indirectly depend on the value of KYBER_K. To do this, in `params.h` we defined a structure that holds those ML-KEM parameters and functions
that initialize a given structure with values corresponding to a parameter set. This structure is then passed to every function that requires it as a function argument. In addition, the following changes were made to the source code in `ml_kem_ref` directory:
- `randombytes.{h|c}` are deleted because we are using the randomness generation functions provided by AWS-LC.
- `kem.c`: call to randombytes function is replaced with a call to RAND_bytes and the appropriate header file is included (openssl/rand.h).
- `fips202.{h|c}` are deleted as all SHA3/SHAKE functionality is provided instead by AWS-LC fipsmodule/sha rather than the reference implementation.
- `symmetric-shake.c`: unnecessary include of fips202.h is removed.
- `api.h`: `pqcrystals` prefix substituted with `ml_kem` (to be able to build alongside `crypto/kyber`).
- `poly.c`: the `poly_frommsg` function was modified to address the constant-time issue described [here](https://github.com/pq-crystals/kyber/commit/9b8d30698a3e7449aeb34e62339d4176f11e3c6c).
- All internal header files were updated with unique `ML_KEM_*` include guards.

**Testing.** The KATs were obtained from an independent implementation of ML-KEM written in SPARK Ada subset: https://github.com/awslabs/LibMLKEM.
