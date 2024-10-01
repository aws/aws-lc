# AWS-LC ML-DSA readme file

The source code in this folder implements ML-DSA as defined in FIPS 204 Module-Lattice-Based Digital Signature Standard [link](https://csrc.nist.gov/pubs/fips/204/final).

**Source code origin and modifications.** The source code was imported from a branch of the official repository of the Crystals-Dilithium team: https://github.com/pq-crystals/dilithium. The code was taken at [commit](https://github.com/pq-crystals/dilithium/commit/cbcd8753a43402885c90343cd6335fb54712cda1) as of 10/01/2024. At the moment, only the reference C implementation is imported.

The `api.h`, `fips202.h` and `params.h` header files were modified to support our [prefixed symbols build](https://github.com/awslabs/aws-lc/blob/main/BUILDING.md#building-with-prefixed-symbols).

- `randombytes.{h|c}` are deleted because we are using the randomness generation functions provided by AWS-LC.
- `sign.c`: calls to `randombytes` function is replaced with calls to `pq_custom_randombytes` and the appropriate header file is included (`crypto/rand_extra/pq_custom_randombytes.h`).

**Testing.** The KATs were obtained from https://github.com/pq-crystals/dilithium/tree/master/ref/nistkat.
