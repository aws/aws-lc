# AWS-LC ML-DSA readme file

The source code in this folder implements ML-DSA as defined in FIPS 204 Module-Lattice-Based Digital Signature Standard [link](https://csrc.nist.gov/pubs/fips/204/final).

**Source code origin and modifications** 

The source code was imported from a branch of the official repository of the Crystals-Dilithium team: https://github.com/pq-crystals/dilithium. The code was taken at [commit](https://github.com/pq-crystals/dilithium/commit/cbcd8753a43402885c90343cd6335fb54712cda1) as of 10/01/2024. At the moment, only the reference C implementation is imported.

The `api.h`, `fips202.h` and `params.h` header files were modified to support our [prefixed symbols build](https://github.com/awslabs/aws-lc/blob/main/BUILDING.md#building-with-prefixed-symbols).

- `randombytes.{h|c}` are deleted because we are using the randomness generation functions provided by AWS-LC.
- `sign.c`: calls to `randombytes` function is replaced with calls to `pq_custom_randombytes` and the appropriate header file is included (`crypto/rand_extra/pq_custom_randombytes.h`).
- `ntt.c`, `poly.c`, `reduce.c`, `reduce.h`: have been modified with a code refactor. The function `fqmul` has been added to bring mode code consistency with Kyber/ML-KEM. See https://github.com/aws/aws-lc/pull/1748 for more details on this change.
- `reduce.c`: a small fix to documentation has been made on the bounds of `reduce32`.
- `poly.c`: a small fix to documentation has been made on the bounds of `poly_reduce`.
- `polyvec.c`: a small fix to documentation has been made on the bounds of `polyveck_reduce`.

**Testing** 

The KATs were obtained from https://github.com/pq-crystals/dilithium/tree/master/ref/nistkat.
To compile the KAT programs on Linux or macOS, go to the `ref/` directory and run `make nistkat`. This will produce executables within `nistkat` which once executed will produce the KATs: `PQCsignKAT_Dilithium2.rsp`, `PQCsignKAT_Dilithium3.rsp`,`PQCsignKAT_Dilithium5.rsp`.
