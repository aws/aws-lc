# AWS-LC Kyber readme file

The source code in this folder implements support for [Kyber](https://www.pq-crystals.org/kyber/index.shtml) Post-Quantum (PQ) Key Encapsulation Mechanism (KEM). The Kyber KEM was submitted to the [NIST PQ Crypto standardization project](https://csrc.nist.gov/projects/post-quantum-cryptography/post-quantum-cryptography-standardization) by the PQ-Crystals team. The team also developed and maintains Kyber’s source code repository, publicly available at Github ([link](https://github.com/pq-crystals/kyber)).

Kyber is specified with three parameter sets targeting security levels 1, 3, and 5 as defined by NIST. These three versions are denoted by Kyber512, Kyber768, and Kyber1024. Moreover, the Crystals team defined additional variants of each version that internally uses AES and SHA2 instead of SHA3 and SHAKE algorithms. These versions are denoted Kyber512-90s, Kyber768-90s, and Kyber1024-90s.

The AWS-LC team considers the official repository of [Kyber](https://github.com/pq-crystals/kyber) the primary source of Kyber’s implementation and takes the code directly from it. The code is integrated in AWS-LC with only minimal changes that are required to build on the platforms AWS-LC supports (see below for details).

NIST has not published the final PQ standard yet, and is not expected to do so until 2024. Therefore, the specification and implementation of Kyber is not finalized yet. Potentially, there will be changes to Kyber in the future. Some changes might even break backwards compatibility. The AWS-LC team follows the developments around the PQC project and will update the implementation and documentation if necessary. Therefore, AWS-LC can not promise backward compatibility of the Kyber implementation and API until NIST locks in the specification and reserves the right to change the implementation if necessary.

**Supported versions.** AWS-LC supports Kyber512/768/1024 algorithms (as specified in the Round-3 submission of Kyber). The NIDs assigned to Kyber512/768/1024 are `NID_KYBER512_R3`, `NID_KYBER768_R3`, `NID_KYBER1024_R3`, respectively.

**Source code origin and modifications.** The source code was taken from the primary source of Kyber at [link](https://github.com/pq-crystals/kyber), at [commit](https://github.com/pq-crystals/kyber/tree/faf5c3fe33e0b61c7c8a7888dd862bf5def17ad2) as of September 13th 2021. Only the reference C implementation of Kyber is currently integrated. The source code is in the `pqcrystals_kyber_ref_common` folder.

To be able to compile multiple variants of Kyber without duplicating the code, we add a C file for each Kyber variant, directly include the required C and header files from `pqcrystals_kyber_ref_common`, and define the appropriate `KYBER_K` value to specify the variant to be compiled (see `kyber512r3_ref.c` for example).

The following changes were made to the source code in `pqcrystals_kyber_ref_common` (compared to the official Kyber repository):

* `randombytes.{h|c}` are deleted because we are using the randomness generation functions provided by AWS-LC.
* `rng.{h|c}` are deleted because we are using the randomness generation functions provided by AWS-LC.
* `sha2.h, sha256.c, sha512.c, symmetric-aes.c` are removed because we are using only the SHA3 based Kyber (SHA2 and AES are used in the 90s variants only).
* `indcpa.c`: call to `randombytes` function is replaced with a call to `pq_custom_randombytes` and the appropriate header file is included (`crypto/rand_extra/pq_custom_randombytes.h`).
* `kem.c`: calls to `randombytes` function is replaced with calls to `pq_custom_randombytes` and the appropriate header file is included (`crypto/rand_extra/pq_custom_randombytes.h`).
* `symmetric-shake.c`: unnecessary include of `fips202.h` is removed.
* `api.h`, `fips202.h`, `params.h`: modified [in this PR](https://github.com/aws/aws-lc/pull/655) to support our [prefixed symbols build](https://github.com/aws/aws-lc/blob/main/BUILDING.md#building-with-prefixed-symbols).
* `poly.c` and 'polyvec.c' were modified to remove 6 lines of comment from these two reference commits ([dda29cc](https://github.com/pq-crystals/kyber/commit/dda29cc63af721981ee2c831cf00822e69be3220), [272125f](https://github.com/pq-crystals/kyber/commit/272125f6acc8e8b6850fd68ceb901a660ff48196))
* `poly.c`: the `poly_frommsg` function was modified to address the constant-time issue described [here](https://github.com/pq-crystals/kyber/commit/9b8d30698a3e7449aeb34e62339d4176f11e3c6c).

**Usage.** The KEM API is defined and documented in `include/openssl/evp.h`. To see examples of how to use any KEM, including Kyber, see `crypto/kem/README.md`.
