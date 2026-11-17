# SLH-DSA

The source code in this directory implements SLH-DSA as defined in the
[FIPS 205 Stateless Hash-Based Digital Signature Standard](https://csrc.nist.gov/pubs/fips/205/final).
It is a hand port of [slhdsa-c](https://github.com/pq-code-package/slhdsa-c),
originally written by Markku-Juhani O. Saarinen. See [META.yml](META.yml) for
the upstream commit.

## Parameter sets

Only the SHAKE "small" parameter sets of FIPS 205, Table 2 are implemented.

| Parameter set      | `SLHDSA_PARAMS`               | Public key | Private key | Signature |
|--------------------|-------------------------------|-----------:|------------:|----------:|
| SLH-DSA-SHAKE-128s | `slh_dsa_shake_128s_params()` |         32 |          64 |      7856 |
| SLH-DSA-SHAKE-192s | `slh_dsa_shake_192s_params()` |         48 |          96 |     16224 |
| SLH-DSA-SHAKE-256s | `slh_dsa_shake_256s_params()` |         64 |         128 |     29792 |

## API

The interface is [slh_dsa.h](slh_dsa.h). Every function takes the parameter
set, and every buffer is passed with its length.

| Function                                                  | FIPS 205              |
|-----------------------------------------------------------|-----------------------|
| `slh_dsa_keypair`                                         | Algorithm 21          |
| `slh_dsa_check_private_key`, `slh_dsa_public_from_private` | Sections 3.1, 9.1   |
| `slh_dsa_sign`, `slh_dsa_verify`                          | Algorithms 22, 24     |
| `slh_dsa_prehash_sign`, `slh_dsa_prehash_verify`          | Algorithms 23, 25     |
| `slh_dsa_prehash_sign_digest`, `slh_dsa_prehash_verify_digest` | Algorithms 23, 25 |
| `slh_dsa_prehash_digest_bytes`                            | Section 10.2.2        |
| `slh_dsa_keypair_internal`                                | Algorithm 18          |
| `slh_dsa_sign_internal`, `slh_dsa_verify_internal`        | Algorithms 19, 20     |

`slh_dsa_sign` and `slh_dsa_verify` are pure SLH-DSA. They take an optional
context string of up to 255 bytes (FIPS 205, Section 10.2.1).

The `prehash` functions are HashSLH-DSA (FIPS 205, Section 10.2.2) with
SHAKE128 or SHAKE256 as the pre-hash function, selected by `NID_shake128` or
`NID_shake256`. The message is hashed to `SHAKE128(M, 256)` or
`SHAKE256(M, 512)` and signed with the DER-encoded OID of the hash,
2.16.840.1.101.3.4.2.11 or 2.16.840.1.101.3.4.2.12 (see the
[NIST Computer Security Objects Register](https://csrc.nist.gov/projects/computer-security-objects-register/algorithm-registration)).
SHAKE128 is only appropriate for security category 1 (FIPS 205,
Section 10.2.2), so it is supported only with SLH-DSA-SHAKE-128s. RFC 9909
pairs SLH-DSA-SHAKE-128s with SHAKE128, and SLH-DSA-SHAKE-192s and -256s with
SHAKE256. The `_digest` variants take the 32- or 64-byte digest
instead of the message. A pure signature never verifies as a HashSLH-DSA
signature, or vice versa.

`slh_dsa_check_private_key` regenerates PK.root from SK.seed and PK.seed and
compares it with the private key, which assures possession of the private key
(FIPS 205, Sections 3.1 and 9.1). `slh_dsa_public_from_private` runs it, and
fails if the private key is inconsistent. It costs about as much as key
generation.

Signing is hedged: it uses n bytes of fresh randomness from the RBG. The
deterministic variant (FIPS 205, Section 9.2) is available only through
`slh_dsa_sign_internal`. Like the other `_internal` functions, it exists only
for tests and ACVP. FIPS 205, Section 9 says these should not be available to
applications, so they are not declared in any public header and are never
approved.

## Source layout

| File                   | Contents                                                     |
|------------------------|--------------------------------------------------------------|
| [internal.h](internal.h) | Internal interfaces and base_2b (Algorithm 4)              |
| [address.h](address.h) | ADRS (Section 4.2)                                           |
| [thash.c](thash.c)     | F, H, T_l, PRF, PRF_msg and H_msg for SHAKE (Section 11.1)   |
| [wots.c](wots.c)       | WOTS+ (Algorithms 5-8)                                       |
| [merkle.c](merkle.c)   | XMSS and the hypertree (Algorithms 9-13)                     |
| [fors.c](fors.c)       | FORS (Algorithms 14-17)                                      |
| [slh_dsa.c](slh_dsa.c) | Parameter sets, key generation, signing, verification (Algorithms 18-25) |

Each function that implements an algorithm of FIPS 205 is marked with its
number and page.

## Changes from slhdsa-c

* SHAKE only. SHAKE256 is AWS-LC's own implementation, and the SHA2 parameter
  sets and bundled SHA-2/SHA-3 code are not ported.
* Parameter sets are plain integers rather than tables of function pointers,
  so they need no relocations in the FIPS module.
* Every secret, including the shared SHAKE256 state, lives in one
  `SLHDSA_STATE` that is cleansed at the end of each operation. Each exported
  function also overwrites the stack below its frame before returning, which
  clears what the hash functions and the WOTS+, XMSS and FORS computations
  left there (FIPS 205, Section 3.1). Each call therefore needs about 18 KB of
  stack: the 16 KB scrub, which is larger than any operation's own use.
* Explicit lengths on every buffer, and AWS-LC's 1/0 return convention.
* `gen_len2` (Algorithm 1) is not computed at runtime; `len2` is in the
  parameter table and checked against Algorithm 1 in the tests.
* HashSLH-DSA supports SHAKE128, with SLH-DSA-SHAKE-128s only, and SHAKE256.

## FIPS status

SLH-DSA is built into the FIPS module but is not yet an approved service:
there are no self-tests or pairwise consistency test yet, so the service
indicator is never set.

## Tests

[slh_dsa_test.cc](slh_dsa_test.cc) runs the NIST ACVP vectors in [kat](kat),
generated from [ACVP-Server](https://github.com/usnistgov/ACVP-Server) JSON by
[kat/acvp_to_filetest.py](kat/acvp_to_filetest.py). Signing is slow, so only a
subset of the signature generation vectors runs by default. To run all of
them:

```bash
crypto_test --gtest_also_run_disabled_tests --gtest_filter='All/SLHDSATest.DISABLED_ACVPSigGenAll/*'
```
