# Post-Quantum Cryptography in AWS-LC

AWS Cryptography focuses research and engineering efforts on the continuation of providing cryptographic security for our customers, while developing new cryptographic systems that exceed current customers’ demands and protect against projected future adversaries. This document contains notes about the design of the Post-Quantum (PQ) Cryptography provided by AWS-LC, and documentation on our current PQ integrations.

In 2023 the U.S. Government passed the [Quantum Computing Cybersecurity Preparedness Act](https://www.congress.gov/bill/117th-congress/house-bill/7535/text), which creates requirements for government agencies to have a cryptographic inventory and plans to migrate to post-quantum (PQ) cryptography. These requirements extend to information technology providers like AWS. The NSA has also announced the [Commercial National Security Algorithm Suite (CNSA) 2.0](https://media.defense.gov/2022/Sep/07/2003071834/-1/-1/0/CSA_CNSA_2.0_ALGORITHMS_.PDF) that provides timelines for Cloud providers wishing to support National Security Systems, with support of PQ by 2025, and exclusively use PQ by 2033.

## Relevant Standards
To support these initiatives, the U.S. Department of Commerce’s National Institute of Standards and Technology (NIST) published three PQ algorithms as part of the Federal Information Processing Standards (FIPS):

- [FIPS 203: Module-Lattice-Based Key-Encapsulation Mechanism Standard](https://csrc.nist.gov/pubs/fips/203/final)
- [FIPS 204: Module-Lattice-Based Digital Signature Standard](https://csrc.nist.gov/pubs/fips/204/final)
- [FIPS 205: Stateless Hash-Based Digital Signature Standard](https://csrc.nist.gov/pubs/fips/205/final)

## AWS-LC Post-Quantum Algorithms

AWS-LC provides two post-quantum Key Encapsulation Mechanisms (KEMs), FIPS 203 ML-KEM and KyberR3, and a post-quantum digital signature scheme FIPS 204 ML-DSA. For details on the KEM API and how it can be used please see [README](https://github.com/aws/aws-lc/blob/main/crypto/fipsmodule/kem/README.md).

### FIPS 203: Module-Lattice-Based Key-Encapsulation Mechanism (ML-KEM)

| Algorithm   | Public Key (B)  | Private Key (B)  | Ciphertext(B)  |
|-------------|-----------------|------------------|----------------|
| ML-KEM-512  | 800             | 1632             | 768            |
| ML-KEM-768  | 1184            | 2400             | 1088           |
| ML-KEM-1024 | 1568            | 3168             | 1568           |

These three parameter sets were designed to meet security strength categories defined by NIST. These security strength categories are explained further in SP 800-57, Part 1. Concretely, ML-KEM-512 is claimed to be in security category 1, ML-KEM-768 is claimed to be in security category 3, and ML-KEM-1024 is claimed to be in security category 5.

Performance benchmarks for key generation, encapsulation, and decapsulation are included for ML-KEM within the `speed` tool. To run:

```aws-lc-build % ./tool/bssl speed -filter ML-KEM```

#### KyberR3

Round 3 Kyber (KyberR3) was added to AWS-LC in September 2021 ([README](https://github.com/aws/aws-lc/blob/main/crypto/kyber/README.md)). Once all existing deployments of Kyber are migrated over to ML-KEM we will be removing support for Kyber from AWS-LC.

### FIPS 204: Module-Lattice-Based Digital Signature Algorithm (ML-DSA)

| Algorithm  | Public Key (B)  | Private Key (B)  | Signature (B)  |
|------------|-----------------|------------------|----------------|
| ML-DSA-44  | 1312            | 2560             | 2420           |
| ML-DSA-65  | 1952            | 4032             | 3309           |
| ML-DSA-87  | 2592            | 4896             | 4627           |

The parameter set ML-DSA-44 is claimed to be in security strength category 2, ML-DSA-65 is claimed to be in category 3, and ML-DSA-87 is claimed to be in category 5.

## AWS-LC Post-Quantum Integrations

### Hybrid Post-Quantum TLS Specifications

To utilize Post-Quantum key exchange in TLS we recommend using our open-source TLS implementation s2n-tls that now supports Hybrid key exchange in TLS 1.3 (draft-ietf-tls-hybrid-design). s2n-tls also provides support for Post-Quantum hybrid ECDHE-MLKEM Key Agreement for TLSv1.3 (draft-kwiatkowski-tls-ecdhe-mlkem) with a proposal for new key share identifies for x25519 and ML-KEM-768.


| Supported Group       | IANA ID (Hex)  | IANA ID (Dec)  |
|-----------------------|----------------|----------------|
| x25519_kyber512       | 0x2f39         | 12089          |
| p256_kyber512         | 0x2f3a         | 12090          |
| X25519Kyber768Draft00 | 0x6399         | 25497          |
| X25519Kyber768Draft00 | 0x639a         | 25498          |
| SecP256r1MLKEM768     | 0x11eb         | 4587           |
| X25519MLKEM768        | 0x11ec         | 4588           |

Note that pre-standard groups (those that include Kyber)  will stop being supported after the Kyber deprecation described above.

### AWS Java V2 SDK

PQ TLS is also available in the Java V2 SDK. Support for post-quantum algorithms is provided by AWS-LC when configured to use the AWS Common Runtime (CRT) library for TLS.
