# Post-Quantum Cryptography in AWS-LC

AWS Cryptography focuses research and engineering efforts on the continuation of providing cryptographic security for our customers, while developing new cryptographic systems that exceed current customers’ demands and protect against projected future adversaries. This document contains notes about the design of the Post-Quantum (PQ) Cryptography provided by AWS-LC, and documentation on our current PQ integrations.

In 2023 the U.S. Government passed the [Quantum Computing Cybersecurity Preparedness Act](https://www.congress.gov/bill/117th-congress/house-bill/7535/text), which creates requirements for government agencies to have a cryptographic inventory and plans to migrate to post-quantum (PQ) cryptography. These requirements extend to information technology providers like AWS. The NSA has also announced the [Commercial National Security Algorithm Suite (CNSA) 2.0](https://media.defense.gov/2022/Sep/07/2003071834/-1/-1/0/CSA_CNSA_2.0_ALGORITHMS_.PDF) that provides timelines for Cloud providers wishing to support National Security Systems, with support of PQ by 2025, and exclusively use PQ by 2033.

## Relevant Standards
To support these initiatives, the U.S. Department of Commerce’s National Institute of Standards and Technology (NIST) published three PQ algorithms as part of the Federal Information Processing Standards (FIPS):

- [FIPS 203: Module-Lattice-Based Key-Encapsulation Mechanism Standard](https://csrc.nist.gov/pubs/fips/203/final)
- [FIPS 204: Module-Lattice-Based Digital Signature Standard](https://csrc.nist.gov/pubs/fips/204/final)
- [FIPS 205: Stateless Hash-Based Digital Signature Standard](https://csrc.nist.gov/pubs/fips/205/final)

## AWS-LC Post-Quantum Algorithms

AWS-LC supports the post-quantum Key Encapsulation Mechanisms (KEMs) FIPS 203 ML-KEM and the post-quantum digital signature scheme FIPS 204 ML-DSA. For details on the KEM API and how it can be used please see [README](https://github.com/aws/aws-lc/blob/main/crypto/fipsmodule/kem/README.md).

### FIPS 203: Module-Lattice-Based Key-Encapsulation Mechanism (ML-KEM)

| Algorithm   | Public Key (B)  | Private Key (B)  | Ciphertext(B)  |
|-------------|-----------------|------------------|----------------|
| ML-KEM-512  | 800             | 1632             | 768            |
| ML-KEM-768  | 1184            | 2400             | 1088           |
| ML-KEM-1024 | 1568            | 3168             | 1568           |

These three parameter sets were designed to meet security strength categories defined by NIST. These security strength categories are explained further in SP 800-57, Part 1. Concretely, ML-KEM-512 is claimed to be in security category 1, ML-KEM-768 is claimed to be in security category 3, and ML-KEM-1024 is claimed to be in security category 5.

Performance benchmarks for key generation, encapsulation, and decapsulation are included for ML-KEM within the `speed` tool. To run:

```aws-lc-build % ./tool/bssl speed -filter ML-KEM```

### FIPS 204: Module-Lattice-Based Digital Signature Algorithm (ML-DSA)

| Algorithm  | Public Key (B)  | Private Key (B)  | Signature (B)  |
|------------|-----------------|------------------|----------------|
| ML-DSA-44  | 1312            | 2560             | 2420           |
| ML-DSA-65  | 1952            | 4032             | 3309           |
| ML-DSA-87  | 2592            | 4896             | 4627           |

The parameter set ML-DSA-44 is claimed to be in security strength category 2, ML-DSA-65 is claimed to be in category 3, and ML-DSA-87 is claimed to be in category 5.

## AWS-LC Post-Quantum Integrations

### Hybrid Post-Quantum TLS Specifications

To utilize Post-Quantum key exchange in TLS we recommend using our open-source TLS implementation s2n-tls. However, AWS-LC libssl also supports Post-Quantum key exchange in TLS. Namely, ML-KEM-based cipher suites for TLSv1.3 (draft-kwiatkowski-tls-ecdhe-mlkem)

| Supported Group       | IANA ID (Hex)  | IANA ID (Dec)  |
|-----------------------|----------------|----------------|
| SecP256r1MLKEM768     | 0x11eb         | 4587           |
| SecP384r1MLKEM1024    | 0x11ed         | 4589           |
| X25519MLKEM768        | 0x11ec         | 4588           |

In addition, AWS-LC libssl supports "pure" ML-KEM cipher suites (https://datatracker.ietf.org/doc/html/draft-connolly-tls-mlkem-key-agreement.html).

| Supported Group       | IANA ID (Hex)  | IANA ID (Dec)  |
|-----------------------|----------------|----------------|
| MLKEM512              | 0x0200         | 512            |
| MLKEM768              | 0x0201         | 513            |
| MLKEM1024             | 0x0202         | 514            |

### AWS Java V2 SDK

PQ TLS is also available in the Java V2 SDK. Support for post-quantum algorithms is provided by AWS-LC when configured to use the AWS Common Runtime (CRT) library for TLS.
