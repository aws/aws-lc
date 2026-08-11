# Security Reporting Policy

## Reporting Security Issues

We kindly ask that you **do not** open a public GitHub issue to report security concerns.

Instead, please submit the issue to the AWS Vulnerability Disclosure Program via [HackerOne](https://hackerone.com/aws_vdp) or send your report via [email](mailto:aws-security@amazon.com).

Amazon Web Services (AWS) practices industry-standard Coordinated Vulnerability Disclosure (CVD) with the goal of reducing adversary advantage while a security vulnerability is being addressed. The [CERT® Guide to Coordinated Vulnerability Disclosure](https://certcc.github.io/CERT-Guide-to-CVD/tutorials/cvd_in_a_nutshell/) provides information about the CVD process, and outlines tools and practices that can help achieve this goal.

For more details, visit the [AWS Vulnerability Reporting Page](http://aws.amazon.com/security/vulnerability-reporting/).

Thank you in advance for collaborating with us to help protect our customers.

## Threat Model

### Shared Responsibility Model

Security is a shared responsibility between AWS-LC and the applications that use it. AWS-LC is a general-purpose cryptographic library, and its consumers include s2n-tls and aws-lc-rs.

AWS-LC is responsible for correctly implementing the cryptographic algorithms and protocols it supports, for keeping secret-dependent operations free of observable timing and memory access variation, for zeroizing key material it owns, and for reporting failures accurately rather than returning a misleading success.

Applications are responsible for the security of the host on which the process loading AWS-LC runs, and for using AWS-LC in a way that achieves their security goals. This includes selecting algorithms, key sizes, and parameters adequate for their own threat model, and calling the API correctly. AWS-LC is a C library with a large OpenSSL compatibility surface, so it offers weaker misuse resistance than an API designed for that purpose.

Given this shared responsibility, the following attacks are considered out of scope for AWS-LC:

* Attacks requiring access to the memory, files, or privileges of the calling process
* Side-channel attacks exploiting CPU or hardware flaws, such as Meltdown and Spectre
* Physical attacks, including fault injection, power analysis, and electromagnetic observation
* Defects in the operating system entropy source, or in the toolchain used to build AWS-LC

If you are unsure whether an issue falls in or out of scope, we encourage you to report it; we'd rather investigate a potential concern than miss a real one. Even for out-of-scope attacks, we may still choose to apply mitigations after weighing the potential cost to performance, maintainability, and complexity. All reported findings will be investigated and mitigations will be decided on a case-by-case basis.

### Adversarial Models

The following adversarial models describe the threats that AWS-LC is designed to defend against. The protection actually achieved depends on the algorithms and parameters the application selects. For example, forward secrecy requires ephemeral key exchange, and resistance to harvest-now-decrypt-later attacks requires post-quantum key establishment.

#### Untrusted Input Adversary

An adversary who controls data an application passes to AWS-LC, such as certificates, signatures, ciphertexts, and encoded keys. This adversary can:

* Send crafted encodings (e.g. DER, PEM) to exploit flaws in parsers
* Supply malformed public keys or group parameters to provoke invalid-curve or small-subgroup behavior
* Tamper with authenticated ciphertexts, or attempt to forge signatures and authentication tags
* Cause denial of service through resource exhaustion

#### Network Adversary

An active attacker with complete control over the network between a TLS client and server using AWS-LC's libssl. In addition to the untrusted input capabilities above, this adversary may:

* Intercept, modify, replay, and inject messages sent on public network channels
* Attempt to downgrade the protocol version or cryptographic parameters negotiated between the peers
* Exploit timing differences practically measurable over a network
* Obtain long-term secrets (e.g. private keys) after a session is complete, or exploit weak long-term keys

#### Co-located Adversary

An unprivileged process on the same host, or a workload sharing the same physical CPU. In addition to the untrusted input and network capabilities above, this adversary may:

* Measure fine-grained timing of cryptographic operations performed on secret data
* Observe microarchitectural state shared with AWS-LC, such as CPU cache access patterns

### Vulnerability Scope

Given the adversarial models above, the following are examples of security-relevant issues that should be reported in accordance with [Reporting Security Issues](#reporting-security-issues):

* Memory safety defects, undefined behavior, integer overflow, or reads of uninitialized memory
* Secret-dependent timing, branching, or memory access in cryptographic operations
* Incorrect algorithm implementations that weaken confidentiality, integrity, or authentication
* Verification routines that accept an invalid signature, authentication tag, or certificate chain
* Failure to zeroize long-term or intermediate secret key material
* Weaknesses in random number generation, such as insufficient seeding or repetition across `fork`
* A security-relevant failure reported to the caller as success

The following are generally not considered vulnerabilities in this project's context:

* Caller-supplied invalid arguments, such as NULL pointers or undersized output buffers
* Use of deprecated OpenSSL compatibility APIs that behave as documented
* Weak algorithms or parameters that the caller explicitly selects
* Differences from OpenSSL behavior documented in the [porting guide](./PORTING.md)
* Findings requiring `BORINGSSL_UNSAFE_FUZZER_MODE` or `BORINGSSL_UNSAFE_DETERMINISTIC_MODE`, which disable checks for testing

Please tell us if a report concerns a FIPS build. The FIPS module is validated separately, and its boundary and platform limitations are described in [FIPS.md](./crypto/fipsmodule/FIPS.md).

## Prenotification Policy

If you package or distribute AWS-LC, or use AWS-LC as part of a large multi-user service, you may be eligible for pre-notification of future AWS-LC releases. Please contact aws-lc-pre-notifications@amazon.com.
