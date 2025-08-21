# AWS libcrypto (AWS-LC)

AWS-LC is a general-purpose cryptographic library maintained by the AWS Cryptography
team for AWS and their customers. It іs based on code from the Google BoringSSL project
and the OpenSSL project.

AWS-LC contains portable C implementations of algorithms needed for TLS and common
applications. For performance critical algorithms, optimized assembly versions are
included for x86 and ARM.

## Quickstart for Amazon Linux 2

AWS-LC’s libcrypto is a C library and needs a C compiler. AWS-LC's libssl is a
C++ library and needs a C++ compiler.

Fork AWS-LC on GitHub and run the following commands to build AWS-LC with optimizations
and debug info, run all tests, and install it:
```bash
sudo yum install cmake3 ninja-build clang perl golang
git clone https://github.com/${YOUR_GITHUB_ACCOUNT_NAME}/aws-lc.git
mkdir aws-lc-build && cd aws-lc-build
cmake3 -GNinja \
    -DCMAKE_BUILD_TYPE=RelWithDebInfo \
    -DCMAKE_INSTALL_PREFIX=../aws-lc-install \
    ../aws-lc
ninja-build run_tests && ninja-build install
cd ../aws-lc-install/
ls *
```
See [Building.md](https://github.com/aws/aws-lc/blob/main/BUILDING.md) for more
information about required dependencies and build options. If you’re interested in
getting involved [open an issue](https://github.com/aws/aws-lc/issues/new/choose) to discuss your plan.
[Contributing.md](https://github.com/aws/aws-lc/blob/main/CONTRIBUTING.md) has
info for how to specifically make the change and get it reviewed by AWS-LC maintainers.
If you just want to use AWS-LC see our existing documentation in the public header
files, if you’re moving your application from OpenSSL see
[Porting_to_AWS-LC.md](https://github.com/aws/aws-lc/blob/main/PORTING_TO_AWSLC.md)
for more information.

## Why AWS-LC?

AWS-LC's goal is to maintain a secure libcrypto that is compatible with software and
applications used at AWS. AWS-LC also serves as the new home for the AWS Cryptography
team to publish open source contributions and enhancements that are submitted to
other libcrypto projects.

## AWS-LC features

### API Compatibility

AWS-LC is compatible with the majority of OpenSSL’s APIs to make it easy to use with
existing applications. We’re open to discussing adding missing functionality and
understanding your use case in an [issue](https://github.com/aws/aws-lc/issues/new/choose).

### Algorithm optimization support

A portable C implementation of all algorithms is included and optimized assembly
implementations of select algorithms is included for some x86 and Arm CPUs. We
use [AWS Graviton processors](https://aws.amazon.com/ec2/graviton/) to test
ARMv8 optimizations and Intel CPUs to test x86 and x86-64 optimizations.

The [Intel Software Development Emulator](https://software.intel.com/content/www/us/en/develop/articles/intel-software-development-emulator.html)
is used to run tests on many different x86 processors.

If you use another CPU and would like to make sure we test it or discuss adding
an assembly optimized algorithm implementation, please open an issue to discuss
adding it to our CI.

## Platform Support

AWS-LC correctness is tested on a variety of *platforms* (i.e., OS/CPU combinations).  
The following is an overview of the platforms we actively support or are 
known to be of interest to our community. 

If you use a platform not listed below and would like to request it be added to our CI,
please open an [issue](https://github.com/aws/aws-lc/issues/new/choose) for discussion.
Regardless of our support level for a particular platform, we will gladly consider contributions that 
improve or extend our support.

### Supported Platforms

The following platforms are actively tested in our CI pipeline. A few of these platforms are tested across 
multiple compilers or compiler versions. For each pull request, the proposed change is validated to confirm that it 
successfully builds and tests pass for these platform. 
A more complete description of our test setup can be found in the 
[CI README](https://github.com/aws/aws-lc/blob/main/tests/ci/README.md).

| OS      | CPU     | 
|---------|---------|
| Linux   | x86     |
| Linux   | x86-64  |
| Linux   | aarch64 |
| Windows | x86-64  |
| macOS   | x86-64  |
| macOS   | aarch64 |
| Android | aarch64 |
| Linux   | ppc     |
| Linux   | ppc64   |
| Linux   | ppc64le |

### Other platforms

The platforms listed below are of interest to us or to our community. However, problems reported 
against them might not be prioritized for immediate action by our team. We welcome contributions 
that improve the experience for consumers on these platforms.

| OS        | CPU         |
|-----------|-------------|
| Android   | arm32       |
| iOS       | aarch64     |
| Linux     | arm32       |
| Linux     | loongarch64 |
| Linux     | risc-v64    |
| Linux     | s390x       |
| Windows   | aarch64     |
| OpenBSD   | x86-64      |
| FreeBSD   | x86-64      |

### FIPS Compliance

For information about FIPS compliance, building AWS-LC in FIPS mode, and platform limitations, see [crypto/fipsmodule/FIPS.md](crypto/fipsmodule/FIPS.md).

### Post-Quantum Cryptography

Details on the post-quantum algorithms supported by AWS-LC can be found at [PQREADME](https://github.com/aws/aws-lc/tree/main/crypto/fipsmodule/PQREADME.md).

## AWS-LC safety mechanisms

### Automated testing

Every change is tested with our
[CI](https://github.com/aws/aws-lc/blob/main/tests/ci/README.md) that includes
positive and negative unit tests, fuzz tests, Sanitizers
([Address](https://clang.llvm.org/docs/AddressSanitizer.html),
[Memory](https://clang.llvm.org/docs/MemorySanitizer.html),
[Control flow integrity](https://clang.llvm.org/docs/ControlFlowIntegrity.html),
[Thread](https://clang.llvm.org/docs/ThreadSanitizer.html), and
[Undefined behavior](https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html)),
[Valgrind](https://valgrind.org/), and Formal Verification.

### Formal Verification

Portions of AWS-LC have been formally verified in
[AWS-LC Formal Verification](https://github.com/awslabs/aws-lc-verification),
the checks are run in AWS-LC’s CI on every change. The algorithms that have been
verified on certain CPUs with caveats include:
| Algorithm | Parameters | CPUs |
| ----------| ------------| -----------
| SHA-2 | 384, 512 | SandyBridge+ |
| SHA-2 | 384 | neoverse-n1, neoverse-v1 |
| HMAC | with <nobr>SHA-384</nobr> | SandyBridge+ |
| <nobr>AES-KW(P)</nobr> | 256 | SandyBridge+ |
| <nobr>AES-GCM</nobr> | 256 | SandyBridge+ |
<!--- | Elliptic Curve Keys and Parameters | with <nobr>P-384</nobr> | SandyBridge+ | --->
<!--- | ECDSA | with <nobr>P-384</nobr>, <nobr>SHA-384</nobr> | SandyBridge+ | --->
<!--- | ECDH | with <nobr>P-384</nobr> | SandyBridge+ | --->
<!--- | HKDF | with <nobr>HMAC-SHA384</nobr> | SandyBridge+ | --->

The CPUs for which code is verified are defined in the following table.

| CPUs        | Description |
| --------------- | ------------|
| SandyBridge+ | x86-64 with AES-NI, CLMUL, and AVX.
| neoverse-n1 | aarch64 without SHA512.
| neoverse-v1 | aarch64 with SHA512.

For more details on verified API functions, caveats and technology used, check the [AWS-LC Formal Verification](https://github.com/awslabs/aws-lc-verification) repository.

In addition, we use assembly from [s2n-bignum](https://github.com/awslabs/s2n-bignum) to implement algorithms or sub-routines for x86_64 and aarch64. These functions are formally verified in HOL Light. See the following table for detail.

| Algorithms | Functions | CPUs |
| ----------| ------------| ------------|
| RSA | `montgomery_s2n_bignum_mul_mont` | aarch64 |
| P-256 | `bignum_montinv_p256`, `p256_montjscalarmul_selector` | aarch64, x86_64 |
| P-384 | `bignum_add_p384`, `bignum_sub_p384`, `bignum_neg_p384`, `bignum_tolebytes_6`, `bignum_fromlebytes_6`, `bignum_to_mont_p384_selector`, `bignum_deamont_p384_selector`, `bignum_montmul_p384_selector`, `bignum_montsqr_p384_selector`, `bignum_nonzero_6`, `bignum_montinv_p384`, `p384_montjdouble_selector`, `p384_montjscalarmul_selector` | aarch64, x86_64 |
| P-521 | `bignum_add_p521`, `bignum_sub_p521`, `bignum_neg_p521`, `bignum_tolebytes_p521`, `bignum_fromlebytes_p521`, `bignum_mul_p521_selector`, `bignum_sqr_p521_selector`, `bignum_inv_p521`, `p521_jdouble_selector`, `p521_jscalarmul_selector` | aarch64, x86_64 |
| X25519 | `curve25519_x25519_byte_selector`, `curve25519_x25519base_byte_selector` | aarch64, x86_64 |
| Ed25519 | `bignum_mod_n25519`, `bignum_neg_p25519`, `bignum_madd_n25519_selector`, `edwards25519_encode`, `edwards25519_decode_selector`, `edwards25519_scalarmulbase_selector`, `edwards25519_scalarmuldouble_selector` | aarch64, x86_64 |

## Have a Question?

We use [GitHub Issues](https://github.com/aws/aws-lc/issues) for managing feature requests,
bug reports, or questions about AWS-LC API usage.

If you think you might have found a security impacting issue, please instead
follow our [Security Notification Process](#security-issue-notifications).

## Security issue notifications

If you discover a potential security issue in AWS-LC, we ask that you notify AWS
Security via our
[vulnerability reporting page](https://aws.amazon.com/security/vulnerability-reporting/).
Please do **not** create a public GitHub issue.

If you package or distribute AWS-LC, or use AWS-LC as part of a large multi-user service, you may be eligible for pre-notification of future AWS-LC releases. Please contact aws-lc-pre-notifications@amazon.com.


