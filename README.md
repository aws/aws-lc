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

### Compiler, OS, and CPU support

AWS-LC correctness is tested on a variety of C/C++ compiler, OS, and CPU
combinations. For a complete list of tested combinations see
[tests/ci/Readme.md](https://github.com/aws/aws-lc/blob/main/tests/ci/README.md).
If you use a different combination and would like to make sure we test it,
please open an issue to discuss adding it to our CI.

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
verified on certain platforms with caveats include:
* SHA-2
* HMAC
* AES-GCM
* AES-KWP
* ECDH & ECDSA with curve P-384

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
