# AWS libcrypto (AWS-LC)

[![Join the chat at https://gitter.im/awslabs/aws-lc](https://badges.gitter.im/awslabs/aws-lc.svg)](https://gitter.im/awslabs/aws-lc?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

AWS-LC is a general-purpose cryptographic library maintained by the AWS Cryptography
team for AWS and their customers. It іs based on code from the Google BoringSSL project
and the OpenSSL project.

AWS-LC contains portable C implementations of algorithms needed for TLS and common
applications. For performance critical algorithms, optimized assembly versions are
included for x86 and ARM.

## Quickstart for Amazon Linux 2
Fork AWS-LC on GitHub and run the following commands to build AWS-LC with optimizations
and debug info, run all tests, and install it:
```bash
sudo yum install cmake ninja-build clang perl golang
git clone https://github.com/${YOUR_GITHUB_ACCOUNT_NAME}/aws-lc.git
mkdir aws-lc-build && cd aws-lc-build
cmake -GNinja \
    -DCMAKE_BUILD_TYPE=RelWithDebInfo \
    -DCMAKE_INSTALL_PREFIX=../aws-lc-install \
    ../aws-lc
ninja-build run_tests && ninja-build install
cd ../aws-lc-install/
ls *
```
See [Building.md](https://github.com/awslabs/aws-lc/blob/main/BUILDING.md) for more
information about required dependencies and build options. If you’re interested in
getting involved open an Issue to discuss your plan or talk to us on Gitter.
[Contributing.md](https://github.com/awslabs/aws-lc/blob/main/CONTRIBUTING.md) has
info for how to specifically make the change and get it reviewed by AWS-LC maintainers.
If you just want to use AWS-LC see our existing documentation in the public header
files, if you’re moving your application from OpenSSL see
[Porting_to_AWS-LC.md](https://github.com/awslabs/aws-lc/blob/main/PORTING_TO_AWSLC.md)
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
understanding your use case in an Issue or on Gitter.

### Compiler Compatibility
AWS-LC’s libcrypto is a C library and is tested with a variety of C compilers. To
build libssl and AWS-LC’s tests you will need a C++ compiler. AWS-LC is tested with:

* GCC 4.8.5 to 8.4
* Clang 7 to 10
* Visual Studio 2015

For a complete list of tested compilers see
[tests/ci/Readme.md](https://github.com/awslabs/aws-lc/blob/main/tests/ci/README.md).
If you use another compiler and would like to make sure we maintain support, please
open an issue to discuss adding it to our CI.

### OS Compatibility

AWS-LC should work on any system with a supported compiler. AWS-LC has been written to
support Unix and Windows operating systems. AWS-LC is tested on:
* Amazon Linux 2
* Centos 7
* Ubuntu 18.04 and 20.04
* Fedora 31
* Windows Server 2019

If you use another OS and would like to make sure we maintain support, please open an
issue to discuss adding it to our CI.

### CPU Compatibility

A portable C implementation of all algorithms is included and optimized assembly is
included for some platforms. We test all changes on ARM and x86 platforms. We use
[AWS Graviton processors](https://aws.amazon.com/ec2/graviton/) to test ARMv8 and
Intel CPUs to test x86 and x86-64 compatibility. The
[Intel Software Development Emulator](https://software.intel.com/content/www/us/en/develop/articles/intel-software-development-emulator.html)
is used to test all modern x86 processors.

If you use another CPU and would like to make sure we maintain support, please open an
issue to discuss adding it to our CI.

## AWS-LC safety mechanisms

### Automated testing

Every change is tested with our
[CI](https://github.com/awslabs/aws-lc/blob/main/tests/ci/README.md) that includes
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

If you have any questions about Submitting PR's, Opening Issues, AWS-LC API usage or
any similar topic, we have a public chatroom available here to answer your questions
on [Gitter](https://gitter.im/awslabs/aws-lc).

Otherwise, if you think you might have found a security impacting issue, please instead
follow our Security Notification Process.

## Security issue notifications

If you discover a potential security issue in AWS-LC, we ask that you notify AWS
Security via our
[vulnerability reporting page](https://aws.amazon.com/security/vulnerability-reporting/).
Please do **not** create a public GitHub issue.
