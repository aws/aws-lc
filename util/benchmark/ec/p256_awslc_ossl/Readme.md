Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.<br />
SPDX-License-Identifier: Apache-2.0

# Benchmarking P256 on AWS-LC and OpenSSL
This application performs benchmarking of ECDH and ECDSA on the NIST curve P-256
using both OpenSSL and AWS-LC.

## Assumptions for building the application
* This folder is copied under the same parent directory of `aws-lc`.
* If the parent directory contains an `openssl` folder, it will be preserved.
Otherwise, OpenSSL 1.1.1h will be checked out.
* If the parent directory contains an `openssl` folder and it contains `libcrypto.a`,
it will be preserved. Otherwise, `openssl` will be built.
* Additionally, if `--ossl102` is specified, the two previous points apply to
OpenSSL 1.0.2u where the folder `openssl102/openssl` is created/accessed in the
parent directory.
* The operating system is Linux or MacOS. 
* If the platform is ARMv8 AArch64, specifying the option `--cpu_ticks` will use 
the counter-timer virtual count register, CNTVCT_EL0, to calculate the benchmarks.

## Build and Run
```commandline
./benchmark-build-run.sh
```
Command line options can be passed to the shell script
```commandline
./benchmark-build-run.sh [-t|--test <"ecdhp256"|"ecdsap256">]
                         [-m|--msec <milliseconds>]
                         [--ossl102]
                         [--cpu_ticks]
```
for example,
```commandline
./benchmark-build-run.sh -t "ecdhp256" -i 300
```
