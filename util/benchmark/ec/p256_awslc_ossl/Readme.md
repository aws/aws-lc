# Benchmarking P256 on AWS-LC and OpenSSL
This application performs benchmarking of ECDH and ECDSA on the NIST curve P-256 
using both OpenSSL and AWS-LC.

## Assumptions
* This folder is copied under the same parent directory of `aws-lc`.
* If the parent directory contains an `openssl` folder, it will be preserved.
Otherwise, OpenSSL 1.1.1h will be checked out.
* If the parent directory contains an `openssl` folder and it contains `libcrypto.a`, 
it will be preserved. Otherwise, `openssl` will be built.
* The operating system is Linux or MacOS

## Build and Run
```commandline
./benchmark-build-run.sh
```
Command line options can be passed to the shell script
```commandline
./benchmark-build-run.sh [-t|--test <"ecdhp256"|"ecdsap256">] \
                         [-i|--iterations <iterations>]
```
for example,
```commandline
./benchmark-build-run.sh -t "ecdhp256" -i 300
```

