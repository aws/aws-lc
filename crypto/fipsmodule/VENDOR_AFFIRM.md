## FIPS Vendor Affirm

AWS-LC provides a build option `FIPS_VENDOR_AFFIRM_BCM_O_PATH`, which directly uses a prebuilt FIPS module `bcm.o` 
without recompiling bcm.c.  

This build option is developed to support using aws-lc FIPS on **old Linux** platforms(e.g. `CentOS 7`). So 
the support is limited:
* This build option currently only supports `shared` build.
* This build is only tested on `AL2 x86_64(gcc 7.3)`, `Ubuntu 20.04 TLS x86_64(gcc 7.3)` and `CentOS 7 x86_64(gcc 4.9)`.
  * Only `bcm.o` prebuilt on `AL2 x86_64(gcc 7.3)` was used in the tests.

### Usage:
* Launch AWS-LC FIPS test host.

CPU|OS|EC2 AMI|Kernal Version|Instance Type|
------------ | -------------| -------------|-------------|-------------
Intel Xeon Platinum 8275CL|AL2|ami-0aeeebd8d2ab47354|Linux5.4.129-62.227.amzn2.x86_64|c5.metal
* Install build dependencies.
```sh
set -ex && \
yum -y update && yum install -y \
cmake \
ninja-build \
perl \
golang \
gcc \
gcc-c++
```
* In the instance, use below build instruction to generate `bcm.o`.
```sh
# TODO(CryptoAlg-800): add reference to the README that can tell AWS-LC FIPS Security-Policy doc.
# Step 1: get aws-lc code based on AWS-LC FIPS Security-Policy doc.
# Change the directory.
cd aws-lc

# Step2: build aws-lc.
export CC=gcc
export CXX=g++
source tests/ci/common_posix_setup.sh
fips_build_and_test -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=1 -DDISABLE_GETAUXVAL=1

# Step3: the bcm.o is generated under |ABS_PATH_TO_BCM_O|
ABS_PATH_TO_BCM_O="${BUILD_ROOT}/crypto/fipsmodule/bcm.o"
```
* Move the `bcm.o` to the old Linux platform and export the variable `PATH_TO_BCM_O` to tell the absolute path of `bcm.o`.
* Build AWS-LC with below commands.
````sh
# TODO(CryptoAlg-800): add reference to the README that can tell AWS-LC FIPS Security-Policy doc.
# Step 1: get aws-lc code based on AWS-LC FIPS Security-Policy doc.
# Change the directory.
cd aws-lc

# Step2: build aws-lc with prebuilt bcm.o.
source tests/ci/common_posix_setup.sh
fips_build_and_test -DCMAKE_BUILD_TYPE=Release -DFIPS=1 -DBUILD_SHARED_LIBS=1 -DFIPS_VENDOR_AFFIRM_BCM_O_PATH=${PATH_TO_BCM_O}`.
```
