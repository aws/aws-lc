# Tools for AWS-LC
AWS-LC features enhanced benchmarking tools compatible with OpenSSL and BoringSSL in order to help facilitate 1-1 performance comparisons.

## Speed tool

The speed subtool of `bssl` runs a performance test for a number of cryptographic operations (which can be implemented using different APIs). Each operation is mapped to a "filter name". Below we list the filter name, which operation it maps to and which API is used to implement it.

|  Filter name  |  Description  | Function family |
| ------------- | ------------- | -------------
| EVP ECDH {P-224, P-256, P-384, P-521, secp256k1, X25519} | ECDHE key agreement for one party | EVP |
| ECDH {P-224, P-256, P-384, P-521, secp256k1} | ECDHE key agreement for one party | EC |
| Generate {P-224, P-256, P-384, P-521, secp256k1} | Elliptic curve key generation | EVP |
| ECMUL {P-224, P-256, P-384, P-521, secp256k1} | Elliptic curve arbitrary scalar multiplication | EC |

## Benchmarking Tools
When compiled, AWS-LC will generate separate benchmarking tools when provided with corresponding compiler flags. These tools take the same arguments as `bssl speed` tool.

This tool also supports building a newer benchmark with an older version of AWS-LC's code: e.g.
build and install AWS-LC FIPS from 2021 but run the latest benchmark tool from main. To benchmark the AWS-LC libcrypto
from the current folder it is recommended to run `bssl speed` which executes the same code as other benchmarks.

Additionally, the speed tool now prints a message when it is benchmarking a non-release build of AWS-LC instead of a release build of the project.

### Usage
Running each tool without any options (e.g. `./awslc_bm`) will run all available benchmarks for 1 second each.

Additionally, there are a number of arguments that enable different functionality:
* `-filter` provides a filter on the benchmarking tests to be run.
* `-timeout` sets the number of seconds each test is run for (default 1).
* `-threads` is a comma-separated list of thread counts to run multithreaded benchmarks (default is "1,2,4,8,16,32,64")
* `-chunks` is a comma-separated list of input sizes to run tests at (default is "
  "16,256,1350,8192,16384)
* `-json` has the tool print the output of each benchmark in JSON format.

For example, `./awslc_bm -filter AES -timeout 10 -chunks 16, 256, -json` will run all AES-related tests with input sizes of 16 and 256 for 10 seconds, and output the results in JSON format.

## Comparison Setup
The AWS-LC benchmark supports building and running with other common libcryptos.
Build and install the other libcryptos you would like to test with locally, for 
example building AWS-LC 2022 FIPS branch and OpenSSL 3.3 to compare with AWS-LC
main branch:

```bash
mkdir ~/aws-lc-benchmark && pushd ~/aws-lc-benchmark

git clone -b openssl-3.3 --depth 1 https://github.com/openssl/openssl.git openssl-3.3-src
pushd openssl-3.3-src
./config --prefix="${HOME}/aws-lc-benchmark/openssl-3.3-install" --openssldir="${HOME}/aws-lc-benchmark/openssl-3.3-install"
make -j
make install_sw
popd


git clone -b fips-2022-11-02 --depth 1 https://github.com/aws/aws-lc.git aws-lc-fips-src
pushd aws-lc-fips-src
cmake -DCMAKE_INSTALL_PREFIX="${HOME}/aws-lc-benchmark/aws-lc-fips-install" -DCMAKE_BUILD_TYPE=Release -DFIPS=1 -DBUILD_SHARED_LIBS=1
make -j install
popd && popd
```

To build the main branch speed.cc against other libraries pass in the
BENCHMARK_LIBS option when running CMake. BENCHMARK_LIBS is a list of tuples,
the format is `executable_name:install_path`. `executable_name` is the name for
the benchmark that AWS-LC will build with whatever library is in `install_path`.
Multiple libraries can be specified with a semicolon between them:
`executable1_name:executable1_install_path;executable1_name:executable1_install_path;`

To build AWS-LC main speed.cc against the two previously built libcrypto libraries
(AWS-LC FIPS 2022 and OpenSSL 3.3):
```bash
pushd ~/aws-lc-benchmark
git clone -b main --depth 1 https://github.com/aws/aws-lc.git aws-lc-main-src
pushd aws-lc-main-src
cmake -DCMAKE_BUILD_TYPE=Release -DBENCHMARK_LIBS="\
aws-lc-fips-2022:${HOME}/aws-lc-benchmark/aws-lc-fips-install;\
openssl-3-3:${HOME}/aws-lc-benchmark/openssl-3.3-install;"
make -j
popd && popd
```

This will build 3 relevant binaries:
* `~/aws-lc-benchmark/aws-lc-main-src/tool/bssl` is the complete tool build with the main branch of code, `speed` is required to run the benchmark 
* `~/aws-lc-benchmark/aws-lc-main-src/tool/aws-lc-fips-2022` is the main branch of speed.cc built with the AWS-LC FIPS 2022 install
* `~/aws-lc-benchmark/aws-lc-main-src/tool/openssl-3-3` is the main branch of speed.cc built with the OpenSSL 3.3 install

Not all benchmarks will be available with all libraries, for example OpenSSL 3.3
does not support ML-KEM.

```
~/aws-lc-benchmark/aws-lc-main-src/tool/bssl speed -filter P-256
~/aws-lc-benchmark/aws-lc-main-src/tool/aws-lc-fips-2022 -filter P-256
~/aws-lc-benchmark/aws-lc-main-src/tool/openssl-3-3 -filter P-256
```

### Expected Directory Structure
Additionally, the benchmarking tools expects specific directory structures for the provided install locations for each
library. Each library has its own instructions for building and installing their libcrypto, and once installed to that 
directory you can simply use the appropriate `INSTALL_DIR` flag to point the benchmarking tool to it. Each library is
expected to provide the following directory structure:

```
-install_dir/
--include/
---openssl/
--lib/
---libcrypto
or
--lib64/
---libcrypto
```

The benchmark tool can be built using dynamic/shared libraries (.so, .dynalib, or .dll) or static archives (.a, or .lib).