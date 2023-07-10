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

The `awslc_bm` tool is expected to be used when benchmarking an installation of AWS-LC with a different speed tool: e.g.
build and install AWS-LC FIPS from 2021 but run the latest benchmark tool from main. To benchmark the AWS-LC libcrypto
from the current folder it is recomended to run `bssl speed` which executes the same code as other benchmarks: e.g. 
`ossl_1_1_bm`.

Additionally, the speed tool now prints a message when it is benchmarking a non-release build of AWS-LC instead of a release build of the project.

### Usage
Running each tool without any options (e.g. `./awslc_bm`) will run all available benchmarks for 1 second each.

Additionally, there are a number of arguments that enable different functionality:
* `-filter` provides a filter on the benchmarking tests to be run.
* `-timeout` sets the number of seconds each test is run for (default 1).
* `-chunks` is a comma-separated list of input sizes to run tests at (default is "
  "16,256,1350,8192,16384)
* `-json` has the tool print the output of each benchmark in JSON format.

For example, `./awslc_bm -filter AES -timeout 10 -chunks 16, 256, -json` will run all AES-related tests with input sizes of 16 and 256 for 10 seconds, and output the results in JSON format.

## Setup
In order to build the above-mentioned benchmarking tools, absolute paths to each libaries' install location must be provided via compiler flags.

### Compiler Flags
|  Tool Name  |  Compiler Flag  |
| ------------- | ------------- |
 | bssl speed | (none) | 
| awslc_bm | -DAWSLC_INSTALL_DIR |
| bssl_bm | -DBORINGSSL_INSTALL_DIR |
| ossl_1_0_bm | -DOPENSSL_1_0_INSTALL_DIR |
| ossl_1_1_bm | -DOPENSSL_1_1_INSTALL_DIR |
| ossl_3_0_bm | -DOPENSSL_3_0_INSTALL_DIR |

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