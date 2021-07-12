# Tools for AWS-LC
AWS-LC features enhanced benchmarking tools compatible with OpenSSL and BoringSSL in order to help facilitate 1-1 performance comparisons.

## Benchmarking Tools
When compiled, AWS-LC will generate three benchmarking tools when provided with corresponding compiler flags. These tools take the same arguments as the BoringSSL speed tool does.

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
| awslc_bm | -DAWSLC_INSTALL_DIR |
| bssl_bm | -DBORINGSSL_INSTALL_DIR |
| ossl_bm | -DOPENSSL_INSTALL_DIR |

### Expected Directory Structure
Additionally, the benchmarking tools expects specific directory structures for the provided install locations for each library. Namely, each library must be built into a folder called `build` located in the base directory of the library.

**AWS-LC**
```
-awslc_install_dir/
--include/
```

**BoringSSL**
```
-boringssl_install_dir/
--include/
--build/
---crypto/
----libcrypto.a
```

**OpenSSL**
```
-openssl_install_dir/
--include/
--build/
---lib/
----libcrypto.a
```