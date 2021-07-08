# Tools for AWS-LC
In addition to the tools provided by BoringSSL, AWS-LC features enhanced benchmarking tools compatible with OpenSSL and BoringSSL in order to help facilitate 1-1 performance comparisons.

## Benchmarking Tools
In addition to `bssl speed`, AWS-LC will generate three additional benchmarking tools when provided with corresponding compiler flags. These tools take the same arguments as the BoringSSL speed tool does.

Additionally, the speed tool now prints a message when it is benchmarking a non-release build of AWS-LC.

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