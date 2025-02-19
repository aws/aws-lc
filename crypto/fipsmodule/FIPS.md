# FIPS 140-3

A submodule of AWS-LC, referred to here as the “FIPS module”, is periodically submitted for FIPS validation from the National Institute for Standards and Technology (NIST). This document contains notes about the design of our FIPS module and documentation on performing certain FIPS-related tasks. This document is not a substitute for reading our latest official [FIPS Security Policy](https://csrc.nist.gov/CSRC/media/projects/cryptographic-module-validation-program/documents/security-policies/140sp4631.pdf). Please note that we cannot answer questions about FIPS, nor about using AWS-LC in a FIPS-compliant manner. Please consult with an [accredited CMVP lab](http://csrc.nist.gov/groups/STM/testing_labs/) or a compliance specialist on these topics.

## Validations

NIST has awarded the FIPS module of AWS-LC its validation certificate as a Federal Information Processing Standards (FIPS) 140-3, level 1, cryptographic module.

* AWS-LC-FIPS v1.0: certificate [#4631](https://csrc.nist.gov/projects/cryptographic-module-validation-program/certificate/4631) - [security policy](https://csrc.nist.gov/CSRC/media/projects/cryptographic-module-validation-program/documents/security-policies/140sp4631.pdf)
* AWS-LC-FIPS v2.0 (dynamic library): certificate [#4759](https://csrc.nist.gov/projects/cryptographic-module-validation-program/certificate/4759) - [security policy](https://csrc.nist.gov/CSRC/media/projects/cryptographic-module-validation-program/documents/security-policies/140sp4759.pdf)
* AWS-LC-FIPS v2.0 (static library): certificate [#4816](https://csrc.nist.gov/projects/cryptographic-module-validation-program/certificate/4816) - [security policy](https://csrc.nist.gov/CSRC/media/projects/cryptographic-module-validation-program/documents/security-policies/140sp4816.pdf)

NIST has also awarded SP 800-90B validation certificate for our CPU Jitter Entropy Source.

1. 2023-09-14: entropy certificate [#E77](https://csrc.nist.gov/projects/cryptographic-module-validation-program/entropy-validations/certificate/77), [public use document](https://csrc.nist.gov/CSRC/media/projects/cryptographic-module-validation-program/documents/entropy/E77_PublicUse.pdf)

### Modules in Process

The modules below have been tested by an accredited lab and have been submitted to NIST for FIPS 140-3 validation.
* AWS-LC Cryptographic Module (dynamic): [Review Pending](https://csrc.nist.gov/Projects/Cryptographic-Module-Validation-Program/Modules-In-Process/Modules-In-Process-List) - [draft security policy](./policydocs/DRAFT-140-3-AmazonSecurityPolicy-NetOS-dynamic.pdf)
* AWS-LC-FIPS v3.0 (static): [Review Pending](https://csrc.nist.gov/Projects/Cryptographic-Module-Validation-Program/Modules-In-Process/Modules-In-Process-List) - [draft security policy](./policydocs/DRAFT-140-3-AmazonSecurityPolicy-3.0.0-static.pdf)
* AWS-LC-FIPS v3.0 (dynamic): [Review Pending](https://csrc.nist.gov/Projects/Cryptographic-Module-Validation-Program/Modules-In-Process/Modules-In-Process-List) - [draft security policy](./policydocs/DRAFT-140-3-AmazonSecurityPolicy-3.0.0-dynamic.pdf)

## RNG design

FIPS 140-3 requires the use of one of its Deterministic Random Bit Generators (DRBGs, also called Pseudo-Random Number Generators, PRNGs). In AWS-LC, we use CTR-DRBG with AES-256 exclusively from which `RAND_bytes` produces its output. The DRBG state is kept in a thread-local structure and is seeded using the configured entropy source. The CTR-DRBG is periodically reseeded from the entropy source during calls to `RAND_bytes`. The rest of the library obtains random data from `RAND_bytes`.

The FIPS DRBGs allow “additional input” to be fed into a given call. We use this feature to be as robust as possible against state duplication from process forks and VM copies. A caller may supply bytes that will be XOR'd into the generated “additional input” using  `RAND_bytes_with_additional_data`.

FIPS requires that RNG state be zeroed when the process exits. In order to implement this, all per-thread RNG states are tracked in a linked list and a [destructor function](https://github.com/aws/aws-lc/blob/eb58525ce1704c5183af9aa28f50945c11fe5a0d/crypto/fipsmodule/rand/rand.c#L251) is included which clears them. In order for this to be safe in the presence of threads, a lock is used to stop all other threads from using the RNG once this process has begun. Thus the main thread exiting may cause other threads to deadlock, and drawing on entropy in a destructor function may also deadlock.

## AWS-LC-FIPS v1.0 Entropy Source

The AWS-LC-FIPS v1.0 entropy source is CPU Jitter Entropy ([version 3.1.0](https://github.com/aws/aws-lc/blob/fips-2021-10-20/third_party/jitterentropy/README.md)).  For technical details on how CPU Jitter generates entropy, please refer to the [Jitter RNG homepage](https://www.chronox.de/jent/index.html).   

## AWS-LC-FIPS v2.0 Entropy Source

The AWS-LC-FIPS v2.0 module uses passive entropy by default and the specific entropy gathering mechanism depends on the operating environment installed on. CPU Jitter Entropy ([version 3.4.0](https://github.com/aws/aws-lc/blob/fips-2022-11-02/third_party/jitterentropy/README.md)) can still be enabled by using the `ENABLE_FIPS_ENTROPY_CPU_JITTER=ON` flag.

## Breaking known-answer and continuous tests

Each known-answer test (KAT) uses a unique, random input value. `util/fipstools/break-kat.go` contains a listing of those values and can be used to corrupt a given test in a binary. Since changes to the KAT input values will invalidate the integrity test, `BORINGSSL_FIPS_BREAK_TESTS` can be defined in `fips_break_tests.h` to disable it for the purposes of testing.

Some FIPS tests cannot be broken by replacing a known string in the binary. For those, when `BORINGSSL_FIPS_BREAK_TESTS` is defined, the environment variable `BORINGSSL_FIPS_BREAK_TEST` can be set to one of a number of values in order to break the corresponding test:

1. `RSA_PWCT`
2. `ECDSA_PWCT`
3. `EDDSA_PWCT`
4. `MLKEM_PWCT`
5. `MLDSA_PWCT`

## Running ACVP tests

See `util/fipstools/acvp/ACVP.md` for details of how ACVP testing is done.

## Integrity Test

FIPS-140 mandates that a module calculate an HMAC of its own code in a constructor function and compare the result to a known-good value. Typical code produced by a C compiler includes large numbers of relocations: places in the machine code where the linker needs to resolve and inject the final value of a symbolic expression. These relocations mean that the bytes that make up any specific bit of code generally aren't known until the final link has completed. Additionally, because of shared libraries and [ASLR](https://en.wikipedia.org/wiki/Address_space_layout_randomization), some relocations can only be resolved at run-time, and thus targets of those relocations vary even after the final link.

AWS-LC is linked (often statically) into a large number of binaries. It would be a significant cost if each of these binaries had to be post-processed in order to calculate the known-good HMAC value. We would much prefer if the value could be calculated, once, when AWS-LC itself is compiled. In order for the value to be calculated before the final link, there can be no relocations in the hashed code and data. 

We describe below how we build C and assembly code in order to produce a binary file containing the code and data for the FIPS module without that code having any relocations. There are two build configurations supported: **static** and **shared**. The shared build produces `libcrypto.so`, which includes the FIPS module and is significantly more straightforward and so is described first.

### Linux Shared build

First, all the C source files for the module are compiled as a single unit by compiling a single source file that `#include`s them all (this is `[bcm.c](https://github.com/aws/aws-lc/blob/main/crypto/fipsmodule/bcm.c)`). This, along with some assembly sources, comprise the FIPS module.

The object files resulting from compiling/assembling those files are linked in partial-linking mode with a [linker script](https://github.com/aws/aws-lc/blob/main/crypto/fipsmodule/gcc_fips_shared.lds) that causes the linker to insert symbols marking the beginning and end of the text and rodata sections. The linker script also discards other types of data sections to ensure that no unhashed data is used by the module.

One source of unhashable data is `rel.ro` sections, which contain data that includes function pointers. Since these function pointers are absolute, they are written by the dynamic linker at run-time and so must be eliminated. The pattern that causes them is when we have a static `EVP_MD` or `EVP_CIPHER` object thus, inside the module, this pattern is changed to instead reserve space in the [BSS](https://en.wikipedia.org/wiki/.bss) for the object, and to add a `CRYPTO_once_t` to protect its initialization.

Once the partially-linked result is linked again with other parts of libcrypto, to produce `libcrypto.so`, the contents of the module are fixed, as required. The module code uses the linker-added symbols to find its code and data at run-time and hashes them upon initialization. The result is compared against a value stored inside `libcrypto.so`, but outside of the module. That value will, initially, be incorrect, but `inject-hash.go` injects the correct value.

### Windows Shared build

The Shared Windows FIPS integrity test differs in two key ways:

1. How the start and end of the module are marked
2. How the correct integrity hash is calculated

Microsoft Visual C compiler (MSVC) does not support linker scripts that add symbols to mark the start and end of the text and rodata sections, as is done on Linux. Instead, `fips_shared_library_marker.c` is compiled twice to generate two object files that contain start/end functions and variables. MSVC `pragma` segment definitions are used to place the markers in specific sections (e.g. `.fipstx$a`). This particular name format uses [Portable Executable Grouped Sections](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format#grouped-sections-object-only) to control what section the code is placed in and the order within the section. With the start and end markers placed at `$a` and `$z` respectively, BCM puts everything in the `$b` section. When the final crypto.dll is built, all the code is in the `.fipstx` section, all data is in `.fipsda`, all constants are in `.fipsco`, all uninitialized items in `.fipsbs`, and everything is in the correct order.
The process to generate the expected integrity fingerprint is also different from Linux:

1. Build the required object files once: `bcm.obj` from `bcm.c` and the start/end object files 
    1. `bcm.obj` places the power-on self tests in the `.CRT$XCU` section which is run automatically by the Windows Common Runtime library (CRT) startup code
2. Use MSVC's `lib.exe` to combine the start/end object files with `bcm.obj` to create the static library `bcm.lib`. 
    1. MSVC does not support combining multiple object files into another object file like the Apple build.
3. Build `fipsmodule` which contains the placeholder integrity hash
4. Build `precrypto.dll` with `bcm.obj` and `fipsmodule`
5. Build the small application `fips_empty_main.exe` and link it with `precrypto.dll`
6. `capture-hash.go` runs `fips_empty_main.exe`
    1. The CRT runs all functions in the `.CRT$XC*` sections in order starting with `.CRT$XCA`
    2. The BCM power-on tests are in `.CRT$XCU` and are run after all other Windows initialization is complete
    3. BCM calculates the correct integrity value which will not match the placeholder value. Before aborting the process the correct value is printed
    4. `capture-hash.go` reads the correct integrity value and writes it to `generated_fips_shared_support.c`
7. `generated_fipsmodule` is built with `generated_fips_shared_support.c`
8. `crypto.dll` is built with the same original `bcm.lib` and `generated_fipsmodule`

### Linux Static build

The static build cannot depend on the shared-object linkage to resolve relocations and thus must take another path.
As with the shared build, all the C sources are built into a single compilation unit. The `-fPIC` flag is used to cause the compiler to use [IP-relative addressing](https://en.wikipedia.org/wiki/Position-independent_code) in many (but not all) cases.

The unit is built with the `-S` flag to instruct the compiler to produce a textual assembly file rather than a binary object file.
The textual assembly file is then processed by a “delocator” script to merge in assembly implementations of some primitives and to eliminate the remaining sources of relocations.

#### Redirector functions

The most obvious cause of relocations are out-calls from the module to non-cryptographic functions outside of the module. Most obviously these include `malloc`, `memcpy` and other libc functions, but also include calls to support code in AWS-LC such as functions for managing the error queue.

Offsets to these functions cannot be known until the final link because only the linker sees the object files containing them. Thus calls to these functions are rewritten into an IP-relative jump to a *redirector* function. The redirector functions contain a single jump instruction to the real function and are placed outside of the module and are thus not hashed (see diagram).
In this diagram, the integrity check hashes from `module_start` to `module_end`. Since this does not cover the jump to `memcpy`, it's fine that the linker will poke the final offset into that instruction.

![module structure](./intcheck1.png)

#### Read-only data

Normally read-only data is placed in an `.rodata` segment that doesn't get mapped into memory with execute permissions. However, the offset of the data segment from the text segment is another thing that isn't determined until the final link. In order to fix data offsets before the link, read-only data is simply placed in the module's `.text` segment. This might make building ROP chains easier for an attacker, but so it goes.

Data containing function pointers remains an issue. The source-code changes described above for the shared build apply here too, but no direct references to a BSS section are possible because the offset to that section is not known at compile time. Instead, the script generates functions outside of the module that return pointers to these areas of memory—they effectively act like special-purpose malloc calls that cannot fail.

#### Read-write data

Mutable data is a problem. It cannot be in the text segment because the text segment is mapped read-only. If it's in a different segment then the code cannot reference it with a known, IP-relative offset because the segment layout is only fixed during the final link.
In order to allow this we use a similar design to the redirector functions: the code references a symbol that's in the text segment, but out of the module and thus not hashed. A relocation record is emitted to instruct the linker to poke the final offset to the variable in that location. Thus the only change needed is an extra indirection when loading the value.

#### Other transforms

The delocator script performs a number of other transformations which are worth noting but do not warrant their own discussions:

1. It duplicates each global symbol with a local symbol that has `_local_target` appended to the name. References to the global symbols are rewritten to use these duplicates instead. Otherwise, although the generated code uses IP-relative references, relocations are emitted for global symbols in case they are overridden by a different object file during the link.
2. Various sections, notably `.rodata`, are moved to the `.text` section, inside the module, so module code may reference it without relocations.
3. For each BSS symbol, it generates a function named after that symbol but with `_bss_get` appended, which returns its address.
4. It inserts the labels that delimit the module's code and data (called `module_start` and `module_end` in the diagram above).
5. It adds a 64-byte, read-only array outside of the module to contain the known-good HMAC value.

#### Integrity testing

In order to actually implement the integrity test, a constructor function within the module calculates an HMAC from `module_start` to `module_end` using a fixed, all-zero key. It compares the result with the known-good value added (by the script) to the unhashed portion of the text segment. If they don't match, it calls `exit` in an infinite loop.
Initially the known-good value will be incorrect. Another script (`inject_hash.go`) calculates the correct value from the assembled object and injects it back into the object.

### Breaking the integrity test

The utility in `util/fipstools/break-hash.go` can be used to corrupt the FIPS module inside a binary and thus trigger a failure of the integrity test. Note that the binary must not be stripped, otherwise the utility will not be able to find the FIPS module.

![build process](./intcheck2.png)

