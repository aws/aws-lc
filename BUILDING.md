# Building AWS-LC

## Build Prerequisites

The standalone CMake build is primarily intended for developers. If embedding
AWS-LC into another project with a pre-existing build system, see
[INCORPORATING.md](./INCORPORATING.md).

If in doubt, use the most recent stable version of each build tool.

  * [CMake](https://cmake.org/download/) 3.0 or later is required.

  * A recent version of Perl is required. On Windows,
    [Active State Perl](http://www.activestate.com/activeperl/) has been
    reported to work, as has MSYS Perl.
    [Strawberry Perl](http://strawberryperl.com/) also works but it adds GCC
    to `PATH`, which can confuse some build tools when identifying the compiler
    (removing `C:\Strawberry\c\bin` from `PATH` should resolve any problems).
    If Perl is not found by CMake, it may be configured explicitly by setting
    `PERL_EXECUTABLE`.
    * To build without Perl (not recommended) see [this section.](#using-pre-generated-build-files)

  * [Go](https://golang.org/dl/) 1.17.13 or later is required. If not found by
    CMake, the go executable may be configured explicitly by setting
    `GO_EXECUTABLE`.
    * To build without Go (not recommended) see [this section.](#using-pre-generated-build-files)

  * Building with [Ninja](https://ninja-build.org/) instead of Make is
    recommended, because it makes builds faster. On Windows, CMake's Visual
    Studio generator may also work, but it not tested regularly and requires
    recent versions of CMake for assembly support.

  * On Windows only, [NASM](https://www.nasm.us/) is required. If not found
    by CMake, it may be configured explicitly by setting
    `CMAKE_ASM_NASM_COMPILER`.

  * C and C++ compilers with C++11 support are required. On Windows, MSVC 14
    (Visual Studio 2015) or later with Platform SDK 8.1 or later are supported,
    but newer versions are recommended. We will drop support for Visual Studio
    2015 in March 2022, five years after the release of Visual Studio 2017.
    Recent versions of GCC (4.1.3+) and Clang should work on non-Windows
    platforms, and maybe on Windows too.

  * On x86_64 Linux, the tests have an optional
    [libunwind](https://www.nongnu.org/libunwind/) dependency to test the
    assembly more thoroughly.

## Building

We use CMake to manage the build process. Note that the executable name for
CMake version 3.0 and later differs depending on the OS. For example, on Amazon
Linux 2 the executable name is `cmake3` while on Ubuntu 20.04 the executable
name is `cmake`. Modify command snippets below accordingly.

Using Ninja (note the 'N' is capitalized in the cmake invocation):

    cmake -GNinja -B build
    ninja -C build

Using Make (does not work on Windows):

    cmake -B build
    make -C build

This produces a debug build by default. Optimisation isn't enabled, and debug
assertions are included. Pass `-DCMAKE_BUILD_TYPE=Release` to `cmake` to
configure a release build:

    cmake -GNinja -B build -DCMAKE_BUILD_TYPE=Release
    ninja -C build

If you want to cross-compile then there is an example toolchain file for 32-bit
Intel in `util/`. Wipe out the build directory, run `cmake` like this:

    cmake -B build -DCMAKE_TOOLCHAIN_FILE=../util/32-bit-toolchain.cmake -GNinja

If you want to build as a shared library, pass `-DBUILD_SHARED_LIBS=1`. On
Windows, where functions need to be tagged with `dllimport` when coming from a
shared library, define `BORINGSSL_SHARED_LIBRARY` in any code which `#include`s
the BoringSSL headers.

In order to serve environments where code-size is important as well as those
where performance is the overriding concern, `OPENSSL_SMALL` can be defined to
remove some code that is especially large.

See [CMake's documentation](https://cmake.org/cmake/help/v3.4/manual/cmake-variables.7.html)
for other variables which may be used to configure the build.

You usually don't need to run `cmake` again after changing `CMakeLists.txt`
files because the build scripts will detect changes to them and rebuild
themselves automatically.

### Building for Android

It's possible to build BoringSSL with the Android NDK using CMake. Recent
versions of the NDK include a CMake toolchain file which works with CMake 3.6.0
or later. This has been tested with version r16b of the NDK.

Unpack the Android NDK somewhere and export `ANDROID_NDK` to point to the
directory. Then run CMake like this:

    cmake -DANDROID_ABI=armeabi-v7a \
          -DANDROID_PLATFORM=android-19 \
          -DCMAKE_TOOLCHAIN_FILE=${ANDROID_NDK}/build/cmake/android.toolchain.cmake \
          -GNinja -B build

Once you've run that, Ninja should produce Android-compatible binaries.  You
can replace `armeabi-v7a` in the above with `arm64-v8a` and use API level 21 or
higher to build aarch64 binaries.

For other options, see the documentation in the toolchain file.

To debug the resulting binaries on an Android device with `gdb`, run the
commands below. Replace `ARCH` with the architecture of the target device, e.g.
`arm` or `arm64`.

    adb push ${ANDROID_NDK}/prebuilt/android-ARCH/gdbserver/gdbserver \
        /data/local/tmp
    adb forward tcp:5039 tcp:5039
    adb shell /data/local/tmp/gdbserver :5039 /path/on/device/to/binary

Then run the following in a separate shell. Replace `HOST` with the OS and
architecture of the host machine, e.g. `linux-x86_64`.

    ${ANDROID_NDK}/prebuilt/HOST/bin/gdb
    target remote :5039  # in gdb

### Building for iOS

To build for iOS, pass `-DCMAKE_OSX_SYSROOT=iphoneos` and
`-DCMAKE_OSX_ARCHITECTURES=ARCH` to CMake, where `ARCH` is the desired
architecture, matching values used in the `-arch` flag in Apple's toolchain.

Passing multiple architectures for a multiple-architecture build is not
supported.

### Building with Prefixed Symbols

BoringSSL's build system has experimental support for adding a custom prefix to
all symbols. This can be useful when linking multiple versions of BoringSSL in
the same project to avoid symbol conflicts.

In order to build with prefixed symbols, the `BORINGSSL_PREFIX` CMake variable
should specify the prefix to add to all symbols, and the
`BORINGSSL_PREFIX_SYMBOLS` CMake variable should specify the path to a file
which contains a list of symbols which should be prefixed (one per line;
comments are supported with `#`). In other words, `cmake -B build
-DBORINGSSL_PREFIX=MY_CUSTOM_PREFIX
-DBORINGSSL_PREFIX_SYMBOLS=/path/to/symbols.txt` will configure the build to add
the prefix `MY_CUSTOM_PREFIX` to all of the symbols listed in
`/path/to/symbols.txt`.

It is currently the caller's responsibility to create and maintain the list of
symbols to be prefixed. Alternatively, `util/read_symbols.go` reads the list of
exported symbols from a `.a` file, and can be used in a build script to generate
the symbol list on the fly (by building without prefixing, using
`read_symbols.go` to construct a symbol list, and then building again with
prefixing).

This mechanism is under development and may change over time. Please contact the
BoringSSL maintainers if making use of it.

## Known Limitations on Windows

  * CMake can generate Visual Studio projects, but the generated project files
    don't have steps for assembling the assembly language source files, so they
    currently cannot be used to build BoringSSL.

## ARM CPU Capabilities

ARM, unlike Intel, does not have a userspace instruction that allows
applications to discover the capabilities of the processor. Instead, the
capability information has to be provided by a combination of compile-time
information and the operating system.

BoringSSL determines capabilities at compile-time based on `__ARM_NEON`,
`__ARM_FEATURE_AES`, and other preprocessor symbols defined in
[Arm C Language Extensions (ACLE)](https://developer.arm.com/architectures/system-architectures/software-standards/acle).
These values are usually controlled by the `-march` flag. You can also define
any of the following to enable the corresponding ARM feature, but using the ACLE
symbols via `-march` is recommended.

  * `OPENSSL_STATIC_ARMCAP_NEON`
  * `OPENSSL_STATIC_ARMCAP_AES`
  * `OPENSSL_STATIC_ARMCAP_SHA1`
  * `OPENSSL_STATIC_ARMCAP_SHA256`
  * `OPENSSL_STATIC_ARMCAP_PMULL`

The resulting binary will assume all such features are always present. This can
reduce code size, by allowing the compiler to omit fallbacks. However, if the
feature is not actually supported at runtime, BoringSSL will likely crash.

BoringSSL will additionally query the operating system at runtime for additional
features, e.g. with `getauxval` on Linux. This allows a single binary to use
newer instructions when present, but still function on CPUs without them. But
some environments don't support runtime queries. If building for those, define
`OPENSSL_STATIC_ARMCAP` to limit BoringSSL to compile-time capabilities. If not
defined, the target operating system must be known to BoringSSL.

## Binary Size

The implementations of some algorithms require a trade-off between binary size
and performance. For instance, BoringSSL's fastest P-256 implementation uses a
148 KiB pre-computed table. To optimize instead for binary size, pass
`-DOPENSSL_SMALL=1` to CMake or define the `OPENSSL_SMALL` preprocessor symbol.

# Running Tests

There are two sets of tests: the C/C++ tests and the blackbox tests. For former
are built by Ninja and can be run from the top-level directory with `go run
util/all_tests.go`. The latter have to be run separately by running `go test`
from within `ssl/test/runner`.

Both sets of tests may also be run with `ninja -C build run_tests`, but CMake
3.2 or later is required to avoid Ninja's output buffering.

# Using Pre-Generated Build Files

If your project is unable to take on a Go or Perl dependency, the AWS-LC repository
provides generated build files. These can be used in place of the files that would
normally be generated by these dependencies.

It is still recommended to have both Go and Perl installed to be able to run the full
range of unit tests, as well as running valgrind and SDE tests. Building without Go now
produces a new target, `run_minimal_tests` in place of `run_tests`.

More information on this can be found in [INCORPORATING.md](/INCORPORATING.md).

# Snapsafe Detection

AWS-LC supports Snapsafe-type uniqueness breaking event detection
on Linux using SysGenID (https://lkml.org/lkml/2021/3/8/677). This mechanism
is used for security hardening. If a SysGenID interface is not found, then the
mechanism is ignored.

## Snapsafe Prerequisites

Snapshots taken on active hosts can potentially be unsafe to use.
See "Snapshot Safety Prerequisites" here: https://lkml.org/lkml/2021/3/8/677

# FIPS Mode

For more details on building AWS-LC in FIPS mode, see the [crypto/fipsmodule/FIPS.md](crypto/fipsmodule/FIPS.md).

# Data Independent Timing on AArch64

The functions described in this section are still experimental.

The Data Independent Timing (DIT) flag on Arm64 processors, when
enabled, ensures the following as per [Arm A-profile Architecture
Registers
Document](https://developer.arm.com/documentation/ddi0601/2023-12/AArch64-Registers/DIT--Data-Independent-Timing):
- The timing of every load and store instruction is insensitive to the
  value of the data being loaded or stored.
- For certain data processing instructions, the instruction takes a
  time which is independent of the data in the registers and the NZCV
  flags.

It is also expected to disable the Data Memory-dependent Prefetcher
(DMP) feature of Apple M-series CPUs starting at M3 as per [this
article](https://appleinsider.com/articles/24/03/21/apple-silicon-vulnerability-leaks-encryption-keys-and-cant-be-patched-easily).

Building with the option `-DENABLE_DATA_INDEPENDENT_TIMING=ON`
will enable the macro `SET_DIT_AUTO_RESET`. This macro is present at
the entry of functions that process/load/store secret data to set the
DIT flag and then restore it to its original value on entry.  With this
build option, there is an effect on performance that varies by
function and by processor architecture. The effect is mostly due to
setting and resetting the DIT flag. If it remains set over many calls,
the effect can be largely mitigated.

The macro and the functions invoked by it are internally declared,
being experimental. In the following, we tested the effect of
inserting the macro in the caller's application at the beginning of
the code scope that makes repeated calls to AWS-LC cryptographic
functions. The functions that are invoked in the macro,
`armv8_set_dit` and `armv8_restore_dit`, are placed at the beginning
and the end, respectively, of the benchmarking function `Speed()` in
`tool/speed.cc` when the `-dit` option is used.

    ./tool/bssl speed -dit

This resulted in benchmarks that are close to the release build
without the `-DENABLE_DATA_INDEPENDENT_TIMING=ON` flag when tested on
Apple M2.

The DIT capability, which is checked in `OPENSSL_cpuid_setup` can be
masked out at runtime by calling `armv8_disable_dit`. This would
result in having the functions `armv8_set_dit` and `armv8_restore_dit`
being of no effect. It can be made available again at runtime by calling
`armv8_enable_dit`.

**Important**: This runtime control is provided to users that would use
the build flag `ENABLE_DATA_INDEPENDENT_TIMING`, but would
then disable DIT capability at runtime. This is ideally done in
an initialization routine of AWS-LC before any threads are spawn.
Otherwise, there may be data races created because these functions write
to the global variable `OPENSSL_armcap_P`.
