# Incorporating AWS-LC into a project

## Which branch to use

AWS-LC usage typically follows a
["live at head"](https://abseil.io/about/philosophy#we-recommend-that-you-choose-to-live-at-head)
model. Projects pin to whatever the current latest of AWS-LC is at the time
of update, and regularly update it to pick up new changes.

While the AWS-LC repository may contain project-specific branches, e.g.
`integrate-pq`, those are _not_ supported release branches and must not as
such. In rare cases, AWS-LC will temporarily maintain a short-lived branch on
behalf of a project. Most such branches are no longer updated, because the
corresponding project no longer needs them, and we do not create new ones to
replace the ones that are no longer updated.

## Build support

AWS-LC currently supports the following build systems:
* [CMake](https://cmake.org/download) version 3.0 or later.

The development build system is CMake and the CMake build knows how to
automatically generate the intermediate files that AWS-LC needs. However,
outside of the CMake environment, these intermediates are generated and
checked into the AWS-LC source repository in `generated-src`. This avoids
incorporating projects needing to support Perl and Go in their build systems.

The script [`util/generate_build_files.py`](./util/generate_build_files.py)
expects to be run from the `aws-lc` directory. The generated build files will 
be output to `aws-lc/generated-src`. If you don't use any of the supported
build systems then you should augment `generate_build_files.py` with support
for it.

The script will pregenerate the intermediate files (see
[BUILDING.md](./BUILDING.md) for details about which tools will need to be
installed) and output helper files for that build system. It doesn't generate a
complete build script, just file and test lists, which change often.

Periodically an engineer will update the AWS-LC revision, regenerate
these files and check in the updated result.

## Building applications against AWS-LC

Once AWS-LC is built and installed (see [BUILDING.md](./BUILDING.md)), you can
compile and link your application against it. AWS-LC installs the
OpenSSL-compatible headers, the `libcrypto` and `libssl` libraries, and
pkg-config metadata under the prefix you choose.

### Install layout

Configure the install prefix with `CMAKE_INSTALL_PREFIX` and install:

```bash
cmake -GNinja -B aws-lc-build \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_INSTALL_PREFIX="${AWS_LC_INSTALL}" \
  -DCMAKE_INSTALL_LIBDIR=lib
cmake --build aws-lc-build --target install
```

This produces, under `${AWS_LC_INSTALL}`:

* `include/openssl/*.h` -- the public headers.
* `lib/libcrypto.*` and `lib/libssl.*` -- static (`.a`) and/or shared
  (`.so`/`.dylib`) libraries, depending on `BUILD_SHARED_LIBS`.
* `lib/pkgconfig/{libcrypto,libssl,aws-lc}.pc` -- pkg-config files.

`-DCMAKE_INSTALL_LIBDIR=lib` is optional but keeps the library directory named
`lib` on distributions that would otherwise use `lib64`; adjust the paths below
if you omit it. Pass `-DBUILD_SHARED_LIBS=1` for shared libraries, or leave it
unset (the default) for static libraries.

### Compiler flags

Point your compiler at the installed headers:

```bash
cc -I"${AWS_LC_INSTALL}/include" -c app.c -o app.o
```

### Linker flags

Link against `libssl` and `libcrypto`. `libssl` depends on `libcrypto`, so it
must appear first on the link line:

```bash
cc app.o -L"${AWS_LC_INSTALL}/lib" -lssl -lcrypto -lpthread -o app
```

If you only use libcrypto APIs, drop `-lssl`. When linking the static libraries
(`.a`) you also need the system threading library (`-lpthread`); with a shared
build the transitive dependencies are resolved for you and `-lpthread` is not
required.

For a shared-library build, the dynamic loader must be able to find the
libraries at runtime. Either set `LD_LIBRARY_PATH="${AWS_LC_INSTALL}/lib"`
(macOS: `DYLD_LIBRARY_PATH`), add an rpath at link time
(`-Wl,-rpath,"${AWS_LC_INSTALL}/lib"`), or install the libraries into a
directory already on the loader's search path (e.g. via `ldconfig`).

### Using pkg-config

The installed `.pc` files let pkg-config emit the correct compiler and linker
flags:

```bash
export PKG_CONFIG_PATH="${AWS_LC_INSTALL}/lib/pkgconfig"
cc $(pkg-config --cflags libssl) app.c \
   $(pkg-config --libs libssl libcrypto) -o app
```

When linking against the static libraries, pass `--static` so pkg-config also
emits the private dependencies (e.g. `-lpthread`) that a static link requires:

```bash
cc $(pkg-config --cflags libssl) app.c \
   $(pkg-config --libs --static libssl libcrypto) -o app
```

### Verifying the link

After building, confirm your application actually resolved against AWS-LC (and
not, say, a system OpenSSL that happened to be on the search path). Which tool
to use depends on whether you linked the shared or static libraries.

For a **shared** build, `ldd` shows which `libcrypto`/`libssl` the loader
resolves for the binary:

```bash
ldd ./app | grep -E 'libssl|libcrypto'
# libssl.so => /path/to/aws-lc-install/lib/libssl.so (0x...)
# libcrypto.so => /path/to/aws-lc-install/lib/libcrypto.so (0x...)
```

Each line should point at your AWS-LC install prefix. If a path instead points
at a system location (e.g. `/lib64/libcrypto.so.10`), the binary is not using
AWS-LC -- revisit your `-L`/rpath flags or `LD_LIBRARY_PATH`. `readelf -d` shows
the same information statically, without running the loader, plus any embedded
rpath:

```bash
readelf -d ./app | grep -E 'libssl|libcrypto|R(UN)?PATH'
# 0x...(NEEDED)  Shared library: [libssl.so]
# 0x...(NEEDED)  Shared library: [libcrypto.so]
# 0x...(RPATH)   Library rpath: [/path/to/aws-lc-install/lib]
```

For a **static** build the crypto code is baked into your binary, so neither
`ldd` nor the `NEEDED` entries mention `libcrypto`/`libssl`. Instead, look for an
AWS-LC-specific symbol such as `awslc_version_string`, which is present only in
AWS-LC (not OpenSSL). This works for either link mode:

```bash
readelf -sW ./app | grep awslc_version_string   # or: nm ./app | grep awslc_version_string
# ...  FUNC  GLOBAL DEFAULT  ...  awslc_version_string
```

The most direct check is to have the application print the library version at
runtime; against AWS-LC, `OpenSSL_version(OPENSSL_VERSION)` returns a string that
starts with `AWS-LC`:

```c
printf("%s\n", OpenSSL_version(OPENSSL_VERSION));  /* -> "AWS-LC X.Y.Z" */
```

### Integrating with autotools / configure scripts

Most projects that use an autotools `./configure` script expose one of a few
conventions for locating an OpenSSL-compatible library. The AWS-LC integration
tests under [`tests/ci/integration`](./tests/ci/integration) exercise these
patterns against real applications. The following are working examples, each
linking to the relevant build configuration:

* A single `--with-openssl=<prefix>` flag pointing at the install prefix, as
  with curl:
  [`run_curl_integration.sh`](https://github.com/aws/aws-lc/blob/ea70f681ce48c3996b7584be573355c2ebdc56e3/tests/ci/integration/run_curl_integration.sh#L33-L38).
* Separate include and library directory flags (`--with-openssl-incdir` /
  `--with-openssl-libdir`), as with ntp:
  [`run_ntp_integration.sh`](https://github.com/aws/aws-lc/blob/ea70f681ce48c3996b7584be573355c2ebdc56e3/tests/ci/integration/run_ntp_integration.sh#L46-L49).
* A `--with-ssl-dir=<prefix>` flag, as with OpenSSH:
  [`run_openssh_integration.sh`](https://github.com/aws/aws-lc/blob/ea70f681ce48c3996b7584be573355c2ebdc56e3/tests/ci/integration/run_openssh_integration.sh#L53-L61).
* Setting `CPPFLAGS`/`LDFLAGS` in the environment before `./configure` when the
  project has no dedicated flag (here linking the static archives directly), as
  with OpenLDAP:
  [`run_openldap_integration.sh`](https://github.com/aws/aws-lc/blob/ea70f681ce48c3996b7584be573355c2ebdc56e3/tests/ci/integration/run_openldap_integration.sh#L38-L50).
* Combining `--with-openssl=<prefix>` with `CFLAGS`/`CPPFLAGS`/`LDFLAGS`
  environment overrides, as with Cyrus SASL:
  [`run_cyrus_sasl_integration.sh`](https://github.com/aws/aws-lc/blob/ea70f681ce48c3996b7584be573355c2ebdc56e3/tests/ci/integration/run_cyrus_sasl_integration.sh#L31-L40).

### Integrating with CMake

If your project uses CMake's `find_package(OpenSSL)`, point it at AWS-LC by
setting `OPENSSL_ROOT_DIR` to the install prefix:

```bash
cmake -B build -DOPENSSL_ROOT_DIR="${AWS_LC_INSTALL}" ...
```

The gRPC integration does this (and also selects its packaged-SSL provider):
[`run_grpc_integration.sh`](https://github.com/aws/aws-lc/blob/ea70f681ce48c3996b7584be573355c2ebdc56e3/tests/ci/integration/run_grpc_integration.sh#L49-L51).

AWS-LC identifies itself with the `OPENSSL_IS_AWSLC` preprocessor macro (rather
than OpenSSL's version macros or BoringSSL's `OPENSSL_IS_BORINGSSL`). Projects
with BoringSSL- or OpenSSL-specific code paths may need to account for this; see
the note in the gRPC example above.

### Building against a distribution-packaging install

For a system-wide install on Linux/BSD you will typically build AWS-LC in
distribution packaging mode (`-DENABLE_DIST_PKG=ON`, see
[BUILDING.md](./BUILDING.md#distribution-packaging-mode)). This mode is designed
so AWS-LC can coexist with other crypto libraries (including a system OpenSSL)
on the same machine, so the artifacts are named and laid out differently from
the plain build described above. The differences that affect consumers are:

* **Library names carry an `-awslc` suffix**: the libraries are
  `libcrypto-awslc` and `libssl-awslc` (e.g. `libcrypto-awslc.so.1`), not
  `libcrypto`/`libssl`. Link with `-lssl-awslc -lcrypto-awslc` (ssl before
  crypto, as above).
* **Headers move under an `aws-lc/` subdirectory**: they install to
  `<prefix>/include/aws-lc/openssl/` rather than `<prefix>/include/openssl/`.
  Add `-I<prefix>/include/aws-lc` so that `#include <openssl/ssl.h>` resolves.
* **pkg-config modules are renamed to match**: use `libcrypto-awslc` and
  `libssl-awslc` (there is also an `aws-lc` module). The unsuffixed `libcrypto`
  and `libssl` pkg-config modules are *never* installed in this mode -- only the
  `-awslc`-suffixed ones. Enabling the OpenSSL compatibility shim
  (`-DENABLE_DIST_PKG_OPENSSL_SHIM=ON`) adds an `openssl` pkg-config module (and
  unsuffixed `libcrypto.so`/`libssl.so` and `include/<...>/openssl` symlinks),
  but it does not add unsuffixed `libcrypto`/`libssl` pkg-config modules.

Putting the first three together, a manual build against a dist-package install
looks like:

```bash
# Manual flags
cc -I"${AWS_LC_INSTALL}/include/aws-lc" app.c \
   -L"${AWS_LC_INSTALL}/lib" -lssl-awslc -lcrypto-awslc -o app

# Or via pkg-config
export PKG_CONFIG_PATH="${AWS_LC_INSTALL}/lib/pkgconfig"
cc $(pkg-config --cflags libssl-awslc) app.c \
   $(pkg-config --libs libssl-awslc libcrypto-awslc) -o app
```

#### Symbol versioning

Distribution packaging mode also enables ELF symbol versioning for the shared
libraries: every exported symbol is bound to a version node (e.g. `AWS_LC_1.0`
for the current series) and the SONAME encodes the ABI version (e.g.
`libcrypto-awslc.so.1`). The exact node name and SONAME depend on the AWS-LC
version you build; the values shown here are illustrative. See
[docs/SymbolVersioning.md](./docs/SymbolVersioning.md) for the full details.

This is transparent to consumers: you do not pass any extra compiler or linker
flags for it. When you link against the versioned libraries, the linker
automatically records the versions your application references (visible in the
binary's `Verneed` table, e.g. via `readelf -V app`), and at runtime the dynamic
loader checks that the installed library provides them. Version nodes inherit
from their predecessors, so a binary built against `AWS_LC_1.0` keeps working
against later libraries in the same series; the only consumer-visible effect is
a runtime error such as `symbol version 'AWS_LC_1.1' not found` if you deploy
against an *older* AWS-LC than the one you built against.

## Defines

AWS-LC does not present a lot of configurability in order to reduce the
number of configurations that need to be tested. But there are a couple of
\#defines that you may wish to set:

`OPENSSL_NO_ASM` prevents the use of assembly code (although it's up to you to
ensure that the build system doesn't link it in if you wish to reduce binary
size). This will have a significant performance impact but can be useful if you
wish to use tools like
[AddressSanitizer](http://clang.llvm.org/docs/AddressSanitizer.html) that
interact poorly with assembly code.

`OPENSSL_SMALL` removes some code that is especially large at some performance
cost.

## Symbols

You cannot link multiple versions of AWS-LC/BoringSSL or OpenSSL into a single binary
without dealing with symbol conflicts. If you are statically linking multiple
versions together, there's not a lot that can be done because C doesn't have a
module system.

If you are using multiple versions in a single binary, in different shared
objects, ensure you build AWS-LC with `-fvisibility=hidden` and do not
export any symbols. This will prevent any collisions with other
verisons that may be included in other shared objects. Note that this requires
that all callers of AWS-LC APIs live in the same shared object as AWS-LC.

If you require that AWS-LC APIs be used across shared object boundaries,
continue to build with `-fvisibility=hidden` but define
`BORINGSSL_SHARED_LIBRARY` in both AWS-LC and consumers. AWS-LC's own
source files (but *not* consumers' source files) must also build with
`BORINGSSL_IMPLEMENTATION` defined. This will export AWS-LC's public symbols
in the resulting shared object while hiding private symbols. However note that,
as with a static link, this precludes dynamically linking with another version
of AWS-LC/BoringSSL or OpenSSL.
