# Incorporating AWS-LC into a project

## Build support

AWS-LC currently supports the following build systems:
* [CMake](https://cmake.org/download) version 3.0 or later.

The development build system is CMake and the CMake build knows how to
automatically generate the intermediate files that AWS-LC needs. However,
outside of the CMake environment, these intermediates are generated and
checked into the AWS-LC source repository in `generated-src`. This avoids
incorporating projects needing to support Perl and Go in their build systems.

The script [`util/generate_build_files.py`](/util/generate_build_files.py)
expects to be run from the `aws-lc` directory. The generated build files will 
be output to `aws-lc/generated-src`. If you don't use any of the supported
build systems then you should augment `generate_build_files.py` with support
for it.

The script will pregenerate the intermediate files (see
[BUILDING.md](/BUILDING.md) for details about which tools will need to be
installed) and output helper files for that build system. It doesn't generate a
complete build script, just file and test lists, which change often.

Periodically an engineer will update the AWS-LC revision, regenerate
these files and check in the updated result.

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
objects, ensure you build BoringSSL with `-fvisibility=hidden` and do not
export any of BoringSSL's symbols. This will prevent any collisions with other
verisons that may be included in other shared objects. Note that this requires
that all callers of BoringSSL APIs live in the same shared object as BoringSSL.

If you require that BoringSSL APIs be used across shared object boundaries,
continue to build with `-fvisibility=hidden` but define
`BORINGSSL_SHARED_LIBRARY` in both BoringSSL and consumers. BoringSSL's own
source files (but *not* consumers' source files) must also build with
`BORINGSSL_IMPLEMENTATION` defined. This will export BoringSSL's public symbols
in the resulting shared object while hiding private symbols. However note that,
as with a static link, this precludes dynamically linking with another version
of BoringSSL or OpenSSL.
