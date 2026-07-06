# Symbol Versioning in AWS-LC

## Overview

AWS-LC uses **ELF symbol versioning** for its shared libraries on UNIX systems (Linux and BSDs). Symbol versioning provides:

- **ABI Stability Tracking**: Each exported symbol is assigned to a specific version namespace
- **Backward Compatibility**: Applications link to specific symbol versions, preventing breakage
- **Concurrent Installation**: Multiple AWS-LC versions can coexist on the same system
- **Distribution Packaging**: Standard practice for system libraries in Linux distributions

Symbol versioning is automatically enabled when building with distribution packaging mode (`-DENABLE_DIST_PKG=1`).

## How It Works

### Symbol Versions

AWS-LC assigns every exported symbol to a version node. Both libcrypto and libssl
share the same symbol version namespace:

- **AWS_LC_1.0** (current baseline - ~3,000 libcrypto symbols, ~640 libssl symbols)

When you link an application against AWS-LC, the linker records which symbol versions your application uses. At runtime, the dynamic linker ensures your application gets the correct symbol versions.

### Example

```c
// Your application code
#include <openssl/evp.h>

int main() {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();  // Uses EVP_MD_CTX_new@@AWS_LC_1.0
    // ...
}
```

When compiled and linked:
```bash
$ gcc myapp.c -o myapp -lcrypto-awslc
$ nm -D myapp | grep EVP_MD_CTX_new
                 U EVP_MD_CTX_new@@AWS_LC_1.0
```

The `@@AWS_LC_1.0` suffix indicates your application requires the `AWS_LC_1.0` version of `EVP_MD_CTX_new`.

## Building with Symbol Versioning

### Prerequisites

- UNIX system (Linux or BSD)
- GNU ld or compatible linker
- CMake 3.0+
- Ninja or Make

### Build Configuration

Symbol versioning is enabled automatically with distribution packaging:

```bash
cmake -GNinja -B build \
  -DBUILD_SHARED_LIBS=ON \
  -DENABLE_DIST_PKG=ON \
  -DCMAKE_BUILD_TYPE=Release

ninja -C build
```

This produces versioned shared libraries whose file name carries the full
library version (`SOFTWARE_VERSION`) and whose SONAME carries the ABI version
(`ABI_VERSION`). For example, on AWS-LC `5.1.0` with `ABI_VERSION=1`:

- `build/crypto/libcrypto-awslc.so.5.1.0` — real file, with `AWS_LC_1.0` versioned symbols
- `build/ssl/libssl-awslc.so.5.1.0` — real file, with `AWS_LC_1.0` versioned symbols

along with the usual symlinks: `libcrypto-awslc.so.1` (SONAME) → `libcrypto-awslc.so.5.1.0`, and the linker/dev symlink `libcrypto-awslc.so`.

> Note: the symbol version node (`AWS_LC_1.0`) is independent of the file
> version. The node only changes when new API is added or an ABI break starts a
> new series; the file version tracks each release.

### Verification

Verify symbol versioning is applied (use the `libcrypto-awslc.so` dev symlink so
the commands do not depend on a specific version string):

```bash
# Check version definitions
readelf --version-info build/crypto/libcrypto-awslc.so

# List versioned symbols
nm -D build/crypto/libcrypto-awslc.so | grep @AWS_LC_1.0 | head -10

# Verify all symbols are versioned
nm -D build/crypto/libcrypto-awslc.so | grep ' T ' | grep -v '@'
# (should be empty - all symbols should have a version suffix)
```

## Version Scripts and the Symbol Registry

Symbol versioning is driven by two per-library files that are checked into the tree:

- **Registry (source of truth)**: [`crypto/libcrypto.txt`](../crypto/libcrypto.txt), [`ssl/libssl.txt`](../ssl/libssl.txt)
- **Version script (generated)**: [`crypto/libcrypto.map`](../crypto/libcrypto.map), [`ssl/libssl.map`](../ssl/libssl.map)

Each registry line records a symbol, its version node, and its visibility:

```
AES_encrypt AWS_LC_1.0 PUBLIC
CRYPTO_once AWS_LC_1.0 PRIVATE
ssl_cert_check_key_usage AWS_LC_1.0 PRIVATE_CXX
```

Visibility values:
- `PUBLIC` — public API from `include/openssl/*.h`; can never be removed
- `PRIVATE` — internal API with C linkage from `crypto/**/*.h`; may be removed
- `PRIVATE_CXX` — internal API with C++ linkage from `ssl/**/*.h`; may be removed

The `.map` files are **auto-generated from the registry and must not be edited by
hand.** CMake attaches the `.map` to each library via `apply_version_script()`
(see [`cmake/GenerateVersionScript.cmake`](../cmake/GenerateVersionScript.cmake)).

### Tooling

The registry and version scripts are managed by Go tools and shell wrappers in `util/`:

| Tool | Purpose |
|------|---------|
| [`util/read_public_symbols`](../util/read_public_symbols) | Extracts exported symbols from headers and classifies visibility (PUBLIC / PRIVATE / PRIVATE_CXX). |
| [`util/generate_version_script`](../util/generate_version_script) | Generates a `.map` version script from a registry `.txt`. Deterministic. |
| [`util/generate_initial_version_scripts.sh`](../util/generate_initial_version_scripts.sh) | Bootstraps both registries and `.map` files from scratch (used once to establish the baseline). |
| [`util/update_symbol_version.sh`](../util/update_symbol_version.sh) | Adds newly introduced API to a new version node and regenerates the `.map` files. |

### Version Script Format

```
AWS_LC_1.0 {
  global:
    AES_encrypt;
    AES_decrypt;
    EVP_MD_CTX_new;
    /* ... all symbols in this node ... */
  local:
    *;  /* Hide all other symbols */
};
```

This defines:
- **global**: Symbols exported with version `AWS_LC_1.0`
- **local: \***: Hide all other symbols (internal implementation)

When more than one version node exists, each node inherits from its predecessor
(e.g. `AWS_LC_1.1 { global: ...; } AWS_LC_1.0;`). `generate_version_script`
emits this inheritance automatically; only the oldest (base) node carries the
`local: *;` catch-all.

## Version Evolution

### Adding New Symbols

When new public APIs are added, the new symbols must be assigned to a new version
node. Use `update_symbol_version.sh` rather than editing the registry or `.map`
files by hand:

```bash
# Build so the new OPENSSL_EXPORT symbols exist in the headers, then:
./util/update_symbol_version.sh AWS_LC_1.1
```

This extracts the current symbol set from the headers, identifies symbols not yet
in the registry, appends them to the registry under the given node with their
visibility, re-sorts the registry, and regenerates `crypto/libcrypto.map` and
`ssl/libssl.map`. Commit the updated `.txt` and `.map` files together.

> While a version series is unreleased, newly added symbols may simply be folded
> into the existing baseline node (`AWS_LC_1.0`) by regenerating the registry;
> once a version has shipped, its node is frozen and new API goes into a new node.

### Version Naming Convention

- **Format**: `AWS_LC_<MAJOR>.<MINOR>`
- **Increment**: Bump minor version for each API addition
- **Examples**:
  - `AWS_LC_1.0` - Initial release
  - `AWS_LC_1.1` - First update with new symbols
  - `AWS_LC_1.2` - Second update with new symbols
  - `AWS_LC_2.0` - After ABI break (new SONAME)

### Symbol Removal (ABI Break)

**Removing a PUBLIC symbol breaks ABI compatibility** and should be avoided. If
absolutely necessary:

1. **Increment `ABI_VERSION`** in `CMakeLists.txt` (this drives the SONAME):
   ```cmake
   set(ABI_VERSION 2)  # Was 1
   ```

2. **Start a new version series** by assigning symbols to a new major node:
   ```bash
   ./util/update_symbol_version.sh AWS_LC_2.0
   ```

3. **SONAME changes accordingly**:
   - Old: `libcrypto-awslc.so.1`
   - New: `libcrypto-awslc.so.2`

4. **Document the breaking change**: release notes must prominently document this.

## CI Integration

AWS-LC CI monitors the symbol registry and version scripts on every PR via
`.github/workflows/abidiff.yml`.

### Symbol Check Jobs

Six jobs run:

1. **libcrypto symbol check (incremental)** — compares the registry between the PR base and head; flags additions (warning) and PUBLIC removals (error).
2. **libssl symbol check (incremental)** — same for libssl.
3. **libcrypto symbol check (baseline)** — extracts symbols from the headers and verifies every one is present in the registry (catches unregistered new API).
4. **libssl symbol check (baseline)** — same for libssl.
5. **libcrypto version script drift check** — regenerates `crypto/libcrypto.map` from the registry and verifies it matches the committed `.map` byte-for-byte.
6. **libssl version script drift check** — same for libssl.

These are implemented by
[`.github/docker_images/symbol_check/check_symbols.sh`](../.github/docker_images/symbol_check/check_symbols.sh)
in `incremental`, `baseline`, and `mapcheck` modes.

### CI Policy

- **Symbol additions**: ⚠️ Warning (allowed, but verify intentional)
- **PUBLIC symbol removals**: ❌ Error (blocks the build — ABI break)
- **PRIVATE / PRIVATE_CXX removals**: ⚠️ Warning (allowed)
- **Unregistered new API (baseline)**: ❌ Error (run `update_symbol_version.sh`)
- **`.map` out of sync with registry (drift)**: ❌ Error (regenerate the `.map`)

### When CI Fails

#### Unregistered symbols (baseline check)

```
❌ UNREGISTERED SYMBOLS (1):
CRYPTO_tls13_hkdf_expand_label

🛑 New symbols are not in the registry.
   Run: util/update_symbol_version.sh <version>
```

**Action**: run `./util/update_symbol_version.sh <version>` and commit the updated `.txt`/`.map`.

#### PUBLIC symbol removal (incremental check)

```
❌ PUBLIC SYMBOLS REMOVED FROM REGISTRY (2):
OldFunction1
OldFunction2

🛑 ABI BREAK: removing public symbols from the registry breaks compatibility.
```

**Action**: restore the symbols if possible; otherwise follow the ABI break procedure above.

#### Version script drift (mapcheck)

```
❌ crypto/libcrypto.map is out of sync with crypto/libcrypto.txt (diff above).
🛑 The version script is auto-generated and must not drift.
```

**Action**: regenerate the `.map` with `go run ./util/generate_version_script -in crypto/libcrypto.txt -out crypto/libcrypto.map` (or `util/generate_initial_version_scripts.sh`) and commit it.

## Developer Workflow

### Normal Development (No API Changes)

No action needed. Symbol versioning is transparent.

### Adding New Public APIs

1. Add new `OPENSSL_EXPORT` functions to headers.
2. Register the new symbols and regenerate the version scripts:
   ```bash
   ./util/update_symbol_version.sh AWS_LC_1.1
   ```
3. Optionally verify against a build:
   ```bash
   cmake -GNinja -B build -DBUILD_SHARED_LIBS=ON -DENABLE_DIST_PKG=ON
   ninja -C build
   nm -D build/crypto/libcrypto-awslc.so | grep @AWS_LC_1.1 | head
   ```
4. Commit the updated registry (`crypto/libcrypto.txt`, `ssl/libssl.txt`) and version scripts (`crypto/libcrypto.map`, `ssl/libssl.map`) together.

### Regenerating from Scratch

To rebuild the registries and version scripts from the current headers (rarely needed):

```bash
./util/generate_initial_version_scripts.sh
git add crypto/libcrypto.txt crypto/libcrypto.map ssl/libssl.txt ssl/libssl.map
git commit -m "Regenerate symbol registry and version scripts"
```

## Application Compatibility

### Forward Compatibility

Applications using `AWS_LC_1.0` symbols work with `AWS_LC_1.1` libraries because version inheritance ensures all `AWS_LC_1.0` symbols remain available.

### Backward Compatibility

Applications using `AWS_LC_1.1` symbols **require** `AWS_LC_1.1` or later. They won't work with `AWS_LC_1.0`-only libraries.

### Package Management

Package managers can enforce version requirements:

```
# Application package metadata
Requires: libcrypto-awslc.so.1(AWS_LC_1.1)
```

This ensures users have a compatible AWS-LC version installed.

## Platform Support

### Supported

- **Linux**: All distributions (Amazon Linux, Ubuntu, Fedora, Debian, RHEL, etc.)
- **BSD**: FreeBSD, OpenBSD, NetBSD (requires GNU ld or compatible)

### Not Supported

- **macOS**: Uses different versioning mechanism (compatibility_version/current_version)
- **Windows**: PE format uses DEF files for exports
- **Static libraries**: Symbol versioning only applies to shared libraries

On unsupported platforms, `ENABLE_DIST_PKG` builds libraries without symbol versioning.

## Troubleshooting

### Build Error: "version script not found"

**Cause**: The `.map` version script file is missing.

**Solution**:
```bash
# Regenerate registries and version scripts
./util/generate_initial_version_scripts.sh
```

### Runtime Error: "symbol version `AWS_LC_1.1' not found"

**Cause**: Application was built against a newer library version than is installed.

**Solution**: Install AWS-LC 1.1 or later, or rebuild the application against the installed version.

### CI Error: "PUBLIC symbols removed" / "unregistered symbols" / "map out of sync"

See [When CI Fails](#when-ci-fails) above for the specific remediation per check.

## References

- **GNU ld version scripts**: https://sourceware.org/binutils/docs/ld/VERSION.html
- **Symbol versioning in glibc**: https://developers.redhat.com/blog/2019/08/01/how-the-gnu-c-library-handles-backward-compatibility
- **Symbol registry**: [`crypto/libcrypto.txt`](../crypto/libcrypto.txt), [`ssl/libssl.txt`](../ssl/libssl.txt)
- **Build documentation**: [`BUILDING.md`](../BUILDING.md)

## Future Enhancements

Potential improvements to symbol versioning:

- Automatic registry updates in CI
- Symbol visibility analysis tool
- Historical symbol database across all versions
- Deprecation warnings for old symbol versions
- Symbol aliasing for renamed functions
