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

AWS-LC assigns all public API symbols to version namespaces:

Both libcrypto and libssl share the same symbol version namespace:

- **AWS_LC_1_0** (current baseline - ~3,800 libcrypto symbols, ~600 libssl symbols)

When you link an application against AWS-LC, the linker records which symbol versions your application uses. At runtime, the dynamic linker ensures your application gets the correct symbol versions.

### Example

```c
// Your application code
#include <openssl/evp.h>

int main() {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();  // Uses EVP_MD_CTX_new@@AWS_LC_1_0
    // ...
}
```

When compiled and linked:
```bash
$ gcc myapp.c -o myapp -lcrypto-awslc
$ nm -D myapp | grep EVP_MD_CTX_new
                 U EVP_MD_CTX_new@@AWS_LC_1_0
```

The `@@AWS_LC_1_0` suffix indicates your application requires the `AWS_LC_1_0` version of `EVP_MD_CTX_new`.

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

This produces:
- `build/crypto/libcrypto-awslc.so.0.0.0` - with AWS_LC_1_0 versioned symbols
- `build/ssl/libssl-awslc.so.0.0.0` - with AWS_LC_1_0 versioned symbols

### Verification

Verify symbol versioning is applied:

```bash
# Check version definitions
readelf --version-info build/crypto/libcrypto-awslc.so.0.0.0

# List versioned symbols
nm -D build/crypto/libcrypto-awslc.so.0.0.0 | grep @AWS_LC_1_0 | head -10

# Verify all symbols are versioned
nm -D build/crypto/libcrypto-awslc.so.0.0.0 | grep ' T ' | grep -v '@'
# (should be empty - all symbols should have version suffix)
```

## Version Scripts

Symbol versioning is controlled by **GNU ld version scripts** (`.map` files):

- [`crypto/libcrypto_1.0.map`](../crypto/libcrypto_1.0.map) - libcrypto version script
- [`ssl/libssl_1.0.map`](../ssl/libssl_1.0.map) - libssl version script

### Version Script Format

```
AWS_LC_1_0 {
  global:
    AES_encrypt;
    AES_decrypt;
    EVP_MD_CTX_new;
    /* ... all public symbols ... */
  local:
    *;  /* Hide all other symbols */
};
```

This defines:
- **global**: Symbols to export with version `AWS_LC_1_0`
- **local: \***: Hide all other symbols (internal implementation)

## Version Evolution

### Adding New Symbols

When new public APIs are added, the symbol version must be bumped:

#### Step 1: Update CMakeLists.txt

```cmake
# In CMakeLists.txt
set(CRYPTO_VERSION_SCRIPT_VERSION "AWS_LC_1_1")
```

#### Step 2: Create New Version Script

```bash
# crypto/libcrypto_1.1.map
AWS_LC_1_1 {
  global:
    NewFunction1;
    NewFunction2;
    /* new symbols only */
} AWS_LC_1_0;  /* Inherits all AWS_LC_1_0 symbols */
```

The version inheritance (`} AWS_LC_1_0;`) means `AWS_LC_1_1` includes all `AWS_LC_1_0` symbols plus the new ones.

#### Step 3: Update Baseline

```bash
# Generate new baseline
./util/extract_symbols.sh build/crypto/libcrypto-awslc.so.0 \
  tests/ci/baselines/symbols/libcrypto-1.1.txt
```

### Version Naming Convention

- **Format**: `AWS_LC_<MAJOR>_<MINOR>`
- **Increment**: Bump minor version for each API addition
- **Examples**:
  - `AWS_LC_1_0` - Initial release
  - `AWS_LC_1_1` - First update with new symbols
  - `AWS_LC_1_2` - Second update with new symbols
  - `AWS_LC_2_0` - After ABI break (new SOVERSION)

### Symbol Removal (ABI Break)

**Symbol removal breaks ABI compatibility** and should be avoided. If absolutely necessary:

1. **Increment SOVERSION**:
   ```cmake
   # CMakeLists.txt
   set(ABI_VERSION 1)  # Was 0
   ```

2. **Start New Version Series**:
   ```cmake
   set(CRYPTO_VERSION_SCRIPT_VERSION "AWS_LC_2_0")
   ```

3. **Update SONAME**:
   - Old: `libcrypto-awslc.so.0`
   - New: `libcrypto-awslc.so.1`

4. **Document Breaking Change**: Release notes must prominently document this

## CI Integration

AWS-LC CI automatically monitors symbol changes on every PR.

### Symbol Check Jobs

Four jobs run in `.github/workflows/abidiff.yml`:

1. **libcrypto-symbols-incremental**: Compares symbols between previous and current commit
2. **libssl-symbols-incremental**: Same for libssl
3. **libcrypto-symbols-baseline**: Compares current symbols against baseline
4. **libssl-symbols-baseline**: Same for libssl

### CI Policy

- **Symbol additions**: ⚠️ Warning (allowed, but verify intentional)
- **Symbol removals**: ❌ Error (blocks build - ABI break)

### When CI Fails

#### New Symbols Detected (Warning)

```
⚠️  ADDED SYMBOLS (5):
NewFunction1
NewFunction2
...
```

**Action**:
1. Verify these are intentional public API additions
2. Consider bumping symbol version
3. Update baselines

#### Symbol Removal Detected (Error)

```
❌ REMOVED SYMBOLS (2):
OldFunction1
OldFunction2

🛑 ABI BREAK DETECTED!
```

**Action**:
1. Check if removal can be avoided
2. If necessary, follow ABI break procedure (increment SOVERSION)
3. Update baselines and version scripts

## Developer Workflow

### Normal Development (No API Changes)

No action needed. Symbol versioning is transparent.

### Adding New Public APIs

1. Add new `OPENSSL_EXPORT` functions to headers
2. Build and verify symbols:
   ```bash
   cmake -B build -DBUILD_SHARED_LIBS=ON -DENABLE_DIST_PKG=ON
   ninja -C build
   ./util/extract_symbols.sh build/crypto/libcrypto-awslc.so.0 /tmp/new_symbols.txt
   diff tests/ci/baselines/symbols/libcrypto-1.0.txt /tmp/new_symbols.txt
   ```
3. Decide if version bump is needed (usually yes for new APIs)
4. Update version scripts and baselines
5. Commit changes including updated baselines

### Updating Baselines

```bash
# Build with symbol versioning
cmake -GNinja -B build -DBUILD_SHARED_LIBS=ON -DENABLE_DIST_PKG=ON
ninja -C build

# Extract current symbols
./util/extract_symbols.sh build/crypto/libcrypto-awslc.so.0 \
  tests/ci/baselines/symbols/libcrypto-1.0.txt
./util/extract_symbols.sh build/ssl/libssl-awslc.so.0 \
  tests/ci/baselines/symbols/libssl-1.0.txt

# Commit updated baselines
git add tests/ci/baselines/symbols/
git commit -m "Update symbol baselines for new APIs"
```

## Application Compatibility

### Forward Compatibility

Applications using `AWS_LC_1_0` symbols work with `AWS_LC_1_1` libraries because version inheritance ensures all `AWS_LC_1_0` symbols remain available.

### Backward Compatibility

Applications using `AWS_LC_1_1` symbols **require** `AWS_LC_1_1` or later. They won't work with `AWS_LC_1_0` only libraries.

### Package Management

Package managers can enforce version requirements:

```
# Application package metadata
Requires: libcrypto-awslc.so.0(AWS_LC_1_1)
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

**Cause**: Version script file is missing

**Solution**:
```bash
# Generate version scripts
./util/generate_initial_version_scripts.sh
```

### Runtime Error: "symbol version `AWS_LC_1_1' not found"

**Cause**: Application was built against newer library version than is installed

**Solution**: Install AWS-LC 1.1 or later, or rebuild application against installed version

### CI Error: "Symbol removals detected"

**Cause**: Code changes removed exported symbols (ABI break)

**Solution**:
1. Restore removed symbols if possible
2. Or follow ABI break procedure (increment SOVERSION)

## References

- **GNU ld version scripts**: https://sourceware.org/binutils/docs/ld/VERSION.html
- **Symbol versioning in glibc**: https://developers.redhat.com/blog/2019/08/01/how-the-gnu-c-library-handles-backward-compatibility
- **Baseline files**: [`tests/ci/baselines/symbols/README.md`](../tests/ci/baselines/symbols/README.md)
- **Build documentation**: [`BUILDING.md`](../BUILDING.md)

## Future Enhancements

Potential improvements to symbol versioning:

- Automatic baseline updates in CI
- Symbol visibility analysis tool
- Historical symbol database across all versions
- Deprecation warnings for old symbol versions
- Symbol aliasing for renamed functions
