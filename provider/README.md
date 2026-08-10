# aws-lc-provider

An OpenSSL 3.x [provider](https://docs.openssl.org/3.0/man7/provider/) that implements no
cryptography of its own. It answers OpenSSL's algorithm fetches by delegating each operation to
AWS-LC, so an application keeps calling the OpenSSL 3.x API while the cryptography underneath it
comes from AWS-LC, with no change to the application.

Algorithms which it currently serves is in `ALGORITHM_SUPPORT.md`.

## Building

Start in the directory containing the AWS-LC checkout, not in the checkout itself:

```bash
# Build OpenSSL from source. It supplies the provider headers AWS-LC's tree
# does not carry.
git clone https://github.com/openssl/openssl.git
export OPENSSL_ROOT="${PWD}/openssl/install"
cd openssl
./config --prefix="${OPENSSL_ROOT}" --openssldir="${OPENSSL_ROOT}"
make && make install_sw

# Build AWS-LC and the provider. The provider uses shared libraries and the
# upstream OpenSSL build for header files and testing.
cd aws-lc
cmake -GNinja -Bbuild -DBUILD_SHARED_LIBS=ON \
  -DBUILD_AWSLC_PROVIDER=ON -DAWSLC_PROVIDER_OPENSSL_ROOT="${OPENSSL_ROOT}"
cd build
ninja

# Build with symbol versioning via ENABLE_DIST_PKG in AWS-LC (Linux only)
cmake -GNinja -Bbuild -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_SHARED_LIBS=ON -DENABLE_DIST_PKG=ON \
  -DBUILD_AWSLC_PROVIDER=ON -DAWSLC_PROVIDER_OPENSSL_ROOT="${OPENSSL_ROOT}"
```

The provider artifact is `build/provider/awslc.so`.

## Testing

There are two test binaries for `aws-lc-provider`, one per side of the split.

`awslc_provider_test` is the interesting one, and where nearly all coverage belongs. It links
OpenSSL's libcrypto, drives the public EVP API, and reaches AWS-LC only through the module the loader
dlopens, which is exactly the arrangement a consumer has.

`awslc_provider_backend_test` links AWS-LC and no OpenSSL, and calls the backend wrappers directly.
It exists for the guarantees the backend adds on top of AWS-LC that the EVP API cannot reach. Anything
testable through EVP belongs in the frontend binary instead.

```bash
# Frontend, through the OpenSSL EVP and provider APIs
./build/provider/awslc_provider_test

# Backend, against the AWS-LC layer directly
./build/provider/awslc_provider_backend_test
```

## Using the provider

### Installing the module

OpenSSL loads a provider by bare name from its modules directory, appending the platform's
suffix. Copy the built module there:

```bash
# Where the OpenSSL you are configuring looks for modules.
MODULES_DIR="$(openssl version -m | sed 's/^MODULESDIR: //; s/"//g')"

cp build/provider/awslc.so "${MODULES_DIR}/"
```

### Activating it by config file

The file to edit is `openssl.cnf` in the directory `openssl version -d` reports.

Providers are only loaded if the top of the file routes into a provider section, which stock
`openssl.cnf` already does with `openssl_conf = openssl_init`. Under that:

```ini
[openssl_init]
providers = provider_sect
alg_section = evp_properties

[provider_sect]
awslc = awslc_sect
default = default_sect

[awslc_sect]
activate = 1

[default_sect]
activate = 1

# Leading `?` makes this a preference: fetches AWS-LC cannot serve fall through.
[evp_properties]
default_properties = ?provider=awslc
```

With that in place, an implicit fetch reaches AWS-LC with no flags and no source change:

```console
$ openssl list -providers
Providers:
  awslc
    name: AWS-LC Provider
    version: 0.1.0
    status: active
  default
    name: OpenSSL Default Provider
    ...
```

### Activating it programmatically

For a test or an application that manages its own library context:

```c
OSSL_LIB_CTX *libctx = OSSL_LIB_CTX_new();
OSSL_PROVIDER_set_default_search_path(libctx, "/path/to/build/provider");
OSSL_PROVIDER_load(libctx, "awslc");
OSSL_PROVIDER_load(libctx, "default");        /* the fallback leg */

// Use `"provider=awslc"` without the `?` to require this specific provider
EVP_MD *md = EVP_MD_fetch(libctx, "SHA2-256", "provider=awslc");
```

### Asserting that AWS-LC is what served the operation

To verify which provider served this operation.

```c
EVP_MD *md = EVP_MD_fetch(libctx, "SHA2-256", "?provider=awslc");
const char *served_by = OSSL_PROVIDER_get0_name(EVP_MD_get0_provider(md));

if (strcmp(served_by, "awslc") != 0) {
  /* AWS-LC did not serve this. Fail, or log, per your policy. */
}
```

## Source layout

OpenSSL's and AWS-LC's headers cannot coexist in one translation unit: both install as
`openssl/*.h`, and they define the same type names incompatibly. The provider is therefore split,
with each side compiled against only one of the two.

The directory structure states which library each file may see, and separates what grows with the
algorithm count from what does not.

| Path | Sees | Contents |
|---|---|---|
| `internal/backend.h` | neither | The only header file that can be included in any source file. Interfaces are plain C-types only. |
| `internal/backend/<operation>.h` | neither | Per-operation backend entry points, in plain C types |
| `internal/frontend/<operation>.h` | OpenSSL | Per-operation dispatch tables, for `registry.c` |
| `frontend/provider.c` | OpenSSL | The entry point. Implements provider-level dispatch table functions. |
| `frontend/registry.c` | OpenSSL | One `OSSL_ALGORITHM` table per operation. |
| `frontend/operations/<operation>/<alg>.c` | OpenSSL | Dispatch slots and their `OSSL_PARAM` plumbing |
| `backend/operations/<operation>/<alg>.c` | AWS-LC | The calls that actually compute |
| `test/frontend/**` | OpenSSL | Main test suite driving from the OpenSSL Provider interface. |
| `test/backend/**` | AWS-LC | Test suite for invoking `backend/` functions directly. |
