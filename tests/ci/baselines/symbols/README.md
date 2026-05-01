# Symbol Version Registries

The symbol version registries have moved alongside their respective libraries:

- [`crypto/libcrypto.txt`](../../../../crypto/libcrypto.txt) — libcrypto symbol registry
- [`ssl/libssl.txt`](../../../../ssl/libssl.txt) — libssl symbol registry

Each line records a symbol and the version node it was introduced in:

```
AES_encrypt AWS_LC_0_0
EVP_MD_CTX_new AWS_LC_0_0
new_function AWS_LC_1_0
```

The GNU ld version scripts (`crypto/libcrypto.map`, `ssl/libssl.map`) are
derived from these registries. See [`docs/SymbolVersioning.md`](../../../../docs/SymbolVersioning.md)
for full documentation.
