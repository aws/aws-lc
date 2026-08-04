# Test Vector Generator

This utility generates cryptographic test vectors for AWS-LC.

## Supported Vectors

### ML-KEM Decapsulation Validation
Generates decapsulation validation test vectors for ML-KEM-512, ML-KEM-768, and ML-KEM-1024 that validate FIPS 203 Section 7.3 requirements:

- Valid decapsulation key and ciphertext pairs
- Invalid ciphertext length tests
- Invalid decapsulation key length tests  
- Invalid decapsulation key content tests (corrupted hash, corrupted embedded encapsulation key)

## Usage

```bash
go run .
```

Generates test vectors in the `gen/` directory:
- `gen/mlkem_512_semi_expanded_decaps_test.json`
- `gen/mlkem_768_semi_expanded_decaps_test.json`
- `gen/mlkem_1024_semi_expanded_decaps_test.json`

## Test Vector Format

Uses Wycheproof-compatible JSON format for consistency with existing test infrastructure.

## Reproducibility

Uses fixed seeds to ensure reproducible test vectors across runs.
