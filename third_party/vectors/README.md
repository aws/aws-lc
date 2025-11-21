# Third-Party Test Vectors

This directory contains cryptographic test vectors from external sources for use in AWS-LC's tests.

## Directory Structure

- `upstream/` - Raw test vectors from third-party sources (checked in for transparency)
- `converted/` - Test vectors converted to our `file_test.h` format (consumed by tests)
- `vectors_spec.md` - Auto-generated specification listing all test vectors
- `sync.py` - Script that updates upstream test vectors, converts them to the `file_test.h` format, and generates `vectors_spec.md`

## Workflow

### Sync Vectors

`./sync.py` fetches the latest versions of test vectors from upstream, converts them, and updates the specification. 

`./sync.py --check` only checks and does not make any changes. It returns `0` if all files are up-to-date and converted correctly. It returns `1` if there's outdated files or incorrectly converted files.

### Adding New Source of Test Vectors

Add the upstream git url of the new source to `sources.toml`. Now, you can add test vectors from this source.

### Adding New Test Vectors from Existing Source

The following command adds a new vector and re-runs sync:
```
./sync.py --new [SOURCE_NAME]/[UPSTREAM_REPO_PATH_TO_FILE] 
```
The path needs to include the source name from `sources.toml` and the file path relative to the upstream repository, for example `wycheproof/testvectors_v1/aes_gcm_test.json`.

## Requirements Traceability

The `vectors_spec.md` file lists all test vectors using the MUST keyword. Test files include duvet annotations linking them to the specification:

```cpp
//= third_party/vectors/vectors_spec.md#wycheproof
//= type=test
//# AWS-LC MUST test against `testvectors_v1/aes_gcm_test.txt`.
TEST(AEADTest, WycheproofAESGCM) { ... }
```

The [duvet](https://github.com/awslabs/duvet) tool tracks which test vectors are used and where. It verifies that annotations haven't been removed, but does not verify test coverage. This helps document which vectors we use and maintain traceability.

Duvet runs automatically when `sync.py` executes. To manually verify:

```bash
cd third_party/vectors
duvet report --ci
```
