# Third-Party Test Vectors

This directory contains cryptographic test vectors from external sources for use in AWS-LC's tests.

## Directory Structure

- `upstream/` - Raw test vectors from third-party sources (checked in for transparency)
- `converted/` - Test vectors converted to our `file_test.h` format (consumed by tests)
- `vectors_spec.md` - Listing of included test vectors in [RFC2119](https://www.rfc-editor.org/rfc/rfc2119) format for use by the `duvet` tool
- `sync.py` - Script that updates upstream test vectors, converts them to the `file_test.h` format, and updates the `vectors_spec.md` specification.

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
