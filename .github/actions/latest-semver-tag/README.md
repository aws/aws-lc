# Latest Semantic Version Tag Action

A GitHub Action that determines the latest tagged git release following semantic versioning and outputs that value for subsequent steps to use.

## Inputs

| Input | Description | Required | Default | Allowed Values |
|-------|-------------|----------|---------|----------------|
| `release` | The release type to filter tags by | Yes | `main` | `main`, `fips1`, `fips2`, `fips3` |
| `path` | The path containing the git repository to check | No | `.` | Any valid directory path |

## Outputs

| Output | Description |
|--------|-------------|
| `latest-tag` | The latest semantic version tag (format depends on release type) |
| `latest-version` | The latest semantic version without the prefix (format depends on release type) |

### Tag Formats by Release Type

- For `main` release: Tags in `vX.Y.Z` format (e.g., `v1.2.3`)
- For `fipsN` releases: Tags in `AWS-LC-FIPS-N.Y.Z` format (e.g., `AWS-LC-FIPS-1.2.3` for `fips1`)

## Usage

```yaml
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Get Latest Tag
        id: latest-tag
        uses: ./.github/actions/latest-semver-tag
        with:
          release: 'main'  # Optional: Allowed values: main, fips1, fips2, fips3
          path: '.'   # Optional: Directory containing the git repository
      
      - name: Use Latest Tag
        run: |
          echo "Latest tag is ${{ steps.latest-tag.outputs.latest-tag }}"
          echo "Latest version is ${{ steps.latest-tag.outputs.latest-version }}"
```

## How It Works

This action:

1. Validates the provided `release` input parameter (must be one of: `main`, `fips1`, `fips2`, `fips3`)
2. Validates that the specified path exists and is a git repository if provided
3. Fetches all tags from the repository
4. Based on the release type:
   - For `main`: Filters tags to only include those that follow the format `vX.Y.Z`
   - For `fipsN`: Filters tags to only include those that follow the format `AWS-LC-FIPS-N.Y.Z` where N matches the FIPS version
5. Sorts the tags according to semantic versioning rules
6. Determines the latest tag (fails if no matching tag is found)
7. Outputs the latest tag and version (without the prefix)

## Requirements

- The repository must use semantic versioning tags in the appropriate format:
  - For `main` release: Tags in `vX.Y.Z` format
  - For `fipsN` releases: Tags in `AWS-LC-FIPS-N.Y.Z` format
- The checkout action must be configured with `fetch-depth: 0` to fetch all tags
