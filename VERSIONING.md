# AWS-LC Versioning

This document describes how AWS-LC is versioned and released, and how consumers should choose between the release types we offer.

## Overview

AWS-LC offers two release types:

* **Rolling mainline releases** are the primary release for most consumers. Rolling mainline receives the latest features, performance improvements, and security fixes as they are developed.
* **Long-term support (LTS) releases** are intended for consumers that require a stable ABI over a multi-year support window.

Rolling mainline is periodically submitted for FIPS 140-3 validation, though changes may land between submissions. LTS branches are fixed FIPS submissions; they are not modified after they are cut, except for the backports permitted by the [LTS release policy](#lts-release-policy). The FIPS version number a given build corresponds to is tracked independently of the AWS-LC version number (see [FIPS version number](#fips-version-number)).

AWS-LC is committed to providing a stable public API across both release types. LTS releases additionally guarantee ABI stability for the duration of the support window.

## AWS-LC version numbers

AWS-LC releases follow a `MAJOR.MINOR.PATCH` scheme. Mainline uses only major and minor; FIPS branches (LTS and non-LTS snapshot) use only minor and patch.

* **Major** (`X.0.0`):
  * Bumped on mainline when a new LTS branch is cut (see [LTS version evolution](#lts-version-evolution)).
  * Signals that the previous major line now belongs to an LTS branch and mainline has moved to a new major line.
* **Minor** (`X.Y.0`):
  * The only increment used on mainline. Every mainline release bumps minor, regardless of the size or kind of change (features, security fixes, performance improvements, bug fixes, platform compatibility fixes, etc.).
  * Also used on LTS branches for backwards compatible features that do not break API/ABI compatibility.
* **Patch** (`X.Y.Z`):
  * Used only on FIPS branches (LTS or non-LTS snapshot) for non-additive changes — security fixes, bug fixes, and platform compatibility fixes.
  * Mainline never produces patch versions, so patch increments on FIPS branches cannot collide with mainline.

AWS-LC version numbers do not follow Semantic Versioning. Major version bumps on mainline are tied to LTS branch cuts (see [LTS version evolution](#lts-version-evolution)) and do not necessarily indicate API or ABI breaking changes. Consumers needing to detect public API surface changes can use the `AWSLC_API_VERSION` macro defined in `openssl/base.h`, which increments when the API surface changes.

A build's AWS-LC version can be queried at runtime via the `awslc_version_string` API:

```c
OPENSSL_EXPORT const char *awslc_version_string(void);
```

AWS-LC version numbers are independent of the FIPS version number. A bump in either does not imply a bump in the other. To identify the FIPS submission a build corresponds to, use `FIPS_version` (see [FIPS version number](#fips-version-number)).

## FIPS version number

The FIPS version number is an integer that identifies a specific FIPS validation submission. It is incremented each time a new FIPS branch is cut from mainline and corresponds to the value used in our submissions to the NIST Cryptographic Module Validation Program (CMVP). Mainline tracks the most recent FIPS version number that has been cut from it.

The FIPS version number is decoupled from the AWS-LC version number. A build's FIPS version number can be queried at runtime via the `FIPS_version` API:

```c
OPENSSL_EXPORT uint32_t FIPS_version(void);
```

Prior to this scheme, AWS-LC version numbers and FIPS version numbers were coupled (for example, AWS-LC FIPS 3.0 corresponded to the third FIPS submission). That coupling has been removed. Earlier FIPS branches still carry version numbers matching their FIPS version number, and their FIPS version number is documented in the security policy published alongside each validation.

## Release types

### Rolling mainline

Mainline is the primary release for AWS-LC consumers. It receives all new features, performance improvements, and security fixes as they are developed.

Rolling mainline characteristics:

* Latest features, performance improvements, and security fixes.
* Submitted for FIPS validation approximately every 6 months.

### LTS releases

LTS releases are intended for consumers that require a stable ABI. An LTS branch is cut from mainline and then receives only the changes permitted by the [LTS release policy](#lts-release-policy).

LTS release characteristics:

* Cut from mainline every 2 years and supported for 5 years from the date the branch is cut.
* Each LTS branch is submitted for FIPS validation.

Both rolling mainline releases and LTS releases are tagged in the public repository; non-LTS FIPS branches are not.

## LTS release policy

### LTS version evolution

Each LTS branch inherits mainline's major version at the time it is cut. In the next commit, mainline bumps to the next major version. This guarantees that mainline and every LTS branch have distinct major version numbers.

For example, when mainline is at `4.13.0` and an LTS branch is cut, the `4.x` version prefix is reserved exclusively for the LTS branch. The `4.x` line receives only the changes permitted below, as patch (`4.13.1`, `4.13.2`, ...) or minor (`4.14.0`, `4.15.0`, ...) increments. Mainline advances to `5.0.0` and continues normal development with minor increments only (`5.1.0`, `5.2.0`, ...). Because mainline never returns to the `4.x` line, version numbers on the LTS cannot collide with mainline. When the next LTS is cut approximately two years later, it takes ownership of whatever major version line mainline is on at that moment, and mainline bumps again.

### Permitted changes on LTS branches

The following are permitted on LTS branches, mapped to version increments:

* Minor increments:
  * Additive changes that preserve existing function signatures.
* Patch increments:
  * Security fixes for CVEs and critical vulnerabilities. These may alter the FIPS module integrity hash when necessary.
  * Bug fixes that do not alter public API behavior, ABI compatibility, or the FIPS module integrity hash.
  * Platform compatibility fixes for supported operating environments that do not alter the FIPS module integrity hash.

See [AWS-LC version numbers](#aws-lc-version-numbers) for the full scheme.

### Not permitted on LTS branches

The following are not permitted on LTS branches:

* API or ABI breaking changes.
* Changes within the FIPS module boundary that alter the integrity hash, unless required for a security fix.
* New features or algorithms that alter the FIPS module.
* Performance improvements that alter the FIPS module or change behavioral characteristics.

### Support window

Each LTS branch is supported for 5 years from the date the branch is cut. End of support (EOS) means security fixes and other changes are no longer backported to the branch. EOS applies regardless of the status of any FIPS certificate associated with the branch; once an LTS reaches EOS, consumers should migrate to mainline or to a newer LTS.

At any given time, at least one LTS branch is within its support window. Consecutive LTS branches overlap so that consumers always have a supported migration target.

## Non-LTS FIPS branches

FIPS validation requires a fixed snapshot of the cryptographic module's source code. Each time AWS-LC is submitted for FIPS validation, a branch is cut from mainline that preserves the exact code submitted. Most of these branches are not designated as LTS. LTS designation is decided at branch-cut time; existing non-LTS branches are never promoted to LTS.

Non-LTS FIPS branches exist solely to preserve the validated snapshot. They do not receive release tags, and consumers should not depend on them.

We may apply critical security fixes to a non-LTS FIPS branch from the time it is cut until a newer FIPS branch (LTS or non-LTS) receives NIST certification and supersedes it. This is a maintenance concession; these branches are not supported for consumption. Once superseded, the previous non-LTS branch is frozen and receives no further updates.

A non-LTS FIPS branch inherits its version from mainline at cut time and only ever issues patch-level increments (e.g., a branch cut at `5.6.0` becomes `5.6.1` after a security fix). Because mainline only produces minor increments (`5.6.0` → `5.7.0`), patch versions on a non-LTS branch cannot collide with mainline.

At branch-cut time, the non-LTS branch and mainline are the same build; `awslc_version_string()` and `FIPS_version()` return identical values on both. They diverge afterward — mainline through its next minor release, the non-LTS branch through any patch-level security fixes.

## Branch naming conventions

Going forward, FIPS branches use a suffix to indicate their release type:

* `fips-YYYY-MM-DD-lts` — LTS branch. Receives security fixes and other permitted changes throughout its support window.
* `fips-YYYY-MM-DD-snapshot` — Non-LTS validation snapshot. Frozen once it is no longer the most recently NIST-certified FIPS branch.

The date in the branch name corresponds to the date the branch was cut for FIPS submission. Branches cut before this convention was adopted retain their original names.

## Deprecation of legacy FIPS branches

`fips-2025-09-12-lts` (AWS-LC FIPS 4.x) is the first branch designated as LTS under this versioning scheme. It is supported for 5 years from its cut date (approximate EOS: September 2030).

FIPS branches published before this scheme have the following deprecation timelines:

| Branch            | End of support     |
|-------------------|--------------------|
| AWS-LC FIPS 1.0   | October 2026       |
| AWS-LC FIPS 2.0   | April 2027         |
| AWS-LC FIPS 3.0   | April 2028         |

After a branch reaches end of support, security fixes will no longer be backported. Consumers on these branches should migrate to mainline or to the FIPS 4.x LTS branch before the listed date.
