# Security Issues

The following list tries to enumerate all security issues on a best-effort
basis.

# Reporting Of Issues

If you detect any new security issues, please file a bug report or send
a private email to <smueller@chronox.de>.

## 2024-12-30

The API call `jent_read_entropy_safe` contains the logic to transparently handle
intermittent health test errors by reallocating a new Jitter RNG entropy
collector handle and increasing the OSR as well as the memory usage. During that
reallocation, the currently observed APT and RCT counter values are copied info
the new handle. That copy operation contains an failure for the RCT which
effectively disabled the RCT for all newly allocated entropy collector
instances - the other health tests as well as the Jitter RNG itself operates
still as expected with the newly allocated entropy collector instances. Thanks
to Joshua Hill for pointing this issue out.
