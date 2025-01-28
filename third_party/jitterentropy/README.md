Hardware RNG based on CPU timing jitter
=======================================

The Jitter RNG provides a noise source using the CPU execution timing jitter.
It does not depend on any system resource other than a high-resolution time
stamp. It is a small-scale, yet fast entropy source that is viable in almost
all environments and on a lot of CPU architectures.

The implementation of the Jitter RNG is independent of any operating system.
As such, it could even run on baremetal without any operating system.

The design of the RNG is given in the documentation found in at
http://www.chronox.de/jent . This documentation also covers the full
assessment of the SP800-90B compliance as well as all required test code.

API
---

The API is documented in the man page jitterentropy.3.

To use the Jitter RNG, the header file jitterentropy.h must be included.

Build Instructions
==================

To generate the shared library `make` followed by `make install`.

Android
-------

To compile the code on Android, use the following Makefile:

arch/android/Android.mk	-- NDK make file template that can be used to directly
			   compile the CPU Jitter RNG code into Android binaries

Direct CPU instructions
-----------------------

If the function in jent_get_nstime is not available, you can replace the
jitterentropy-base-user.h with examples from the arch/ directory.

Testing
=======

There are numerous tests around the Jitter RNG. Yet, they are too big to be
loaded into the official repository. Email me, if you want them.

Version Numbers
===============
The version numbers for this library have the following schema:
MAJOR.MINOR.PATCHLEVEL

Changes in the major number implies API and ABI incompatible changes, or
functional changes that require consumer to be updated (as long as this
number is zero, the API is not considered stable and can change without a
bump of the major version).

Changes in the minor version are API compatible, but the ABI may change.
Functional enhancements only are added. Thus, a consumer can be left
unchanged if enhancements are not considered. The consumer only needs to
be recompiled.

Patchlevel changes are API / ABI compatible. No functional changes, no
enhancements are made. This release is a bug fixe release only. The
consumer can be left unchanged and does not need to be recompiled.

Author
======
Stephan Mueller <smueller@chronox.de>
