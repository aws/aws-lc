3.6.2
 * Fix RCT re-initialization in jent_read_entropy_safe (thanks to Joshua Hill for pointing this out)
 * simplify test code
 * improve keyword portability

3.6.1
 * Add more test code
 * Add support for SunPRO compiler
 * Fix compilation on OpenBSD by replacing sed with tr
 * internal timer: Add support for Apple
 * Various small fixes to compilation to imporve portability

3.6.0
 * Remove bi-modal behavior of conditioning function
 * Make jent_read_entropy_safe safer by retrying the health test
 * Move the version information to make them available at compile time

3.5.0
 * add distinction between intermittent and permanent health failure

 * add compile time option to allow configuring a mask to reduce the size of
   the time stamp used for the APT

3.4.1
 * add FIPS 140 hints to man page
 * simplify the test tool to search for optimal configurations
 * fix: jent_loop_shuffle: re-add setting the time that was lost with 3.4.0
 * enhancement: add ARM64 assembler code to read high-res timer

3.4.0
 * enhancement: add API call jent_set_fips_failure_callback as requested by Daniel Ojalvo
 * fix: Change the SHA-3 integration: The entropy pool is now a SHA-3 state.
It is filled with the time delta containing entropy and auxiliary data that does not contain entropy using a SHA update operation. The auxiliary data is calculated by a SHA-3 hashing of some varying state data. The time delta that contains entropy is measured about the SHA-3 hasing of the auxiliary data. This satisfies FIPS 140-3 IG D.K resolutions 4, 6, and 8.
 * enhancement: add CMake support by Andrew Hopkins

3.3.1
 * fix: bug fix in initialization logic by Vladis Dronov <vdronov@redhat.com>
 * fix: use __asm__ instead of asm to suit the C11 standard

3.3.0
 * add jent_get_cachesize if _SC_LEVEL1_DCACHE_SIZE is not defined
 * limit the memory buffer size allocated and allow caller to provide
   the means to provide a limit, too
 * fix: update man page
 * update README explaining how to handle entropy shortfall to make it consistent with the current code base

3.2.0
 * fix: add API call jent_read_entropy_safe to header file
 * enhancement: add jent_entropy_init_ex API call
 * enhancement: call jent_entropy_init_ex automatically when jent_entropy_collector_alloc_internal detects that no self test has yet been performed
 * test: provide jitterentropy-rng test tool allowing all options exported by the library to be invoked
 * fix: re-add check of time_backwards in power-on test
 * fix: silence static code analysis tool
 * test: add test for GCD
 * enhancement: add GCD selftest
 * fix: simplify memory management for SHA-3
 * enhancement: add random memory access (JENT_RANDOM_MEMACCESS)

3.1.0
 * Add link call to pthreads library as suggested by Mikhail Novosyolov
 * Add ENTROPY_SAFETY_FACTOR to apply consideration of asymptotically reaching
   full entropy following SP800-90C suggested by Joshua Hill
 * Add test for finiding more entropy by changing the memory buffer size
   used for the memory access loop
 * Increase the memory buffer size to 512 kBytes per default based on
   measurements on systems with low entropy.
 * Add jent_ncpu() detecting the number of existing CPUs. Only when more than
   one CPU is in the system, the internal timer thread is started.
 * add GCD testing and analysis suggested by Joshua Hill
 * add fixes to APT suggested by Joshua Hill
 * add lag predictor health test suggested by Joshua Hill
 * add jent_read_entropy_safe API call
 * break up jitterentropy-base.c into various smaller code files

3.0.2
 * Small fixes suggested by Joshua Hill
 * Update the invocation of SHA-3 invocation: each loop iteration defined by the loop shuffle is a self-contained SHA-3 operation. Therefore, the conditioning information is always *one* SHA-3 operation with different time duration.
 * add JENT_CONF_DISABLE_LOOP_SHUFFLE config option allowing disabling of the shuffle operation
 * Use -O0

3.0.1
 * on older GCC versions use -fstack-protector as suggested by Warszawski,
   Diego
 * prevent creating the internal timer thread if a high-res hardware timer is
   found as reported by Lonnie Abelbeck

3.0.0
 * use RDTSC on x86 directly instead of clock_gettime
 * use SHA-3 instead of LFSR
 * add internal high-resolution timer support

2.2.0
 * SP800-90B compliance: Add RCT runtime health test
 * SP800-90B compliance: Add Chi-Squared runtime health test as a replacement
   for the adaptive proportion test
 * SP800-90B compliance: Increase initial entropy test to 1024 rounds
 * SP800-90B compliance: Invoke runtime health tests during initialization
 * remove FIPS 140-2 continuous self test (RCT covers the requirement as per
   FIPS 140-2 IG 9.8)
 * SP800-90B compliance: Do not mix stuck time deltas into entropy pool

2.1.2:
 * Add static library compilation thanks to Neil Horman
 * Initialize variable ec to satisfy valgrind as suggested by Steve Grubb
 * Add cross-compilation support suggested by Lonnie Abelbeck

2.1.1:
 * Fix implementation of mathematical properties.

2.1.0:
 * Convert all __[u|s][32|64] into [uint|int][32|64]_t
 * Remove all code protected by #if defined(__KERNEL__) && !defined(MODULE)
 * Add JENT_PRIVATE_COMPILE: Enable flag during compile when
   compiling a private copy of the Jitter RNG
 * Remove unused statistical test code
 * Add FIPS 140-2 continuous self test code
 * threshold for init-time stuck test configurable with JENT_STUCK_INIT_THRES
   during compile time

2.0.1:
 * Invcation of stuck test during initalization

2.0.0:
 * Replace the XOR folding of a time delta with an LFSR -- the use of an
   LFSR is mathematically more sound for the argument to maintain entropy

1.2.0:
 * Use constant time operation of jent_stir_pool to prevent leaking
   timing information about RNG.
 * Make it compile on 32 bit archtectures

1.1.0:
 * start new numbering schema
 * update processing of bit that is deemed holding no entropy by heuristic:
   XOR it into pool without LSFR and bit rotation (reported and suggested
   by Kevin Fowler <kevpfowler@gmail.com>)

