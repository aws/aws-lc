# Obtain Raw Noise Data

This tool offers the collection of raw entropy from the running Linux
kernel Jitter RNG, compliant to SP800-90B section 3.1.3

To obtain raw noise data from the Jitter RNG, follow these steps:

1. Ensure patch providing kernel Jitter RNG test interface is applied,
   select `CONFIG_CRYPTO_JITTERENTROPY_TESTINTERFACE`, compile, install and
   reboot the kernel - if you want to stimulate the generation of entropy
   with the command below, ensure the kernel option
   `CONFIG_CRYPTO_USER_API_RNG` is set to `m` or `y`.

2. Compile getrawentropy.c as documented in that file

3. Execute as root to obtain the raw entropy data:
	`getrawentropy -f /sys/kernel/debug/jitterentropy_testing/jent_raw_hires -s 1000001 > /dev/shm/jent_raw_noise.data`

4. In parallel to step 3, stimulate the generation of entropy, e.g. by using
   the following command with a tool from libkcapi using the following command
	`kcapi-rng -n "jitterentropy_rng" -b 2000000 > /dev/null`

5. Process the obtained data with validation-runtime-kernel/processdata.sh
