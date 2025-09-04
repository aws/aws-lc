# Jitter RNG SP800-90B Entropy Analysis Tool

This archive contains the SP800-90B analysis tool to be used for the Jitter RNG.
The tool set consists of the following individual tools:

- `recording_kernelspace`: This tool is used to gather the raw entropy of
  the Linux kernel space Jitter RNG.

- `recording_userspace`: This tools is used to gather the raw entropy of
  the user space Jitter RNG implementation.

- `validation-runtime`: This tool is used to calculate the minimum entropy
  values compliant to SP800-90B section 3.1.3.

- `validation-restart`: This tool is used to calculate the minimum entropy
  values for the restart test compliant to SP800-90B section 3.1.4

See the README files in the different subdirectories.

# Interpretation of Results

## Runtime Tests

The result of the data analysis performed with `validation-runtime` contains
in the file `jent-raw-noise-0001.minentropy_FF_8bits.var.txt` at the bottom data
like the following:

```
H_original: 2.387470
H_bitstring: 0.337104

min(H_original, 8 X H_bitstring): 2.387470
```

The last value gives you the entropy estimate per time delta. That means for one
time delta the given number of entropy in bits is collected on average.

Per default, the Jitter RNG heuristic applies 1/3 bit of entropy per
time delta. This implies that the measurement must show that *at least* 1/3 bit
of entropy is present. In the example above, the measurement shows that
2.3 bits of entropy is present which implies that the available amount of
entropy is more than what the Jitter RNG heuristic applies.

## Restart Tests

The results of the restart tests obtained with `validation-restart` contains
in the file `jent-raw-noise-restart-consolidated.minentropy_FF_8bits.var.txt`
at the bottom data like the following:

```
H_r: 0.545707
H_c: 1.363697
H_I: 0.333000

Validation Test Passed...

min(H_r, H_c, H_I): 0.333000
```

The last value gives you the entropy estimate per time delta for the restart
tests. That means for one time delta the given number of entropy in bits
collected on average.

Per default, the Jitter RNG heuristic applies 1/3 bit of entropy per
time delta. This implies that the measurement must show that 1/3 bit
of entropy is present. Unlike with the runtime tests, the restart tests
results compares the data against the Jitter RNG's H_I value of 1/3 bits.
Thus, the value must show 1/3 bits to show that sufficient entropy is
provided. In the example above, the measurement shows that
1/3 bits of entropy is present which implies that the available amount of
entropy is more than what the Jitter RNG heuristic applies.

# Approach to Solve Insufficient Entropy

The Jitter RNG does not need any specific configurations or settings. However,
in case your entropy assessment shows that insufficient entropy is
present (e.g. by showing that the measured entropy rate is less than 1/3), you
can perform a search whether different memory access values gives better
entropy.

## Tool for Searching for More Entropy

It is possible that the the default setting of the Jitter RNG does not deliver
sufficient entropy. It is possible to adjust the memory access part of the
Jitter RNG which may deliver more entropy.

To support analysis of insufficient entropy, the following tools are provided.
The goal of those test tools is to detect the proper memory setting that is
appropriate for your environment. One memory setting consists of two values,
one for the number of memory blocks and one for the memory block size.

- `recording_userspace/analyze_options.sh`: This tool generates a large number
  of different test results for different settings for the memory access. Simply
  execute the tool without any options. A large set of different test results
  directories are created.

- `validation-runtime/analyze_options.sh`: This tool analyzes all test results
  directories created by the `recording_userspace/analyze_options.sh` for
  the runtime data. It generates an overview file with all test results in
  `results-runtime-multi`. Analyze it and extract the memory access settings
  that gives you the intended entropy rate.

- `validation-restart/analyze_options.sh`: This tool analyzes all test results
  directories created by the `recording_userspace/analyze_options.sh` for
  the restart data. It generates an overview file with all test results in
  `results-restart-multi`. Analyze it and extract the memory access settings
  that gives you the intended entropy rate.

After you concluded the testing you have 2 memory settings that should be
appropriate for you. As you need exactly one memory setting, analyze again
the results to detect the memory setting that gives suitable entropy rates
for both, the runtime and restart tests.

Once you found the suitable memory setting, compile the Jitter RNG library
with the following defines:

`CFLAGS="-DJENT_MEMORY_BLOCKS=<blocks> -DJENT_MEMORY_BLOCKSIZE=<blocksize>"`

### Example - JENT_RANDOM_MEMACCESS not defined

For example, the test returns the following data (this list is truncated)

```
Number of blocks        Blocksize       min entropy
64      32       0.542445
64      64       0.232963
64      128      0.232486
64      256      0.231005
64      512      0.401778
64      1024     0.326805
64      2048     0.319931
64      4096     0.225761
64      8192     0.220877
64      16384    0.330431
128     32       0.069033
128     64       0.068805
128     128      0.221863
...
```

You now conclude that the following line is good for you:

```
64      512      0.401778
```

This now implies that your CFLAGS setting for compiling the Jitter RNG is

`CFLAGS="-DJENT_MEMORY_BLOCKS=64 -DJENT_MEMORY_BLOCKSIZE=512"`

Note, the Jitter RNG will allocate JENT_MEMORY_BLOCKS * JENT_MEMORY_BLOCKSIZE
bytes for its memory access operation.

### Example - JENT_RANDOM_MEMACCESS defined

For example, the test returns the following data

```
Number of bits  min entropy
10       0.406505
11       0.445082
12       0.402972
13       0.459021
14       0.436911
15       0.578995
16       0.643272
17       0.573532
18       0.627915
19       0.503923
20       0.720609
21       1.871527
22       2.491569
23       2.481533
24       2.493987
25       2.491303
26       2.495017
```

This stack tells you in the first column the actual amount of memory requested
to be allocated by the Jitter RNG for the memory access in powers of 2 (Note,
this amount is limited by the CPU's data cache size.). The second column is what
you can ignore for this test.

You now conclude that the following line is good for you because the measurement
shows that about 1 bit of entropy per Jitter RNG time delta is received. This
is compared with the Jitter RNG internally applied entropy rate of 1/3 bits
of entropy per time delta which means that the Jitter RNG heuristics
underestimates the available entropy - which is the result you want.

```
21       1.871527
```

This value means that the allocated memory is 2^21 = 2MBytes.

You now have two options how to apply this value: either recompiling the
library and use this value as the default allocation or use it as
a flags field when allocating your Jitter RNG instance which does not
need to change the binary.

When recompiling, you need to apply the value `21` with your
CFLAGS setting for compiling the Jitter RNG like this:

`CFLAGS="-DJENT_MEMORY_BITS=21"`

When using the value to allocate the Jitter RNG instance when you did not
recompile the library code you specify this value when invoking
`jent_entropy_init_ex` and `jent_entropy_collector_alloc` by adding the
following to your flags field:

```
unsigned int flags = 0;
...
flags |= JENT_MAX_MEMSIZE_2MB;

ret = jent_entropy_init_ex(0, flags);
...
ret = jent_entropy_collector_alloc(0, flags);
...

```

Note, the Jitter RNG will allocate 1 << JENT_MEMORY_BITS
bytes for its memory access operation, but at most what
jent_cache_size_roundup() returns.

# Author
Stephan Mueller <smueller@chronox.de>
