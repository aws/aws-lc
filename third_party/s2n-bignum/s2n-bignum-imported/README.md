## s2n-bignum

s2n-bignum is a collection of integer arithmetic routines designed for
cryptographic applications. All routines are written in pure machine code,
designed to be callable from C and other high-level languages, with separate but
API-compatible versions of each function for 64-bit x86 (x86_64) and ARM
(aarch64).

s2n-bignum's primary goals are performance and assurance: Assembly routines are
tuned for highest performance both by hand and using automatic optimization
techniques such as the [SLOTHY](https://github.com/slothy-optimizer/slothy)
superoptimizer, and each function is accompanied by a machine-checked formal
proof in [HOL-Light](https://hol-light.github.io/) that its mathematical
result is correct, based on a formal model of the underlying machine. Each
function is moreover written in a constant-time style to avoid timing
side-channels.

For the SHA-3 and ML-KEM code currently part of s2n-bignum, some of the
comments in the main part of this README do not apply exactly. See the section
[ML-KEM code](#ml-kem-code) below for more details.

### Building

Assuming a suitable operating system (e.g. Linux, Mac OS X, or Windows with
Cygwin) and a few basic build tools you should be able to download the repo and
build with just a few basic commands. On an x86 machine:

    git clone https://github.com/awslabs/s2n-bignum
    cd ./s2n-bignum
    (cd ./x86; make)

while on an ARM machine (aarch64, arm64) just replace "x86" with "arm":

    git clone https://github.com/awslabs/s2n-bignum
    cd ./s2n-bignum
    (cd ./arm; make)

This results in a library of bignum mathematical functions that can be
called from C or other languages. To run basic unit tests on the library
just built:

    (cd ./tests; make go)

To run the benchmarking code to get performance numbers for your platform
(this usually takes several minutes):

    (cd ./benchmarks; make go)

The code is all written in assembler, with each individual mathematical
function consisting of a `.S` file that can be assembled by directly
invoking the GNU C compiler `gcc` or by explicitly combining the C
preprocessor and an assembler or other C or C++ compiler. If using your own
build command, consult the existing Makefiles for guidance since there are some
subtle variations even among assemblers (e.g. some C compilers won't handle
multiple instructions per line when taking in assembler files).

### Using the library

The build process above results in a library that can be used to provide all
the functionality together (e.g. `x86/libs2nbignum.a` for an x86 machine),
as well as individual object files, one per function, that can be used for more
fine-grained linkage (e.g. `x86/generic/bignum_add.o` for the addition
function on x86). The functions all use standard Application Binary Interfaces
to connect to C and other high-level languages; the ABI determines, for
example, which registers or stack frames hold the arguments to a function when
called. The x86+Windows combination uses a non-standard ABI, which can
explicitly be forced using the additional option `-DWINDOWS_ABI=1` when
building. In either case the C-level prototypes for the functions are collected
in a header file that can be included in C programs to specify the interfaces.
A quick browse through this also gives an idea of what functions the
library provides.

[s2n-bignum/include/s2n-bignum.h](https://github.com/awslabs/s2n-bignum/blob/main/include/s2n-bignum.h)

You can include this in a C program as usual, after first including
the standard header defining the types `uint64_t` etc. that are
basic for s2n-bignum:

    #include <inttypes.h>
    #include "s2n-bignum.h"

Here is a small complete C program `myprogram.c` calling the
library, computing the modular inverse of 12345 modulo the wordsize
using the `word_negmodinv` function provided by the library,
then printing out confirmation that it works:

```
#include <stdio.h>
#include <inttypes.h>
#include "s2n-bignum.h"

int main(void)
{
  uint64_t x = 12345;
  uint64_t y = -word_negmodinv(x);
  printf("%ld * %ld = %ld (mod 2^64)\n",x,y,x*y);
}
```

Assuming you are on an x86 machine in a directory above the
`s2n-bignum` subdirectory (otherwise change the `.`
below into an appropriate path and/or change `x86` to `arm`),
you can compile this as follows, specifying the paths to the
library itself and the headers:

    gcc -o myprogram myprogram.c -I./s2n-bignum/include/ -L./s2n-bignum/x86/ -ls2nbignum

and then run it as usual to see the output:

    $ ./myprogram
    12345 * 5288216061308878345 = 1 (mod 2^64)

### Architectural and microarchitectural considerations

The overall C-level interface supported by the library is the same
regardless of architecture, ARM or x86. In each case, however, there
are some architectural and microarchitectural considerations to be
aware of:

  * On ARM, each function will work correctly on any existing
    microarchitecture. However, some functions have two variants
    with significant performance differences according to platform.
    The versions with `_alt` suffixes are designed to maximize
    performance on microarchitectures with higher multiplier
    throughput (typically more recent ones, like the Apple M1), while
    the non-alt variants are better suited to 'traditional' ARM
    microarchitectures with lower multiplier throughput (specifically,
    limited pipelining of the `UMULH` instruction to get the
    high part of a 64x64-bit product).

  * On x86, all generic bignum functions (in the `x86/generic`
    subdirectory) will work correctly on any existing microarchitecture.
    Some of the more highly optimized functions for specific elliptic
    curves etc. require the BMI and ADX instruction set extensions
    (specifically the `MULX`, `ADCX` and `ADOX` instructions).
    In such cases, the `_alt` suffix forms are provided
    as a backup that will work for older platforms. In all cases where
    there is such an alt form provided, the non-alt form is likely to be
    faster where those instructions are supported, as on most recent
    x86-64 chips.

If you are unsure which version of a function to use on your platform, a simple
test is to run the benchmarking code (see above) and examine the results. For
example, this is a contemporary ARM platform where the alt form performs
better:

```
...
curve25519_x25519               : 26661.8 ns each (var  0.8%, corr  0.03) =      37507 ops/sec
curve25519_x25519_alt           : 19297.7 ns each (var  0.4%, corr -0.03) =      51820 ops/sec
...
```

and this is a typical x86 chip where the non-alt form is faster:

```
...
curve25519_x25519               : 30103.0 ns each (var  0.0%, corr -0.14) =      33219 ops/sec
curve25519_x25519_alt           : 38097.0 ns each (var  0.0%, corr -0.11) =      26249 ops/sec
...
```

while this is a very old x86 machine where the required instructions for
the non-alt form are not supported:

```
...
curve25519_x25519               :             *** NOT APPLICABLE  ***
curve25519_x25519_alt           : 51977.2 ns each (var  1.4%, corr  0.01) =      19239 ops/sec
...
```

### Constant-time bignums

The s2n-bignum library provides a simple and flexible API for manipulating
bignums, which are integers of arbitrary size (operations focus on nonnegative
integers, but use 2s complement where appropriate for negation). The integers
are represented as little-endian arrays of unsigned 64-bit "digits", where the
digits can be accessed via the standard `uint64_t` type in C. They can be
explicitly read and written as normal C arrays as well as via the s2n-bignum
API. For example, here is how one might set up the constant 2<sup>255</sup>-19
as a 4-digit bignum (note the little-endian digit representation, independent
of the byte order of the underlying machine):

```
uint64_t p_25519[4] =
{
   UINT64_C(0xffffffffffffffed),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0x7fffffffffffffff)
};
```

The arrays can be arbitrarily large or small and the sizes can be runtime
parameters, with no overall restriction to specific sizes like 4 in the example
above. However, in contrast to many standard bignum interfaces like that
supported by [GMP](https://gmplib.org/), the operations do not dynamically
adjust the sizes, but require them to be explicitly specified by the user when
calling each function. The reason for this is to allow flexibility and
genericity while also enforcing "constant-time" behavior for security from
timing side-channels in cryptographic applications.

By "constant-time" we mean roughly that a given bignum operation takes a time
that is independent of the actual numbers involved, depending only on their
*nominal* sizes. Each s2n-bignum operation takes and returns bignums
of specified nominal sizes, and manipulates them on the basis of the nominal
sizes only, independent of their actual numeric values (even if those are
zero). If a result does not fit in the size provided, it is systematically
truncated modulo that size. s2n-bignum functions never strip away leading
zeros to make numbers shorter, nor do they allocate extra space to make them
longer; indeed, they perform no memory allocation or other OS calls at all.
For instance, the basic multiplication function has the following C prototype:

```
void bignum_mul(uint64_t p,uint64_t *z, uint64_t m,uint64_t *x, uint64_t n,uint64_t *y);
```

This means that `x` points to an `m`-digit bignum (little-endian, with
64-bit words as the digits), `y` points to an `n`-digit bignum, and the
function writes their product to the `p`-word buffer pointed to by `z`,
truncating it modulo 2<sup>64p</sup> if it doesn't fit. In this setting
with nominal sizes for all numbers, the "constant-time" characteristic means
that the actual sequence of machine instructions executed, including the
specific addresses and sequencing of memory loads and stores, is
*independent of the numbers themselves*, depending only on their nominal sizes
(`m`, `n` and `p` for the above example).

Since the s2n-bignum interface is just using pointers to pre-existing arrays,
any allocation of memory is the caller's responsibility. Some s2n-bignum
functions use space on the stack for intermediate computations (or just to save
and restore registers), but only in cases where that size is bounded and
moderate. For the few generic-size functions that need similarly generic (and
hence unbounded a priori) space for intermediate storage, it needs to be
provided by the caller via an additional argument. For example, the final
argument to the `bignum_modinv` (modular inverse) function is to a temporary
buffer of a size depending on the generic size parameter `k` (specifically,
according to the API it should be `>= 3 * k`):

```
void bignum_modinv (uint64_t k, uint64_t *z, uint64_t *a, uint64_t *b, uint64_t *t);
```

In order to keep the generic API more convenient, minimizing the need for such
additional parameters, functions sometimes read from and write to the provided
buffers in interleaved fashion in a way that assumes inputs and outputs do not
overlap. Aliasing of input and output buffers is however usually allowed in
fixed-size functions and (provided they are exactly the same, not overlapped in
more intricate fashion) "linear" generic-sized functions; consult the detailed
API reference for more details.

### What's in the library?

The s2n-bignum library supports basic bignum arithmetic using the API specified
above, as well as a host of related operations, the aim being to provide
convenient and reliable building-blocks for higher-level cryptographic
functionality. The range of operations provided covers:

- Elementary operations on 64-bit words, mainly to provide reference
  implementations that are constant-time, e.g. `word_max` (maximum),
  `word_clz` (counting leading zeros)

- Basic generic-size bignum arithmetic functionality like `bignum_add`
  (addition), `bignum_sub` (subtraction), `bignum_mul` (multiplication),
  `bignum_eq` (equality comparison).

- Generic-size constant-time data manipulation like `bignum_digit` (selecting
  a digit, like array indexing but without any difference in memory access
  pattern from element number) and `bignum_mux` (multiplexing or if-then-else,
  analogous to C `b ? x : y`.

- Generic-size Montgomery operations like `bignum_montmul` (Montgomery
  multiplication), `bignum_montredc` (Montgomery reduction) and
  `bignum_montifier` (computes constant for mapping into Montgomery form)
  for performing modular arithmetic in Montgomery form for any odd modulus.

- Optimized multiplication and squaring operations for specific sizes, e.g.
  `bignum_mul_4_8` (multiply two 4-digit numbers with 8-digit result) and
  `bignum_sqr_16_32` (square a 16-digit number with 32-digit result).

- Optimized modular and/or Montgomery arithmetic operations for common
  primes that are field characteristics for  specific elliptic curves,
  e.g. `bignum_montmul_p521` (Montgomery multiplication modulo
  2<sup>521</sup>-1) for NIST P-521, `bignum_sqr_p25519` (modular
  squaring modulo 2<sup>255</sup>-19 for curve25519).

- Full top-level point operations for supported elliptic curves, e.g.
  `p256_jadd` (point addition on NIST P-256 curve), `secp256k1_jdouble`
  (point doubling for secp256k1). These usually assume a particular
  coordinate representation, Jacobian in these cases (hence the "j").

The elliptic curves with some special support are the following; the degree of
support varies from just modular and/or Montgomery arithmetic operations for
the field characteristic modulus, up to basic point operations, and even in
some cases full scalar multiplication (e.g. `curve25519_x25519`).

- curve25519/edwards25519
- NIST P-256
- NIST P-384
- NIST P-521
- secp256k1
- SM2

### Testing and formal verification

The basic testing setup as mentioned above subjects each function to a number
of unit tests, mainly using pseudo-random inputs and comparing against
conceptually simpler (but neither efficient nor constant-time) C references,
also doing some checking of pre-tabulated "known correct" results. This
process

    (cd ./tests; make go)

should be enough to expose any basic problems, typically failure to assemble
and link the code correctly. However, in pursuit of the highest standards of
correctness, that basic testing is complemented by the far more rigorous and
sophisticated process of *formal verification*.

The formal verification process performs a machine-checked proof that the
actual object file generated by the build process satisfies a high-level
mathematical specification for *all* inputs (not just for specific test cases),
assuming a formal model of how each processor (ARM or x86) executes code. These
models make some simplifications and idealizations but model pretty faithfully
the way in which specific machine instructions modify registers, flags and
memory.

To perform the formal proof for a particular function, you will need to install
the latest version of [HOL Light](https://github.com/jrh13/hol-light/).
The OPAM version might not work because it does not contain sufficiently recent
libraries.
To install HOL Light, please follow its
[README](https://github.com/jrh13/hol-light/blob/master/README) instruction.
After installation, set the `HOLDIR` environment variable to the path of
the `hol-light` directory and use the Makefile within either the `arm` or
`x86` directories to generate a target of the form
`function_name.correct` for a corresponding object file `function_name.o`.
Alternatively, the entire collection of functions can all be formally proved
via the `proofs` pseudo-target. This is likely to be very time-consuming and
hence better executed with some parallelism, e.g.

    nohup make -j 16 proofs &

The proof process is controlled by a corresponding "proof script" in the
`proofs` subdirectory with corresponding name `proofs/function_name.ml`
The technical details of how the machine is modeled and how the proof is
performed are too involved to enter into in detail in this brief summary,
but by examining the proof script file you can find detailed specifications
for each function, which might be considered the most rigorous possible
form of API documentation.

For example the file `arm/proofs/bignum_mul_p25519.ml` starts with a lengthy
sequence of 32-bit words that specify the machine code being verified. This is
not just accepted a priori as the canonical machine code, but actually checked
against the object file to make sure it is indeed what is generated by the
build process. The later proof then shows that executing this on the idealized
machine model guarantees some toplevel mathematical properties. In this case,
the specification that is proved looks like this:

```
nonoverlapping (word pc,0x288) (z,8 * 4)
 ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) bignum_mul_p25519_mc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [z; x; y] s /\
           bignum_from_memory(x,4) s = m /\
           bignum_from_memory(y,4) s = n)
      (\s. read PC s = returnaddress /\
           bignum_from_memory(z,4) s = (m * n) MOD p_25519)
      (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                  X10; X11; X12; X13; X14; X15; X16; X17] ,,
       MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
       MAYCHANGE SOME_FLAGS)
```

A detailed understanding of these formal specifications would take careful
study of the underlying logical definitions, but in somewhat general
impressionistic terms we can turn it into English as follows:

 - We assume the output buffer `z` doesn't overlap the code being executed
   but otherwise make no aliasing assumptions for inputs versus outputs.

 - ASSUMING that we start in a state where

    - the machine code specified at the start is loaded (4-byte aligned
      as per ARM restrictions) and the program counter register `PC`
      points to the start of it

    - the return address to the caller is in register `X30` as per ABI

    - the pointers `z`, `x` and `y` are set up in registers according
      to the standard ABI rules

    - the pointers `x` and `y` point at 4-digits bignums with respective
      values `m` and `n`

 - THEN we will reach another state where

    - The program counter `PC` has jumped to the return address

    - The buffer pointed to by `z` contains the mathematical answer
      (x * y) mod p_25519, where p_25519 is an abbreviation for
      2<sup>255</sup>-19.

 - BETWEEN initial and final states, the only components of the
   machine that could have been modified are:

    - Registers including the program counter (of course) and general
      purpose registers `X1`, ..., `X17` (freely modifiable by a subroutine
      according to the ABI)

    - The specified output buffer at address `z` of size 4 x 8-byte words.

    - The machine flags (also freely modifiable according to the ABI)

**Global Assumptions.**
In addition to the assumptions described in the formal specifications,
s2n-bignum implementations globally assume that the execution environment is
configured as following:

- Alignment checking is disabled (`AC` flag in x86, `SCTLR_ELx.A` in ARM).
  If these control bits are set, passing unaligned pointers as input/output
  buffers of a s2n-bignum function may cause a crash. If you are invoking the
  functions from C/C++ via the C header file (`s2n-bignum.h`) however, the
  alignment restriction on int-typed pointers in C standard such as `uint64_t*`
  will guarantee that the pointers are aligned regardless of the control bit.
  The alignment conditions for code and stack pointers in ARM will be
  explicitly described in the formal specifications.


- Little-endian is set in ARM (`E` mask of `CPSR` in ARM). We believe all code
  works equally well on a big-endian machine, but we do not validate that fact
  ourselves, and the instruction model underlying the formal proof does not
  directly address this question since it is assuming little-endian.

- It is assumed that s2n-bignum is run on 64-bit mode.

### Benchmarking and "constant time"

The benchmarking setup included in the repository can be invoked, as mentioned
above, by the following, starting in the s2n-bignum root directory and after
building the library:

    (cd ./benchmarks; make go)

After some explanatory information which summarizes the explanations below,
this shows a list of the execution time behavior of each function on the
current platform, one per line in alphabetical order; generic-size functions
like `bignum_add` are exercised on one or more specific sizes as shown in
parentheses after the function name.

```
bignum_add (4x4->4)             :     3.4 ns each (var  1.6%, corr  0.07) =  296073608 ops/sec
bignum_add (6x6->6)             :     4.3 ns each (var  1.3%, corr  0.02) =  233426704 ops/sec
bignum_add (32x32->32)          :    18.4 ns each (var  0.8%, corr -0.01) =   54430655 ops/sec
bignum_add_p25519               :     2.2 ns each (var  2.9%, corr -0.01) =  462501779 ops/sec
bignum_add_p256                 :     2.9 ns each (var  1.6%, corr -0.01) =  342429670 ops/sec
bignum_add_p256k1               :     2.6 ns each (var  1.9%, corr -0.04) =  387458274 ops/sec
bignum_add_p384                 :     4.4 ns each (var  1.1%, corr -0.03) =  226923614 ops/sec
bignum_add_p521                 :     4.3 ns each (var  1.4%, corr  0.02) =  232991612 ops/sec
bignum_amontifier (32)          :  2993.4 ns each (var  0.1%, corr -0.08) =     334073 ops/sec
bignum_amontmul (32)            :  2410.8 ns each (var  0.0%, corr -0.04) =     414797 ops/sec
bignum_amontredc (32/16 -> 16)  :   317.1 ns each (var  0.1%, corr -0.01) =    3153693 ops/sec
bignum_amontsqr (32 -> 32)      :  2410.2 ns each (var  0.0%, corr  0.05) =     414901 ops/sec
...
word_max                        :     0.8 ns each (var  4.2%, corr -0.03) = 1234333460 ops/sec
word_min                        :     0.8 ns each (var  3.4%, corr  0.05) = 1237623762 ops/sec
word_negmodinv                  :     2.7 ns each (var  2.0%, corr -0.11) =  366568915 ops/sec
word_recip                      :     7.4 ns each (var  0.9%, corr -0.06) =  134380815 ops/sec
```

The first number reported is the average runtime, in nanoseconds (1 ns =
10<sup>-9</sup> seconds, or one billionth of a second), over a large number of
calls, and the last one is the reciprocal of this to give the average number of
operations per second. Hence "smaller is better" for the first number while
"bigger is better" for the final one.

The "var" and "corr" numbers in parentheses attempt to give some empirical
results on the variation in runtime with respect to the data being manipulated.
Since this is intended to be invariant, one wishes these numbers to be small,
though there is inevitably some variation because of miscellaneous platform
factors. For each "bit density" between 0 and 64, pseudo-random inputs are
generated with that bit density; the bit density is essentially the average
number of 1 bits in each 64-bit word of these pseudo-random numbers (so bit
density 0 means all zeros, bit density 64 means all 1s). The function is
separately timed over each of these. The end results give the coefficient of
variation "var" (standard deviation divided by mean) and correlation
coefficient "corr" of runtime with bit density.

As explained above, the "constant time" design principle is that the sequence
of machine instructions executed, including the access pattern of memory reads
and writes, is independent of the actual numeric data being manipulated, once
any parametric sizes are fixed. Any failures in practice to actually take
exactly the same time on all data (beyond some expected experimental errors
and flaws in the timing framework) could only arise if either:

 - The above "constant time" design discipline is not followed at all points
   as intended. We consider this very unlikely, but in contrast to functional
   correctness it is not actually rigorously machine-checked at present. We
   anticipate in the future subjecting the code to automated dataflow analysis
   as an additional validation test.

 - Some individual machine instructions that are used take a time that depends
   on their data. We have specifically avoided certain machine instructions
   known to be problematic in this respect (e.g. division instructions), but
   we have no absolute guarantees from the hardware makers that there are no
   such variations in the instructions we use, except on ARM platforms where
   the "DIT" = "data-independent timing" bit is set.

## ML-KEM code

The code in the following two subdirectories breaks with some of the general
patterns for s2n-bignum that are described above:

    arm/mlkem
    arm/sha3

This code is almost exactly the same as the corresponding aarch64 assembler
kernels in the [mlkem-native](https://github.com/pq-code-package/mlkem-native)
project, and conforms to the same API; this in particular often includes the
precondition that some additional arguments point to certain tables of
constants. The ways in which this body of code breaks with the conventions
for s2n-bignum described above are as follows:

 * This code exists only for ARM, with no x86 counterpart present yet. However,
   x86 code and proofs are under active development and we expect before
   the end of 2025 to provide analogous functionality for x86.

 * The licensing of the code (which largely originates in mlkem-native or
   via other projects) is slightly different: Apache-2.0 or ISC or MIT versus
   the usual s2n-bignum licensing Apache-2.0 or ISC or MIT-0 (the difference
   is the attribution clause present in the unsuffixed MIT license).

 * Some ARM functions in the sha3 directory *do* rely on instruction set
   extension `sha3`, and so will not work on any ARM8 platform, something
   all other ARM code will.

 * One function, and *only* one at present, is not constant-time; this fact is
   explicitly telegraphed in its name `mlkem_rej_uniform_VARIABLE_TIME`.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License or the ISC License or the MIT-0 License.
