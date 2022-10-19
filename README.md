## s2n-bignum

This is a collection of bignum arithmetic routines designed for
cryptographic applications. All routines are written in pure machine
code, designed to be callable from C and other high-level languages,
with separate but API-compatible versions of each function for 64-bit
x86 (x86_64) and ARM (aarch64). Each function is written in a
constant-time style to avoid timing side-channels, and is accompanied
by a machine-checked formal proof that its mathematical result is
correct, based on a formal model of the underlying machine.

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
function consisting of a ```.S``` file that can be assembled by directly
invoking the GNU C compiler ```gcc``` or by explicitly combining the C
preprocessor and an assembler or other C or C++ compiler. If using your own
build command, consult the existing Makefiles for guidance since there are some
subtle variations even among assemblers (e.g. some C compilers won't handle
multiple instructions per line when taking in assembler files).

### Using the library

The build process above results in a library that can be used to provide all
the functionality together (e.g. ```x86/libs2bignum.a``` for an x86 machine),
as well as individual object files, one per function, that can be used for more
fine-grained linkage (e.g. ```x86/generic/bignum_add.o``` for the addition
function on x86). The functions all use standard Application Binary Interfaces
to connect to C and other high-level languages; the ABI determines, for
example, which registers or stack frames hold the arguments to a function when
called. The x86+Windows combination uses a non-standard ABI, which can
explicitly be forced using the additional option ```-DWINDOWS_ABI=1``` when
building. In either case the C-level prototypes for the functions are collected
in a header file that can be included in C programs to specify the interfaces.
A quick browse through this also gives an idea of what functions the
library provides.

[s2n-bignum/include/s2n-bignum.h](https://github.com/awslabs/s2n-bignum/blob/main/include/s2n-bignum.h)

You can include this in a C program as usual, after first including
the standard header defining the types ```uint64_t``` etc. that are
basic for s2n-bignum:

    #include <inttypes.h>
    #include "s2n-bignum.h"

Here is a small complete C program ```myprogram.c``` calling the
library, computing the modular inverse of 12345 modulo the wordsize
using the ```word_negmodinv``` function provided by the library,
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
```s2n-bignum``` subdirectory (otherwise change the ```.```
below into an appropriate path and/or change ```x86``` to ```arm```),
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
    The versions with ```_alt``` suffixes are designed to maximize
    performance on microarchitectures with higher multiplier
    throughput (typically more recent ones, like the Apple M1), while
    the non-alt variants are better suited to 'traditional' ARM
    microarchitectures with lower multiplier throughput (specifically,
    limited pipelining of the ```UMULH``` instruction to get the
    high part of a 64x64-bit product).

  * On x86, all generic bignum functions (in the ```x86/generic```
    subdirectory) will work correctly on any existing microarchitecture.
    Some of the more highly optimized functions for specific elliptic
    curves etc. require the BMI and ADX instruction set extensions
    (specifically the ```MULX```, ```ADCX``` and ```ADOX``` instructions).
    In such cases, the ```_alt``` suffix forms are provided
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

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.

