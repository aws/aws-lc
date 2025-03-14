# ML-KEM

The source code in this folder implements ML-KEM as defined in FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard ([link](https://csrc.nist.gov/pubs/fips/203/final).

## Source code origin and modifications.**

The source code in [mlkem](mlkem) is imported without change from [mlkem-native](https://github.com/pq-code-package/mlkem-native) using [importer.sh](importer.sh); see [META.yml](META.yml) for
the exact hash. mlkem-native's FIPS-202 code is not imported, but glue code [fips202_glue.h](fips202_glue.h) and [fips202x4_glue.h](fips202x4_glue.h) provided to use AWS-LC's own FIPS-202
implementation from [crypto/fipsmodule/sha](../sha). [mlkem_native_bcm.c](mlkem_native_bcm.c) is imported using [importer.sh](importer.sh) from the mlkem-native file `examples/monolithic_build/mlkem_native_monobuild.c` which is a [`crypto/fipsmodule/bcm.c`](../bcm.c)-like file including all mlkem-native compilation units. This file is imported once per security level in [mlkem_c.c](mlkem_c.c) in such a way that level-independent code is shared.
