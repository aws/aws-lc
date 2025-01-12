# ML-KEM

The source code in this folder implements ML-KEM as defined in FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard ([link](https://csrc.nist.gov/pubs/fips/203/final).

## Source code origin and modifications.**

The source code in [mlkem](mlkem) is imported without change from [mlkem-native](https://github.com/pq-code-package/mlkem-native) using [importer.sh](importer.sh); see [META.yml](META.yml) for
the exact hash. mlkem-native's FIPS-202 code is not imported, but glue code [fips202_glue.h](fips202_glue.h) and [fips202x4_glue.h](fips202x4_glue.h) provided to use AWS-LC's own FIPS-202
implementation from [crypto/fipsmodule/sha](../sha).