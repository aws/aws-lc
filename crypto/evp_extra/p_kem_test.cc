// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <algorithm>
#include <gtest/gtest.h>
#include <openssl/base.h>
#include <openssl/bio.h>
#include <openssl/evp.h>
#include <openssl/experimental/kem_deterministic_api.h>
#include <openssl/mem.h>
#include <openssl/pem.h>
#include <openssl/pkcs8.h>
#include <openssl/ssl.h>
#include "../fipsmodule/evp/internal.h"
#include "../fipsmodule/kem/internal.h"
#include "../test/file_test.h"
#include "../test/test_util.h"
#include "../test/wycheproof_util.h"


// https://datatracker.ietf.org/doc/rfc9935/
// All example keys are from Appendix C in the above standard
// Example ML-KEM-512 public key
const char *mlkem_512_pub_pem_str =
    "-----BEGIN PUBLIC KEY-----\n"
    "MIIDMjALBglghkgBZQMEBAEDggMhADmVgV5ZfRBDVc8pqlMzyTJRhp1bzb5IcST2\n"
    "Ari2pmwWxHYWSK12XPXYAGtRXpBafwrAdrDGLvoygVPnylcBaZ8TBfHmvG+QsOSb\n"
    "aTUSts6ZKouAFt38GmYsfj+WGcvYad13GvMIlszVkYrGy3dGbF53mZbWf/mqvJdQ\n"
    "Pyx7fi0ADYZFD7GAfKTKvaRlgloxx4mht6SRqzhydl0yDQtxkg+iE8lAk0Frg7gS\n"
    "Tmn2XmLLUADcw3qpoP/3OXDEdy81fSQYnKb1MFVowOI3ajdipoxgXlY8XSCVcuD8\n"
    "dTLKKUcpU1VntfxBPF6HktJGRTbMgI+YrddGZPFBVm+QFqkKVBgpqYoEZM5BqLtE\n"
    "wtT6PCwglGByjvFKGnxMm5jRIgO0zDUpFgqasteDj3/2tTrgWqMafWRrevpsRZMl\n"
    "JqPDdVYZvplMIRwqMcBbNEeDbLIVC+GCna5rBMVTXP9Ubjkrp5dBFyD5JPSQpaxU\n"
    "lfITVtVQt4KmTBaItrZVvMeEIZekNML2Vjtbfwmni8xIgjJ4NWHRb0y6tnVUAAUH\n"
    "gVcMZmBLgXrRJSKUc26LAYYaS1p0UZuLb+UUiaUHI5Llh2JscTd2V10zgGocjicy\n"
    "r5fCaA9RZmMxxOuLvAQxxPloMtrxs8RVKPuhU/bHixwZhwKUfM0zdyekb7U7oR3l\n"
    "y0GRNGhZUWy2rXJADzzyCbI2rvNaWArIfrPjD6/WaXPKin3SZ1r0H3oXthQzzRr4\n"
    "D3cIhp9mVIhJeYCxrBCgzctjagDthoGzXkKRJMqANQcluF+DperDpKPMFgCQPmUp\n"
    "NWC5szblrw1SnawaBIEZMCy3qbzBELlIUb8CEX8ZncSFqFK3Rz8JuDGmgx1bVMC3\n"
    "kNIlz2u5LZRiomzbM92lEjx6rw4moLg2Ve6ii/OoB0clAY/WuuS2Ac9huqtxp6PT\n"
    "UZejQ+dLSicsEl1UCJZCbYW3lY07OKa6mH7DciXHtEzbEt3kU5tKsII2NoPwS/eg\n"
    "nMXEHf6DChsWLgsyQzQ2LwhKFEZ3IzRLrdAA+NjFN8SPmY8FMHzr0e3guBw7xZoG\n"
    "WhttY7Js\n"
    "-----END PUBLIC KEY-----\n";

// https://datatracker.ietf.org/doc/rfc9935/
// Example ML-KEM-768 public key
const char *mlkem_768_pub_pem_str =
    "-----BEGIN PUBLIC KEY-----\n"
    "MIIEsjALBglghkgBZQMEBAIDggShACmKoQ1CPI3aBp0CvFnmzfA6CWuLPaTKubgM\n"
    "pKFJB2cszvHsT68jSgvFt+nUc/KzEzs7JqHRdctnp4BZGWmcAvdlMbmcX4kYBwS7\n"
    "TKRTXFuJcmecZgoHxeUUuHAJyGLrj1FXaV77P8QKne9rgcHMAqJJrk8JStDZvTSF\n"
    "wcHGgIBSCnyMYyAyzuc4FU5cUXbAfaVgJHdqQw/nbqz2ZaP3uDIQIhW8gvEJOcg1\n"
    "VwQzao+sHYHkuwSFql18dNa1m75cXpcqDYusQRtVtdVVfNaAoaj3G064a8SMmgUJ\n"
    "cxpUvZ1ykLJ5Y+Q3Lcmxmc/crAsBrNKKYjlREuTENkjWIsSMgjTQFEDozDdskn8j\n"
    "pa/JrAR0xmInTkJFJchVLs47P+JlFt6QG8fVFb3olVjmJslcgLkzQvgBAATznmxs\n"
    "lIccXjRMqzlmyDX5qWpZr9McQChrOLHBp4RwurlHUYk0RTzoZzapGfH1ptUQqG9U\n"
    "VPw5gMtcdlvSvV97NrFBDWY1yM60fE3aDXaijqyTnHHDAkgEhmxxYmZYRCFjwsIh\n"
    "F+UKzvzmN4qYVlIwKk7wws4Mxxa3eW4ray43d9+hrD2iWaMbWptTD4y2OKgaYqww\n"
    "GEmrr5WnMBvaMAaJCb/bfmfbzLs4pVUaJbGjoPaFdIrVdT2IgPABbGJ0hhZjhMVX\n"
    "H+I2WQA2TQODEeLYdds2ZoaTK17GAkMKNp6Hpu9cM4eGZXglvUwFes65I+sJNeaQ\n"
    "XmO0ztf4CFenc91ksVDSZhLqmsEgUtsgF78YQ8y0sygbaQ3HKK36hcACgbjjwJKH\n"
    "M1+Fa0/CiS9povV5Ia2gGRTECYhmLVd2lmKnhjUbm2ZJPat5WU2YbeIQDWW6D/Tq\n"
    "WLgVONJKRDWiWPrCVASqf0H2WLE4UGXhWNy2ARVzJyD0BFmqrBXkBpU6kKxSmX0c\n"
    "zQcAYO/GXbnmUzVEZ/rVbscTyG51QMQjrPJmn1L6b0rGiI2HHvPoR8ApqKr7uS4X\n"
    "skqgebH0GbphdbRCr7EZCdSla3CgM1soc5IYqnyTSOLDwvPrPRWkHmQXwN2Uv+sh\n"
    "QZsxGnuxOhgLvoMyGKmmsXRHzIXyJYWVh6cwdwSay8/UTQ8CVDjhXRU4Jw1Ybhv4\n"
    "MZKpRZz2PA6XL4UpdnmDHs8SFQmFHLg0D28Qew+hoO/Rs2qBibwIXE9ct4TlU/Qb\n"
    "kY+AOXzhlW94W+43fKmqi+aZitowwmt8PYxrVSVMyWIDsgxCruCsTh67QI5JqeP4\n"
    "edCrB4XrcCVCXRMFoimcAV4SDRY7DhlJTOVyU9AkbRgnRcuBl6t0OLPBu3lyvsWj\n"
    "BuujVnhVwBRpn+9lrlTHcKDYXBhADPZCrtxmB3e6SxOFAr1aeBL2IfhKSClrmN1D\n"
    "IrbxWCi4qPDgCoukSlPDqLFDVxsHQKvVZ9rxzenHnCBLbV4lnRdmoxu7y05qBc9F\n"
    "AhdrMBwcL0Ekd1AVe87IXoCbMKTWDXdHzdD1uZqoyCaYdRd5OqqAgKCxJKhVjfcr\n"
    "vje3X07btr6CFtbGM/srIoDiURPYaV5DSBw+6zl+sZJQUim2eiAeqJPD4ssy2ovD\n"
    "QvpN6gV4\n"
    "-----END PUBLIC KEY-----\n";

// https://datatracker.ietf.org/doc/rfc9935/
// Example ML-KEM-1024 public key
const char *mlkem_1024_pub_pem_str =
    "-----BEGIN PUBLIC KEY-----\n"
    "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\n"
    "uYOILhF1\n"
    "-----END PUBLIC KEY-----\n";

// https://datatracker.ietf.org/doc/rfc9935/
// C.1.1.1. ML-KEM-512 Private Key Examples: Seed Format
const char *mlkem_512_seed_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "MFQCAQAwCwYJYIZIAWUDBAQBBEKAQAABAgMEBQYHCAkKCwwNDg8QERITFBUWFxgZ\n"
    "GhscHR4fICEiIyQlJicoKSorLC0uLzAxMjM0NTY3ODk6Ozw9Pj8=\n"
    "-----END PRIVATE KEY-----\n";

// C.1.2.1. ML-KEM-768 Private Key Examples: Seed Format
const char *mlkem_768_seed_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "MFQCAQAwCwYJYIZIAWUDBAQCBEKAQAABAgMEBQYHCAkKCwwNDg8QERITFBUWFxgZ\n"
    "GhscHR4fICEiIyQlJicoKSorLC0uLzAxMjM0NTY3ODk6Ozw9Pj8=\n"
    "-----END PRIVATE KEY-----\n";

// C.1.3.1. ML-KEM-1024 Private Key Examples: Seed Format
const char *mlkem_1024_seed_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "MFQCAQAwCwYJYIZIAWUDBAQDBEKAQAABAgMEBQYHCAkKCwwNDg8QERITFBUWFxgZ\n"
    "GhscHR4fICEiIyQlJicoKSorLC0uLzAxMjM0NTY3ODk6Ozw9Pj8=\n"
    "-----END PRIVATE KEY-----\n";

// malformed key (63 byte seed)
const char *mlkem_512_bad_seed_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "MFMCAQAwCwYJYIZIAWUDBAQBBEGAPwABAgMEBQYHCAkKCwwNDg8QERITFBUWFxgZ\n"
    "GhscHR4fICEiIyQlJicoKSorLC0uLzAxMjM0NTY3ODk6Ozw9Pg==\n"
    "-----END PRIVATE KEY-----\n";

const char *mlkem_512_priv_expanded_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "JCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+Pw==\n"
    "-----END PRIVATE KEY-----\n";

const char *mlkem_768_priv_expanded_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "JCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+Pw==\n"
    "-----END PRIVATE KEY-----\n";

const char *mlkem_1024_priv_expanded_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "JCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+Pw==\n"
    "-----END PRIVATE KEY-----\n";

// C.1.1.3. ML-KEM-512 Private Key Examples: Both Format
const char *mlkem_512_priv_both_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "Pj8=\n"
    "-----END PRIVATE KEY-----\n";

// C.1.2.3. ML-KEM-768 Private Key Examples: Both Format
const char *mlkem_768_priv_both_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "MIIJvgIBADALBglghkgBZQMEBAIEggmqMIIJpgRAAAECAwQFBgcICQoLDA0ODxAR\n"
    "EhMUFRYXGBkaGxwdHh8gISIjJCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+PwSC\n"
    "CWAn0qd/M3VvYSCO8ROr6CWVhz1KvHMOW11nlSm/akzrY4NCcjGoYS9BVQUVrLpS\n"
    "5I6ti5QoM7vmhl0T0Up50sXD4H8KBW2N56rfyroFjEk8gLN8q4xWJ1O7O6a27IKX\n"
    "+IXqp1QNUwAVqEQG5VsTZrV34jbOWKJtih61pE1UIyPCFn2b9KR/mFaZygW65DuN\n"
    "7GF/AjgKOJCv1LjH7H7eJlU6Al885bxdemITAwQjXLGtSDa1ZrW4Y72b20WihEpw\n"
    "R7bI04PkSFJeBAtNyKK0jGw3yW1i1D8/2I4ogcQKIFyeJI9lK1kngad5+GiA8qFH\n"
    "tnhj85HMGlqQjACV4HISKR4u+KNuuanAxgcyJbNHA6SvBJOCxHVz2mj96SRa1ETj\n"
    "Gx+9tSHx9h83vAzvKSBn5nDSih/9kE9vEZCplpGKEwN6bKvzw3O/gpbNN6szundG\n"
    "gJzD+K3hs2Ob1Xv8xpZQqq8d4Zj8TARjKZ5SxGF4DMQo/F0EpcUYUMumwqUnQ0Bn\n"
    "V5PdoJvkTCnmOVxl+F0qCnxt9BHmkRsfLLbDUc0uh19Rtji+d2CX6T4vKy+D2gvu\n"
    "9KqFup52OrZFAqDKUiLp6rWztwiO1SBg6Mgmm5Q6casK4cWxtofS4BnPgDa8+b9u\n"
    "e6w6qjbkFmD6pFQPJkjNk6GJ7Fwt6nC6yqpP/JBvkIEOobZ78k8seM9rqIGq6mHA\n"
    "ZSv/lbG65EJtF3O5zCyoLCHjjGNuOxxSMkSYawvoqD9d1c8tVHYvs8Xr9ZuOiFMC\n"
    "sc5HAz7fdg9OApvkC21WaxnddYrNXHQSh4ExJE+QFyxT8mZjwh2QUwHUi6+RyRfM\n"
    "d3np2IAswQ2Jo3BQmaKtOjqIlnQ8EURpgJO+JX2stm3HhSKLkSyNll0Uqig0LDrE\n"
    "qT/vpTKyCUXdwQIBOcFNY4uQjE3d6aBkW5Wy5EFNQLt58EQTgw8VqHPCi7cFnCdB\n"
    "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\n"
    "Pj8=\n"
    "-----END PRIVATE KEY-----\n";

// C.1.3.3. ML-KEM-1024 Private Key Examples: Both Format
const char *mlkem_1024_priv_both_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "Pj8=\n"
    "-----END PRIVATE KEY-----\n";

// C.4.1. ML-KEM Inconsistent Seed and Expanded Private Keys
// WARNING: these private keys are purposely bad and MUST be rejected.
//
// The first C.4.1 example: an ML-KEM-512 |both| private key whose seed and
// expandedKey disagree.
const char *mlkem_512_priv_both_inconsistent_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "P0A=\n"
    "-----END PRIVATE KEY-----\n";

// The fourth C.4.1 example: an ML-KEM-512 |both| private key whose expandedKey
// differs from the seed only in |z|, the implicit rejection secret. The private
// and public vectors still match, so a pairwise consistency check passes and
// only the bytewise check of section 8 catches it.
const char *mlkem_512_priv_both_inconsistent_z_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "Pj4=\n"
    "-----END PRIVATE KEY-----\n";

// The second C.4.1 example: an ML-KEM-512 |expandedKey| private key with a
// mutated s_0 and an intact public key hash. The FIPS 203 section 7.3 hash
// check passes; only the pairwise consistency test rejects it.
const char *mlkem_512_priv_expanded_mutated_s0_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "JCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+Pw==\n"
    "-----END PRIVATE KEY-----\n";

// The third C.4.1 example: an ML-KEM-512 |expandedKey| private key with a
// mutated H(ek). The section 7.3 hash check rejects it.
const char *mlkem_512_priv_expanded_mutated_hek_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "JCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+Pw==\n"
    "-----END PRIVATE KEY-----\n";

// The following private/public keys were generated externally and encoded using the Java library BouncyCastle which is a JCA provider. 
// Private keys generated were encoded in expandedKey format. 
// Implementation: https://github.com/bcgit/bc-java/tree/b41f23936724284a20f10dff13c76896a846031b/prov/src/main/java/org/bouncycastle/jcajce/provider/asymmetric/mlkem
// Encoder: https://github.com/bcgit/bc-java/blob/0e100a58af34d0cf91ea5cfd1f0a6d36681c3653/core/src/main/java/org/bouncycastle/pqc/crypto/util/PrivateKeyInfoFactory.java#L247-L256

const char *bouncy_castle_ml_kem_512_seed_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "MFQCAQAwCwYJYIZIAWUDBAQBBEKAQNE4hxN6KQyTF+Qj9UlXv4frRjHiNEt99Dv+\n"
    "fyqv3I4AQmR+rSd2QVr8iGPjcTCQ24hWPJ3BxaOnQs7avyfq7ps=\n"
    "-----END PRIVATE KEY-----\n";

const char *bouncy_castle_mlkem_512_priv_expanded_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "J3ZBWvyIY+NxMJDbiFY8ncHFo6dCztq/J+rumw==\n"
    "-----END PRIVATE KEY-----\n";

const char *bouncy_castle_mlkem_512_pub_pem_str =
    "-----BEGIN PUBLIC KEY-----\n"
    "MIIDMjALBglghkgBZQMEBAEDggMhABC0xcv2T7+iOdhyR9GpG6qbCr2RVwykEti2\n"
    "LPZiNd2DH5nsmrkVqzkCrDjQmvr1am+VzM7Dm4QRjTAnh5pSmfw7PVAoc8WLEf1Q\n"
    "HHyqERoUfYlLGIRQOP5HB/vXDOnpuJgkPlfzJ3bmDA3ZBl0bkt1SBPSklcrHKtzs\n"
    "yGnaO4EbewBKPZy1PGABi3fJbWnGn6hbfHORLiIcjh/QBUWSLjq7ndvYUXiqznBD\n"
    "xNgUkwCxGlf0MocicCJsx7qGfNunpfREzbyxRydrZc0sSoWoyPyQkUgJHznEisdL\n"
    "MTA3z7oBearWDCCWFZPWSXQ0S/MTD4posXI0LKfyViOspJgraO9ci2w3yX+pgGG8\n"
    "pHBseFqxvsSqfR78JXRgSHrCHgG6iZR4ff4wBO0mCV3zvf9QibwMowh7aSoAP22H\n"
    "AJuSMG84yFcoXBMrDYf7qm7DUZ31LhkkjlZIBpiMu4zLf/W1fH08jsy0nPJYN1ka\n"
    "Jt50vTgZxRuJWGGUvHsSjr1ntxUpGQfUBP1jQX1mm6FHm2Sqmk4GD6D2g4h4AAUw\n"
    "RSJDUfL1zL3CUASLiRVnnvlXqYDJMpw0ZAjGR6XoWJIYFYT6cw/Rk5HAaBzWtAjn\n"
    "LVSYHceiQ3LIthGAEHushzLEFl51NijzrqopuFKGpoi1s0SbfTdKLo2EUbxnWP3x\n"
    "ROfAdBx6K1hKSLKhnD16wwmQky0HToioSMplQEOlv4pne7MRq2CYwULlK8pDzVEk\n"
    "R6XabtT7KflgZib7ZeaGIDYgI1sxkn8FtWg6vTNjz19gUWvTckf7YHVYAJfjpw4y\n"
    "GgTxjIjxJzYqIDeFjbEytZRbiHBiG1/1qJt5a+b0udsqPHLUeZbckMpRza6rq25n\n"
    "kDW5hPTQs0jsb8iqgt1xjuMjloGCfahjv0S3qtWnKtOWSp8cx1FaMCDrXQG1zrrQ\n"
    "Ix+MpzN8uuK1Eo8bJH85IL6syek8tx5roXjWR/eRjPUzkAvblBj5zgRsEpRUbJFM\n"
    "c5/2A+kDyOQwIJ5wW7nWdRJkitQaNHgEoKcRLh6yf3G9sIYpQ8JjMo0SBUiMLtp0\n"
    "Yaa6NjZv\n"
    "-----END PUBLIC KEY-----\n";

const char *bouncy_castle_ml_kem_768_seed_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "MFQCAQAwCwYJYIZIAWUDBAQCBEKAQEaoG9U4IT/3ICeEUsmqUomFES14K0pvYTdA\n"
    "LQoFvUzjPo/ghsug5JTZ3g1UrXSl2rXr3BFCDJgpEStfanCeVv0=\n"
    "-----END PRIVATE KEY-----\n";

const char *bouncy_castle_mlkem_768_priv_expanded_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "y6DklNneDVStdKXatevcEUIMmCkRK19qcJ5W/Q==\n"
    "-----END PRIVATE KEY-----\n";

const char *bouncy_castle_mlkem_768_pub_pem_str =
    "-----BEGIN PUBLIC KEY-----\n"
    "MIIEsjALBglghkgBZQMEBAIDggShAKGhKH9RDLSXPlqpkU2js4wCo+CFlr72UnnA\n"
    "N4e4lQmIy7knU1nWvURys55GYm9iZlD2clCij2H4E1XliJtZWnd0EIZ4X26yQpuJ\n"
    "BM13i9VazemaRnCpYnb3DnpzbrdqQ0wkxOX7OybZfZmyrteyNDt6WwhHp2pYw83c\n"
    "bmpyrKALdnUmcS/pcWaFFUdyp4WEGIm4doMzkKHRSQuSoYacny7QBXAjgLiCDQdE\n"
    "J5Q8JXoBIouiepAobcYAffoEMUT1r+QnvdJXEx1Eu4P4bN03IbExT9HjtK58IFib\n"
    "bU1IrZ9WjF4WOwJLWpI0M/yjfVAopLtzhkXxK5jQTeb0eEjQpuFXcuYJXe6HKZaC\n"
    "FDtsM2DhXlIDDHPXiACRbzAxx1jknqqRpIBSIAhahTDGYyp0kQTit30Xb+hSwQZF\n"
    "PmYEB9ZAbTxDUmJCUefBwlh2yKbWQLIzEGKTm9vWsGa3hY8LfWljeha6fwdpH3rL\n"
    "EOJHimeFv78AISsoMVsVHLMjvrtVMYSchkJsWhZ0vybov2pVi4YlcAmgUzykzAdo\n"
    "jm9iYhQIUrcayYbgsl7nxSHMx/cctBJHipo5i1eyAZ5pOQosi70FV2HUV07HLAk2\n"
    "Ua5DK+gsvwuyjTGBL/x1WhPhMRcmWKuENQPAnDSppSFpbQ1qI89RXsLFneBGc/4o\n"
    "kSemG+NDlwJBW+DxC6J5KyhHZRBaxh9StqtsTyomBQMpMoNFBAzkbmOzQiGERgVZ\n"
    "CfiTrtyoX93YOHBSVfjmkl4JBZlsyi7GHtZ8s7OxhqyVSlCCpeLnoZWXnz5Riwgm\n"
    "sxwTIZ4kGmQmSdIxg0BTPxRaV3kRzbmyv4qrMf06Il2gzGJJlXT0uzVxZH9BzurI\n"
    "TmEhGv/wI40kwtAzXpLBs4zmAIdELulgsWnzJpBBkEXsr9yQWyX8CiV4gTbiJ+M8\n"
    "P7L1FDLDHEXnnPZWEyOyr7WZKKKCAEUSlaiTmeG1SwB2kOqnLv1JFOzEyEkBwrzG\n"
    "bVXxuwhxRI5XpVEUQWCmjPRbSQFYjO2yWUCBP/1ca9lnzpqZg9nYz2omUJkTQpbE\n"
    "lP3pI3h6Ujr4FjBTYP8jG2SbdiRQHJ7Gk7ZKS/tqFizwNWQAx2SLXnr0V8ZstWmz\n"
    "oaQjmTdhS9+1na1MZFdkPsdMsObrZ76qLoNhKIhlTzhRSgC6MZ81qZq0Tdp2T4m6\n"
    "ah5qa11UDjeVcz5AoYI2gz/hhHOLYilqRnAbtuTBs8xsHA7cY+hqlguhNUSrqX3B\n"
    "pZxZTcLRjrPSkHcWupF7NrVWOH87AUL3o/SGvbz1RrKFHoaye+27kY4EwY7DYO7b\n"
    "EEACY9MxFOGMagtaKSZlfRBZMJugT9gxLAazlV3FE7ySFlt0Y6bKKWokiiw3VXFB\n"
    "FRqAvnI3azk5oUn1eV18zcxRDcqsZfHgNlq2CPbaJUSFFo2gyEHHAPnMjo5AsR/2\n"
    "OvtnIUJSZx0CRwB5gkxsfvVIop5JFOMENWA2U/PDk1yoUqOIYswgQ0KwmKPpm5FC\n"
    "Vl7cuaOmRC6ys0XznT6mXXCLma0qERroTP8ys6x3Xe+uHWVXo/bxq1eepqFKqWKh\n"
    "M/8A5tdU\n"
    "-----END PUBLIC KEY-----\n";
struct KEMTestVector {
  int nid;
  const char *public_pem_str;
  const char *private_pem_expanded_str;
  const char *private_pem_seed_str;
  const char *expected_deterministic_pub_pem;
  const char *expected_deterministic_priv_pem;
  size_t public_key_len;
  size_t secret_key_len;
};

static const KEMTestVector kemParameters[] = {
    {NID_MLKEM512, mlkem_512_pub_pem_str, mlkem_512_priv_expanded_pem_str,
     mlkem_512_seed_pem_str, mlkem_512_pub_pem_str, mlkem_512_seed_pem_str, 800, 1632},
    {NID_MLKEM768, mlkem_768_pub_pem_str, mlkem_768_priv_expanded_pem_str,
     mlkem_768_seed_pem_str, mlkem_768_pub_pem_str, mlkem_768_seed_pem_str, 1184, 2400},
    {NID_MLKEM1024, mlkem_1024_pub_pem_str, mlkem_1024_priv_expanded_pem_str,
     mlkem_1024_seed_pem_str, mlkem_1024_pub_pem_str, mlkem_1024_seed_pem_str, 1568, 3168},
    {NID_MLKEM512, bouncy_castle_mlkem_512_pub_pem_str,
     bouncy_castle_mlkem_512_priv_expanded_pem_str, bouncy_castle_ml_kem_512_seed_pem_str,
     mlkem_512_pub_pem_str, mlkem_512_seed_pem_str, 800, 1632},
    {NID_MLKEM768, bouncy_castle_mlkem_768_pub_pem_str,
     bouncy_castle_mlkem_768_priv_expanded_str, bouncy_castle_ml_kem_768_seed_pem_str,
     mlkem_768_pub_pem_str, mlkem_768_seed_pem_str, 1184, 2400},
};


static bssl::UniquePtr<EVP_PKEY> generate_kem_key_pair(int nid) {
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_KEM, nullptr));
  if (!ctx || !EVP_PKEY_CTX_kem_set_params(ctx.get(), nid) ||
      !EVP_PKEY_keygen_init(ctx.get())) {
    return nullptr;
  }
  EVP_PKEY *raw = nullptr;
  if (!EVP_PKEY_keygen(ctx.get(), &raw)) {
    return nullptr;
  }
  return bssl::UniquePtr<EVP_PKEY>(raw);
}

class KEMTest : public testing::TestWithParam<KEMTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, KEMTest, testing::ValuesIn(kemParameters));

TEST_P(KEMTest, MarshalParse) {
  // ---- 1. Setup phase: generate a key ----
  int nid = GetParam().nid;
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(nid));
  ASSERT_TRUE(pkey);

  // ---- 2. Test encode (marshal) and decode (parse) of public key ----
  // The public key must encode properly.
  bssl::ScopedCBB cbb;
  uint8_t *der;
  size_t der_len;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_public_key(cbb.get(), pkey.get()));
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  // The public key must parse properly.
  CBS cbs;
  CBS_init(&cbs, der, der_len);
  bssl::UniquePtr<EVP_PKEY> pub_pkey_from_der(EVP_parse_public_key(&cbs));
  ASSERT_TRUE(pub_pkey_from_der.get());
  EXPECT_EQ(1, EVP_PKEY_cmp(pkey.get(), pub_pkey_from_der.get()));

  // ---- 3. Test encode (marshal) and decode (parse) of private key ----
  // The private key must encode properly.
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(cbb.get(), pkey.get()));
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  free_der.reset(der);

  // The private key must parse properly.
  CBS_init(&cbs, der, der_len);
  bssl::UniquePtr<EVP_PKEY> priv_pkey_from_der(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(priv_pkey_from_der);
  EXPECT_EQ(Bytes(priv_pkey_from_der->pkey.kem_key->secret_key,
                  GetParam().secret_key_len),
            Bytes(pkey->pkey.kem_key->secret_key, GetParam().secret_key_len));
}

// Test that the private key is encoded in seed format
TEST_P(KEMTest, PrivateKeySeedFormat) {
  const KEMTestVector &test = GetParam();

  // Generate a key pair
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(test.nid));
  ASSERT_TRUE(pkey);

  // Verify the seed is present
  ASSERT_TRUE(pkey->pkey.kem_key->seed);

  // Encode the private key
  bssl::ScopedCBB cbb;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(cbb.get(), pkey.get()));

  uint8_t *der = nullptr;
  size_t der_len = 0;
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  // Parse the PKCS#8 structure to verify the privateKey field contains
  // the seed format ([0] IMPLICIT OCTET STRING)
  CBS pkcs8, algorithm, private_key;
  uint64_t version = 0;
  CBS_init(&pkcs8, der, der_len);

  ASSERT_TRUE(CBS_get_asn1(&pkcs8, &pkcs8, CBS_ASN1_SEQUENCE));
  ASSERT_TRUE(CBS_get_asn1_uint64(&pkcs8, &version));
  ASSERT_EQ(version, 0u);
  ASSERT_TRUE(CBS_get_asn1(&pkcs8, &algorithm, CBS_ASN1_SEQUENCE));
  ASSERT_TRUE(CBS_get_asn1(&pkcs8, &private_key, CBS_ASN1_OCTETSTRING));

  // The privateKey field should contain the seed as [0] context-specific tag
  CBS seed;
  ASSERT_TRUE(CBS_get_asn1(&private_key, &seed, CBS_ASN1_CONTEXT_SPECIFIC | 0));
  ASSERT_EQ(CBS_len(&seed), 64u);

  // Verify it matches the seed stored in the key
  EXPECT_EQ(Bytes(CBS_data(&seed), CBS_len(&seed)),
            Bytes(pkey->pkey.kem_key->seed, 64));
}

TEST_P(KEMTest, ParsePublicKey) {
  // Test parsing of the draft standard example public keys

  const KEMTestVector &test = GetParam();
  int nid = test.nid;
  size_t public_key_len = test.public_key_len;
  size_t secret_key_len = test.secret_key_len;
  const char *public_pem_str = test.public_pem_str;

  // ---- 1. Convert example PEM to DER ----
  uint8_t *der = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(public_pem_str, &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  // ---- 2. Parse the public key ----
  CBS cbs;
  CBS_init(&cbs, der, der_len);
  bssl::UniquePtr<EVP_PKEY> pkey_from_der(EVP_parse_public_key(&cbs));
  ASSERT_TRUE(pkey_from_der);
  ASSERT_EQ(EVP_PKEY_id(pkey_from_der.get()), EVP_PKEY_KEM);

  // ---- 3. Verify key parameters ----
  ASSERT_EQ(EVP_PKEY_kem_get_type(pkey_from_der.get()), nid);
  KEM_KEY *kem_key = pkey_from_der->pkey.kem_key;
  ASSERT_TRUE(kem_key);
  ASSERT_EQ(kem_key->kem->public_key_len, public_key_len);
  ASSERT_EQ(kem_key->kem->secret_key_len, secret_key_len);
}

TEST_P(KEMTest, ParseExamplePrivateKey) {
  // Test parsing of the draft standard example private keys (expanded format)

  const KEMTestVector &test = GetParam();
  int nid = test.nid;
  size_t public_key_len = test.public_key_len;
  size_t secret_key_len = test.secret_key_len;
  const char *private_pem_expanded_str = test.private_pem_expanded_str;

  // ---- 1. Convert example PEM to DER ----
  uint8_t *der = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(private_pem_expanded_str, &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  // ---- 2. Parse the private key ----
  CBS cbs;
  CBS_init(&cbs, der, der_len);
  bssl::UniquePtr<EVP_PKEY> pkey_from_der(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(pkey_from_der);
  ASSERT_EQ(EVP_PKEY_id(pkey_from_der.get()), EVP_PKEY_KEM);

  // ---- 3. Verify key parameters ----
  ASSERT_EQ(EVP_PKEY_kem_get_type(pkey_from_der.get()), nid);
  KEM_KEY *kem_key = pkey_from_der->pkey.kem_key;
  ASSERT_TRUE(kem_key);
  ASSERT_EQ(kem_key->kem->public_key_len, public_key_len);
  ASSERT_EQ(kem_key->kem->secret_key_len, secret_key_len);

  // ---- 4. Verify private key is present ----
  ASSERT_TRUE(kem_key->secret_key);
}

// A private key parsed from the RFC 9935 section 6 Case-2 "expandedKey" form
// carries both |secret_key| and the |public_key| recovered from it, so it
// compares equal to the separately published public key. |kem_pub_cmp| must
// still return -2 rather than dereferencing a NULL |public_key|, which remains
// reachable for a parameters-only key.
TEST_P(KEMTest, PubCmpExpandedPrivateKey) {
  const KEMTestVector &test = GetParam();

  uint8_t *pub_der = nullptr;
  long pub_der_len = 0;
  ASSERT_TRUE(PEM_to_DER(test.public_pem_str, &pub_der, &pub_der_len));
  bssl::UniquePtr<uint8_t> free_pub_der(pub_der);
  CBS pub_cbs;
  CBS_init(&pub_cbs, pub_der, pub_der_len);
  bssl::UniquePtr<EVP_PKEY> pub_pkey(EVP_parse_public_key(&pub_cbs));
  ASSERT_TRUE(pub_pkey);

  // Parse the expanded-form private key. An expanded ML-KEM key embeds its own
  // encapsulation key, so case 2 in |kem_priv_decode| recovers it and populates
  // |public_key| alongside |secret_key|.
  uint8_t *priv_der = nullptr;
  long priv_der_len = 0;
  ASSERT_TRUE(
      PEM_to_DER(test.private_pem_expanded_str, &priv_der, &priv_der_len));
  bssl::UniquePtr<uint8_t> free_priv_der(priv_der);
  CBS priv_cbs;
  CBS_init(&priv_cbs, priv_der, priv_der_len);
  bssl::UniquePtr<EVP_PKEY> priv_pkey(EVP_parse_private_key(&priv_cbs));
  ASSERT_TRUE(priv_pkey);
  ASSERT_TRUE(priv_pkey->pkey.kem_key->public_key);

  // The recovered public key must be the one that was published separately.
  EXPECT_EQ(EVP_PKEY_cmp(pub_pkey.get(), priv_pkey.get()), 1);
  EXPECT_EQ(EVP_PKEY_cmp(priv_pkey.get(), pub_pkey.get()), 1);

  // |kem_pub_cmp| must still return -2 rather than dereferencing a NULL
  // |public_key|. No import leaves a key in that state any more, so clear the
  // public key to reach the branch. It matters because
  // |X509_check_private_key| compares keys during |PKCS12_parse|.
  OPENSSL_free(priv_pkey->pkey.kem_key->public_key);
  priv_pkey->pkey.kem_key->public_key = nullptr;
  EXPECT_EQ(EVP_PKEY_cmp(pub_pkey.get(), priv_pkey.get()), -2);
  EXPECT_EQ(EVP_PKEY_cmp(priv_pkey.get(), pub_pkey.get()), -2);
}

TEST_P(KEMTest, GetType) {
  int nid = GetParam().nid;

  // ---- 1. Generate a key pair and verify the NID ----
  bssl::UniquePtr<EVP_PKEY> pkey = generate_kem_key_pair(nid);
  ASSERT_TRUE(pkey);
  ASSERT_EQ(EVP_PKEY_kem_get_type(pkey.get()), nid);
}

TEST(KEMTest, GetTypeWrongKeyType) {
  // EVP_PKEY_kem_get_type must return 0 and set EVP_R_EXPECTING_A_KEM_KEY
  // when called on an EVP_PKEY whose type is not EVP_PKEY_KEM. Check both a
  // classical (EC) key and a post-quantum (PQDSA) key, to ensure that
  // adjacent post-quantum types do not slip past the type check.

  // ---- EC key ----
  bssl::UniquePtr<EVP_PKEY_CTX> ec_ctx(
      EVP_PKEY_CTX_new_id(EVP_PKEY_EC, nullptr));
  ASSERT_TRUE(ec_ctx);
  ASSERT_TRUE(EVP_PKEY_keygen_init(ec_ctx.get()));
  ASSERT_TRUE(EVP_PKEY_CTX_set_ec_paramgen_curve_nid(
      ec_ctx.get(), NID_X9_62_prime256v1));
  EVP_PKEY *raw_ec = nullptr;
  ASSERT_TRUE(EVP_PKEY_keygen(ec_ctx.get(), &raw_ec));
  bssl::UniquePtr<EVP_PKEY> ec_pkey(raw_ec);

  ERR_clear_error();
  ASSERT_EQ(EVP_PKEY_kem_get_type(ec_pkey.get()), 0);
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), EVP_R_EXPECTING_A_KEM_KEY);

  // ---- PQDSA key ----
  bssl::UniquePtr<EVP_PKEY_CTX> pqdsa_ctx(
      EVP_PKEY_CTX_new_id(EVP_PKEY_PQDSA, nullptr));
  ASSERT_TRUE(pqdsa_ctx);
  ASSERT_TRUE(EVP_PKEY_CTX_pqdsa_set_params(pqdsa_ctx.get(), NID_MLDSA44));
  ASSERT_TRUE(EVP_PKEY_keygen_init(pqdsa_ctx.get()));
  EVP_PKEY *raw_pqdsa = nullptr;
  ASSERT_TRUE(EVP_PKEY_keygen(pqdsa_ctx.get(), &raw_pqdsa));
  bssl::UniquePtr<EVP_PKEY> pqdsa_pkey(raw_pqdsa);

  ERR_clear_error();
  ASSERT_EQ(EVP_PKEY_kem_get_type(pqdsa_pkey.get()), 0);
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), EVP_R_EXPECTING_A_KEM_KEY);
}

TEST(KEMTest, GetTypeUninitializedKey) {
  // EVP_PKEY_kem_get_type must return 0 and set EVP_R_NO_PARAMETERS_SET when
  // called on an EVP_PKEY whose type is EVP_PKEY_KEM but which has no
  // underlying KEM_KEY attached.
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  ASSERT_TRUE(pkey);
  ASSERT_TRUE(EVP_PKEY_set_type(pkey.get(), EVP_PKEY_KEM));
  ASSERT_EQ(EVP_PKEY_id(pkey.get()), EVP_PKEY_KEM);

  ERR_clear_error();
  ASSERT_EQ(EVP_PKEY_kem_get_type(pkey.get()), 0);
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), EVP_R_NO_PARAMETERS_SET);
}

// Invalid length test vectors - truncated DER structures
static const uint8_t mlkem512_public_key_invalid_length[] = {
    0x30, 0x16, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
    0x04, 0x04, 0x01, 0x03, 0x07, 0x00, 0x39, 0x95, 0x5e, 0x59, 0x7d, 0x10};

static const uint8_t mlkem512_private_key_invalid_length[] = {
    0x30, 0x1c, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60,
    0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x01, 0x04, 0x0a,
    0x04, 0x08, 0x70, 0x55, 0x4f, 0xd4, 0x36, 0x34, 0x4f, 0x27};

TEST(KEMTest, ParsePublicKeyInvalidLength) {
  CBS cbs;
  CBS_init(&cbs, mlkem512_public_key_invalid_length,
           sizeof(mlkem512_public_key_invalid_length));
  bssl::UniquePtr<EVP_PKEY> pub_pkey_from_der(EVP_parse_public_key(&cbs));
  ASSERT_FALSE(pub_pkey_from_der.get());
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), EVP_R_INVALID_BUFFER_SIZE);
}

TEST(KEMTest, ParsePrivateKeyInvalidLength) {
  CBS cbs;
  CBS_init(&cbs, mlkem512_private_key_invalid_length,
           sizeof(mlkem512_private_key_invalid_length));
  bssl::UniquePtr<EVP_PKEY> private_pkey_from_der(EVP_parse_private_key(&cbs));
  ASSERT_FALSE(private_pkey_from_der.get());
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), EVP_R_INVALID_BUFFER_SIZE);
}


// Verifies that deterministic ML-KEM key generation with the fixed seed from the IETF standard produces keys that exactly
// match the expected PEM strings from the standard. 
// The expected PEM strings from the given seed are fields at the top (mlkem_XXX_pub/priv_pem_str)
// See Appendix C.1 in https://datatracker.ietf.org/doc/rfc9935/ for the seed value
TEST_P(KEMTest, DeterministicKeyMarshaling) {
  const KEMTestVector& test = GetParam();
  
  // ---- 1. Setup phase: create context and set parameters ----
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_KEM, nullptr));
  ASSERT_TRUE(ctx);
  ASSERT_TRUE(EVP_PKEY_keygen_init(ctx.get()));
  ASSERT_TRUE(EVP_PKEY_CTX_kem_set_params(ctx.get(), test.nid));

  // ---- 2. Create deterministic seed: 00 01 02 ... 3f (64 consecutive bytes) ----
  // Seed is specified in Appendix C.1 in https://datatracker.ietf.org/doc/rfc9935/
  std::vector<uint8_t> keygen_seed(64);
  for (size_t i = 0; i < 64; i++) {
    keygen_seed[i] = static_cast<uint8_t>(i);  // seed is a sequence - 00, 01, 02, ... 3f (from above standard)
  }
  size_t seed_len = keygen_seed.size();

  // ---- 3. Generate deterministic keypair ----
  EVP_PKEY *raw = nullptr;
  ASSERT_TRUE(EVP_PKEY_keygen_deterministic(ctx.get(), &raw,
                                           keygen_seed.data(), &seed_len));
  ASSERT_TRUE(raw);
  bssl::UniquePtr<EVP_PKEY> pkey(raw);

  // ---- 4. Marshal generated public key to DER ----
  bssl::ScopedCBB public_cbb;
  ASSERT_TRUE(CBB_init(public_cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_public_key(public_cbb.get(), pkey.get()));

  uint8_t *generated_pub_der;
  size_t generated_pub_der_len;
  ASSERT_TRUE(CBB_finish(public_cbb.get(), &generated_pub_der, &generated_pub_der_len));
  bssl::UniquePtr<uint8_t> generated_pub_der_ptr(generated_pub_der);

  // ---- 5. Convert expected public PEM to DER ----
  uint8_t *expected_pub_der = nullptr;
  long expected_pub_der_len = 0;
  ASSERT_TRUE(PEM_to_DER(test.expected_deterministic_pub_pem, &expected_pub_der, &expected_pub_der_len));
  bssl::UniquePtr<uint8_t> expected_pub_der_ptr(expected_pub_der);

  // ---- 6. Compare public key DERs ----
  EXPECT_EQ(generated_pub_der_len, static_cast<size_t>(expected_pub_der_len))
      << "Public key DER length mismatch";
  EXPECT_EQ(Bytes(generated_pub_der, generated_pub_der_len),
            Bytes(expected_pub_der, expected_pub_der_len))
      << "Public key DER content mismatch";

  // ---- 7. Marshal generated private key to DER ----
  bssl::ScopedCBB private_cbb;
  ASSERT_TRUE(CBB_init(private_cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(private_cbb.get(), pkey.get()));

  uint8_t *generated_priv_der;
  size_t generated_priv_der_len;
  ASSERT_TRUE(CBB_finish(private_cbb.get(), &generated_priv_der, &generated_priv_der_len));
  bssl::UniquePtr<uint8_t> generated_priv_der_ptr(generated_priv_der);

  // ---- 8. Convert expected private PEM to DER ----
  uint8_t *expected_priv_der = nullptr;
  long expected_priv_der_len = 0;
  ASSERT_TRUE(PEM_to_DER(test.expected_deterministic_priv_pem, &expected_priv_der, &expected_priv_der_len));
  bssl::UniquePtr<uint8_t> expected_priv_der_ptr(expected_priv_der);

  // ---- 9. Compare private key DERs ----
  EXPECT_EQ(generated_priv_der_len, static_cast<size_t>(expected_priv_der_len))
      << "Private key DER length mismatch";
  EXPECT_EQ(Bytes(generated_priv_der, generated_priv_der_len),
            Bytes(expected_priv_der, expected_priv_der_len))
      << "Private key DER content mismatch";

  // ---- 10. Verify seed-format private key DER is smaller than public key DER ----
  EXPECT_LT(generated_priv_der_len, generated_pub_der_len);
}

// Test KEM public key round-trip serialization using i2d_PUBKEY and d2i_PUBKEY functions.
TEST_P(KEMTest, I2dAndD2iPUBKEYRoundTrip) {
  const KEMTestVector &test = GetParam();
  
  // ---- 1. Generate a keypair ----
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(test.nid));
  ASSERT_TRUE(pkey);

  // ---- 2. Encode public key using i2d_PUBKEY ----
  uint8_t *encoded_der = nullptr;
  int encoded_der_len = i2d_PUBKEY(pkey.get(), &encoded_der);
  ASSERT_GT(encoded_der_len, 0);
  ASSERT_TRUE(encoded_der);
  bssl::UniquePtr<uint8_t> free_encoded_der(encoded_der);

  // ---- 3. Decode back using d2i_PUBKEY ----
  const uint8_t *encoded_der_ptr = encoded_der;
  bssl::UniquePtr<EVP_PKEY> decoded_pkey(d2i_PUBKEY(nullptr, &encoded_der_ptr, encoded_der_len));
  ASSERT_TRUE(decoded_pkey);
  ASSERT_EQ(EVP_PKEY_id(decoded_pkey.get()), EVP_PKEY_KEM);

  // ---- 4. Verify round-trip correctness ----
  EXPECT_EQ(1, EVP_PKEY_cmp(pkey.get(), decoded_pkey.get()));

  // ---- i2d_PUBKEY output should work with EVP_parse_public_key ----
  CBS cbs;
  CBS_init(&cbs, encoded_der, encoded_der_len);
  bssl::UniquePtr<EVP_PKEY> cross_decoded_pkey(EVP_parse_public_key(&cbs));
  ASSERT_TRUE(cross_decoded_pkey);
  EXPECT_EQ(1, EVP_PKEY_cmp(pkey.get(), cross_decoded_pkey.get()));
}

// Test round-trip encoding/decoding of KEM private keys using PKCS#8 format via EVP_PKEY2PKCS8, i2d_PKCS8_PRIV_KEY_INFO, and d2i_PrivateKey.
TEST_P(KEMTest, PKCS8_PrivateKey_RoundTrip) {
  const KEMTestVector &test = GetParam();
  
  // ---- 1. Generate a keypair ----
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(test.nid));
  ASSERT_TRUE(pkey);

  // ---- 2. Convert to PKCS8 structure using EVP_PKEY2PKCS8 ----
  bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> pkcs8_info(EVP_PKEY2PKCS8(pkey.get()));
  ASSERT_TRUE(pkcs8_info);

  // ---- 3. Encode PKCS8 to DER using i2d_PKCS8_PRIV_KEY_INFO ----
  uint8_t *encoded_der = nullptr;
  int encoded_der_len = i2d_PKCS8_PRIV_KEY_INFO(pkcs8_info.get(), &encoded_der);
  ASSERT_GT(encoded_der_len, 0);
  ASSERT_TRUE(encoded_der);
  bssl::UniquePtr<uint8_t> free_encoded_der(encoded_der);

  // ---- 4. Decode back using d2i_PrivateKey ----
  const uint8_t *encoded_der_ptr = encoded_der;
  bssl::UniquePtr<EVP_PKEY> decoded_pkey(d2i_PrivateKey(EVP_PKEY_KEM, nullptr, &encoded_der_ptr, encoded_der_len));
  ASSERT_TRUE(decoded_pkey);
  ASSERT_EQ(EVP_PKEY_id(decoded_pkey.get()), EVP_PKEY_KEM);

  // ---- 5. Verify round-trip correctness by comparing secret keys ----
  ASSERT_TRUE(pkey->pkey.kem_key->secret_key);
  ASSERT_TRUE(decoded_pkey->pkey.kem_key->secret_key);
  EXPECT_EQ(Bytes(pkey->pkey.kem_key->secret_key, test.secret_key_len),
            Bytes(decoded_pkey->pkey.kem_key->secret_key, test.secret_key_len));

  // ---- 6. i2d_PKCS8_PRIV_KEY_INFO output should work with EVP_parse_private_key ----
  CBS cbs;
  CBS_init(&cbs, encoded_der, encoded_der_len);
  bssl::UniquePtr<EVP_PKEY> cross_decoded_pkey(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(cross_decoded_pkey);
  EXPECT_EQ(Bytes(pkey->pkey.kem_key->secret_key, test.secret_key_len),
            Bytes(cross_decoded_pkey->pkey.kem_key->secret_key, test.secret_key_len));
}

// Test cross-compatibility between modern EVP_marshal_* encoding functions d2i_* decoding functions
TEST_P(KEMTest, ASN1_Methods_Cross_Compatibility) {
  const KEMTestVector &test = GetParam();
  
  // ---- 1. Generate a keypair ----
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(test.nid));
  ASSERT_TRUE(pkey);

// ---- 2. Test if the encoded public key using EVP_marshal_public_key can be decoded using d2i_PUBKEY ----
  bssl::ScopedCBB cbb;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_public_key(cbb.get(), pkey.get()));
  uint8_t *marshal_der;
  size_t marshal_der_len;
  ASSERT_TRUE(CBB_finish(cbb.get(), &marshal_der, &marshal_der_len));
  bssl::UniquePtr<uint8_t> free_marshal_der(marshal_der);

  const uint8_t *marshal_der_ptr = marshal_der;
  bssl::UniquePtr<EVP_PKEY> decoded_from_marshal(d2i_PUBKEY(nullptr, &marshal_der_ptr, marshal_der_len));
  ASSERT_TRUE(decoded_from_marshal);
  EXPECT_EQ(1, EVP_PKEY_cmp(pkey.get(), decoded_from_marshal.get()));

// ---- 3. Test if the encoded private key using EVP_marshal_private_key can be decoded using d2i_PrivateKey ----
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(cbb.get(), pkey.get()));
  uint8_t *marshal_priv_der;
  size_t marshal_priv_der_len;
  ASSERT_TRUE(CBB_finish(cbb.get(), &marshal_priv_der, &marshal_priv_der_len));
  bssl::UniquePtr<uint8_t> free_marshal_priv_der(marshal_priv_der);

  const uint8_t *marshal_priv_der_ptr = marshal_priv_der;
  bssl::UniquePtr<EVP_PKEY> decoded_priv_from_marshal(d2i_PrivateKey(EVP_PKEY_KEM, nullptr, 
                                                      &marshal_priv_der_ptr, marshal_priv_der_len));
  ASSERT_TRUE(decoded_priv_from_marshal);
  EXPECT_EQ(Bytes(pkey->pkey.kem_key->secret_key, test.secret_key_len),
            Bytes(decoded_priv_from_marshal->pkey.kem_key->secret_key, test.secret_key_len));
}

TEST_P(KEMTest, ParsePrivateKeySeed) {

  // ---- 1. Setup phase: parse provided public/private from PEM strings ----
  CBS cbs_pub, cbs_priv;
  uint8_t *der_pub = nullptr, *der_priv = nullptr;
  long der_pub_len = 0, der_priv_len = 0;

  ASSERT_TRUE(PEM_to_DER(GetParam().public_pem_str, &der_pub, &der_pub_len));
  ASSERT_TRUE(PEM_to_DER(GetParam().private_pem_seed_str, &der_priv, &der_priv_len));

  CBS_init(&cbs_pub, der_pub, der_pub_len);
  CBS_init(&cbs_priv, der_priv, der_priv_len);

  // ---- 2. Attempt to parse private key ----
  bssl::UniquePtr<EVP_PKEY> pkey1(EVP_parse_private_key(&cbs_priv));
  ASSERT_TRUE(pkey1);

  // ---- 3. Attempt to parse public key ----
  bssl::UniquePtr<EVP_PKEY> pkey2(EVP_parse_public_key(&cbs_pub));
  ASSERT_TRUE(pkey2);

  // ---- 4. Compare public keys ----
  // EVP_parse_private_key will populate both public and private key, we verify
  // that the public key calculated by EVP_parse_private_key is equivalent to
  // the public key that was parsed from PEM.
  ASSERT_EQ(1, EVP_PKEY_cmp(pkey1.get(), pkey2.get()));

  // Clean up
  OPENSSL_free(der_pub);
  OPENSSL_free(der_priv);
}

TEST(KEMTest, InvalidSeedLength) {
  // Test malformed ML-KEM-512 private key with 63-byte seed instead of 64
  // This should fail with EVP_R_INVALID_BUFFER_SIZE when kem_priv_decode
  // calls KEM_KEY_set_raw_keypair_from_seed
  
  uint8_t *der_priv = nullptr;
  long der_priv_len = 0;
  
  ASSERT_TRUE(PEM_to_DER(mlkem_512_bad_seed_pem_str, &der_priv, &der_priv_len));
  
  CBS cbs_priv;
  CBS_init(&cbs_priv, der_priv, der_priv_len);
  
  // This should fail because the seed is only 63 bytes instead of 64
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_parse_private_key(&cbs_priv));
  ASSERT_FALSE(pkey);
  
  uint32_t err = ERR_get_error();
  EXPECT_EQ(ERR_GET_LIB(err), ERR_LIB_EVP);
  EXPECT_EQ(ERR_GET_REASON(err), EVP_R_INVALID_BUFFER_SIZE);
  
  OPENSSL_free(der_priv);
}

// Test that parsing a seed-format PKCS#8 and re-serializing produces seed
// format (round-trip preservation).
TEST_P(KEMTest, SeedFormatRoundTrip) {
  const KEMTestVector &test = GetParam();

  // Parse seed-format private key
  uint8_t *der = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(test.private_pem_seed_str, &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  CBS cbs;
  CBS_init(&cbs, der, der_len);
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(pkey);
  ASSERT_TRUE(pkey->pkey.kem_key->seed);

  // Re-serialize — should produce seed format
  bssl::ScopedCBB cbb;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(cbb.get(), pkey.get()));

  uint8_t *der2 = nullptr;
  size_t der2_len = 0;
  ASSERT_TRUE(CBB_finish(cbb.get(), &der2, &der2_len));
  bssl::UniquePtr<uint8_t> free_der2(der2);

  // Round-trip: output should match input
  EXPECT_EQ(Bytes(der, der_len), Bytes(der2, der2_len));

  // Parse again and verify key material matches
  CBS cbs2;
  CBS_init(&cbs2, der2, der2_len);
  bssl::UniquePtr<EVP_PKEY> pkey2(EVP_parse_private_key(&cbs2));
  ASSERT_TRUE(pkey2);
  EXPECT_EQ(Bytes(pkey->pkey.kem_key->secret_key, test.secret_key_len),
            Bytes(pkey2->pkey.kem_key->secret_key, test.secret_key_len));
}

// Test that keys created via raw import (no seed) encode in expanded format.
TEST_P(KEMTest, RawImportExpandedFormat) {
  const KEMTestVector &test = GetParam();

  // Generate a key to get valid raw key material
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(test.nid));
  ASSERT_TRUE(pkey);

  // Extract raw secret key
  size_t sk_len = 0;
  ASSERT_TRUE(EVP_PKEY_get_raw_private_key(pkey.get(), nullptr, &sk_len));
  std::vector<uint8_t> sk(sk_len);
  ASSERT_TRUE(EVP_PKEY_get_raw_private_key(pkey.get(), sk.data(), &sk_len));

  // Create a new key from raw secret key — no seed available
  bssl::UniquePtr<EVP_PKEY> raw_pkey(
      EVP_PKEY_kem_new_raw_secret_key(test.nid, sk.data(), sk_len));
  ASSERT_TRUE(raw_pkey);
  ASSERT_TRUE(raw_pkey->pkey.kem_key->seed == nullptr);

  // Encode — should produce expanded format
  bssl::ScopedCBB cbb;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(cbb.get(), raw_pkey.get()));

  uint8_t *der = nullptr;
  size_t der_len = 0;
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  // Verify expanded format: parse PKCS#8 and check for OCTET STRING tag
  CBS pkcs8, algorithm, private_key, expanded_key;
  uint64_t version = 0;
  CBS_init(&pkcs8, der, der_len);
  ASSERT_TRUE(CBS_get_asn1(&pkcs8, &pkcs8, CBS_ASN1_SEQUENCE));
  ASSERT_TRUE(CBS_get_asn1_uint64(&pkcs8, &version));
  ASSERT_TRUE(CBS_get_asn1(&pkcs8, &algorithm, CBS_ASN1_SEQUENCE));
  ASSERT_TRUE(CBS_get_asn1(&pkcs8, &private_key, CBS_ASN1_OCTETSTRING));
  ASSERT_TRUE(CBS_get_asn1(&private_key, &expanded_key, CBS_ASN1_OCTETSTRING));
  ASSERT_EQ(CBS_len(&expanded_key), test.secret_key_len);
}

// Test EVP_PKEY_get_private_seed for ML-KEM keys.
TEST_P(KEMTest, GetPrivateSeed) {
  const KEMTestVector &test = GetParam();

  // Generate key and check it has a seed configured.
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(test.nid));
  ASSERT_TRUE(pkey);
  ASSERT_TRUE(pkey->pkey.kem_key->seed);

  // Check size works.
  size_t seed_len = 0;
  ASSERT_TRUE(EVP_PKEY_get_private_seed(pkey.get(), nullptr, &seed_len));
  EXPECT_EQ(seed_len, pkey->pkey.kem_key->kem->keygen_seed_len);

  // Check correct seed is returned.
  std::vector<uint8_t> seed(seed_len);
  ASSERT_TRUE(EVP_PKEY_get_private_seed(pkey.get(), seed.data(), &seed_len));
  EXPECT_EQ(seed_len, pkey->pkey.kem_key->kem->keygen_seed_len);
  EXPECT_EQ(Bytes(seed), Bytes(pkey->pkey.kem_key->seed, seed_len));

  // Oversized buffer is accepted; the function reports the actual length
  // written.
  seed_len = seed.size() + 16;
  std::vector<uint8_t> big_seed(seed_len);
  ASSERT_TRUE(
      EVP_PKEY_get_private_seed(pkey.get(), big_seed.data(), &seed_len));
  EXPECT_EQ(seed_len, pkey->pkey.kem_key->kem->keygen_seed_len);
  EXPECT_EQ(Bytes(big_seed.data(), seed_len), Bytes(seed));

  // Short buffer must fail with EVP_R_BUFFER_TOO_SMALL.
  seed_len = pkey->pkey.kem_key->kem->keygen_seed_len - 1;
  std::vector<uint8_t> short_seed(seed_len);
  ERR_clear_error();
  EXPECT_FALSE(
      EVP_PKEY_get_private_seed(pkey.get(), short_seed.data(), &seed_len));
  uint32_t err = ERR_get_error();
  EXPECT_EQ(ERR_GET_LIB(err), ERR_LIB_EVP);
  EXPECT_EQ(ERR_GET_REASON(err), EVP_R_BUFFER_TOO_SMALL);

  // A key parsed from seed-format PKCS#8 exposes its seed.
  uint8_t *priv_der = nullptr;
  long priv_der_len = 0;
  ASSERT_TRUE(
      PEM_to_DER(test.private_pem_seed_str, &priv_der, &priv_der_len));
  bssl::UniquePtr<uint8_t> free_priv_der(priv_der);
  CBS cbs;
  CBS_init(&cbs, priv_der, priv_der_len);
  bssl::UniquePtr<EVP_PKEY> parsed(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(parsed);
  ASSERT_TRUE(parsed->pkey.kem_key->seed);

  seed_len = 0;
  ASSERT_TRUE(EVP_PKEY_get_private_seed(parsed.get(), nullptr, &seed_len));
  std::vector<uint8_t> parsed_seed(seed_len);
  ASSERT_TRUE(EVP_PKEY_get_private_seed(parsed.get(), parsed_seed.data(),
                                        &seed_len));
  EXPECT_EQ(Bytes(parsed_seed),
            Bytes(parsed->pkey.kem_key->seed, seed_len));

  // Raw expanded private key has no seed and the operation must return
  // EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE.
  size_t sk_len = 0;
  ASSERT_TRUE(EVP_PKEY_get_raw_private_key(pkey.get(), nullptr, &sk_len));
  std::vector<uint8_t> sk(sk_len);
  ASSERT_TRUE(EVP_PKEY_get_raw_private_key(pkey.get(), sk.data(), &sk_len));

  bssl::UniquePtr<EVP_PKEY> raw_pkey(
      EVP_PKEY_kem_new_raw_secret_key(test.nid, sk.data(), sk_len));
  ASSERT_TRUE(raw_pkey);
  ASSERT_EQ(raw_pkey->pkey.kem_key->seed, nullptr);

  seed_len = raw_pkey->pkey.kem_key->kem->keygen_seed_len;
  std::vector<uint8_t> unused(seed_len);
  ERR_clear_error();
  EXPECT_FALSE(
      EVP_PKEY_get_private_seed(raw_pkey.get(), unused.data(), &seed_len));
  err = ERR_get_error();
  EXPECT_EQ(ERR_GET_LIB(err), ERR_LIB_EVP);
  EXPECT_EQ(ERR_GET_REASON(err),
            EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE);
}

// EVP_PKEY_get_private_seed should reject NULL |key| and NULL |out_len|.
TEST(KEMTest, GetPrivateSeedNullArguments) {
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(NID_MLKEM512));
  ASSERT_TRUE(pkey);

  size_t seed_len = 0;
  ERR_clear_error();
  EXPECT_FALSE(EVP_PKEY_get_private_seed(nullptr, nullptr, &seed_len));
  EXPECT_FALSE(EVP_PKEY_get_private_seed(pkey.get(), nullptr, nullptr));
}

// Test that a generated key (seed format) can perform encaps/decaps correctly
// after a serialize → parse round-trip.
TEST_P(KEMTest, SeedFormatEncapsDecapsRoundTrip) {
  const KEMTestVector &test = GetParam();

  // Generate a key pair
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(test.nid));
  ASSERT_TRUE(pkey);

  // Serialize (seed format) and parse back
  bssl::ScopedCBB cbb;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(cbb.get(), pkey.get()));
  uint8_t *der = nullptr;
  size_t der_len = 0;
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  CBS cbs;
  CBS_init(&cbs, der, der_len);
  bssl::UniquePtr<EVP_PKEY> parsed_pkey(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(parsed_pkey);

  // Encapsulate with the original key's public key
  bssl::UniquePtr<EVP_PKEY_CTX> enc_ctx(EVP_PKEY_CTX_new(pkey.get(), nullptr));
  ASSERT_TRUE(enc_ctx);
  size_t ct_len = 0, ss_len = 0;
  ASSERT_TRUE(EVP_PKEY_encapsulate(enc_ctx.get(), nullptr, &ct_len,
                                   nullptr, &ss_len));
  std::vector<uint8_t> ct(ct_len), ss_enc(ss_len);
  ASSERT_TRUE(EVP_PKEY_encapsulate(enc_ctx.get(), ct.data(), &ct_len,
                                   ss_enc.data(), &ss_len));

  // Decapsulate with the parsed key
  bssl::UniquePtr<EVP_PKEY_CTX> dec_ctx(
      EVP_PKEY_CTX_new(parsed_pkey.get(), nullptr));
  ASSERT_TRUE(dec_ctx);
  std::vector<uint8_t> ss_dec(ss_len);
  ASSERT_TRUE(EVP_PKEY_decapsulate(dec_ctx.get(), ss_dec.data(), &ss_len,
                                   ct.data(), ct_len));

  EXPECT_EQ(Bytes(ss_enc), Bytes(ss_dec));
}


// RFC 9935 section 6 defines a third ML-KEM-XX-PrivateKey CHOICE, |both|,
// carrying the seed and the expandedKey in a SEQUENCE. The vectors below are
// the "Both Format" examples from Appendix C.1; each describes the same key
// pair as the seed-only and expandedKey-only examples for its parameter set.
struct KEMBothFormatTestVector {
  int nid;
  const char *both_pem_str;
  const char *seed_pem_str;
  const char *expanded_pem_str;
  const char *public_pem_str;
  size_t secret_key_len;
  size_t seed_len;
};

static const KEMBothFormatTestVector kemBothFormatParameters[] = {
    {NID_MLKEM512, mlkem_512_priv_both_pem_str, mlkem_512_seed_pem_str,
     mlkem_512_priv_expanded_pem_str, mlkem_512_pub_pem_str, 1632, 64},
    {NID_MLKEM768, mlkem_768_priv_both_pem_str, mlkem_768_seed_pem_str,
     mlkem_768_priv_expanded_pem_str, mlkem_768_pub_pem_str, 2400, 64},
    {NID_MLKEM1024, mlkem_1024_priv_both_pem_str, mlkem_1024_seed_pem_str,
     mlkem_1024_priv_expanded_pem_str, mlkem_1024_pub_pem_str, 3168, 64},
};

class KEMBothFormatTest
    : public testing::TestWithParam<KEMBothFormatTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, KEMBothFormatTest,
                         testing::ValuesIn(kemBothFormatParameters));

// A |both| private key must parse, and must yield the same key material as the
// seed-only and expandedKey-only encodings of the same key pair.
TEST_P(KEMBothFormatTest, ParsePrivateKeyBoth) {
  const KEMBothFormatTestVector &test = GetParam();

  uint8_t *der_both = nullptr, *der_seed = nullptr, *der_expanded = nullptr,
          *der_pub = nullptr;
  long der_both_len = 0, der_seed_len = 0, der_expanded_len = 0,
       der_pub_len = 0;
  ASSERT_TRUE(PEM_to_DER(test.both_pem_str, &der_both, &der_both_len));
  bssl::UniquePtr<uint8_t> free_both(der_both);
  ASSERT_TRUE(PEM_to_DER(test.seed_pem_str, &der_seed, &der_seed_len));
  bssl::UniquePtr<uint8_t> free_seed(der_seed);
  ASSERT_TRUE(
      PEM_to_DER(test.expanded_pem_str, &der_expanded, &der_expanded_len));
  bssl::UniquePtr<uint8_t> free_expanded(der_expanded);
  ASSERT_TRUE(PEM_to_DER(test.public_pem_str, &der_pub, &der_pub_len));
  bssl::UniquePtr<uint8_t> free_pub(der_pub);

  CBS cbs;
  CBS_init(&cbs, der_both, der_both_len);
  bssl::UniquePtr<EVP_PKEY> both(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(both);
  EXPECT_EQ(0u, CBS_len(&cbs));
  EXPECT_EQ(test.nid, EVP_PKEY_kem_get_type(both.get()));

  CBS_init(&cbs, der_seed, der_seed_len);
  bssl::UniquePtr<EVP_PKEY> seed(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(seed);

  CBS_init(&cbs, der_expanded, der_expanded_len);
  bssl::UniquePtr<EVP_PKEY> expanded(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(expanded);

  CBS_init(&cbs, der_pub, der_pub_len);
  bssl::UniquePtr<EVP_PKEY> pub(EVP_parse_public_key(&cbs));
  ASSERT_TRUE(pub);

  // The expanded private key matches the expandedKey-only encoding ...
  ASSERT_TRUE(both->pkey.kem_key->secret_key);
  EXPECT_EQ(Bytes(both->pkey.kem_key->secret_key, test.secret_key_len),
            Bytes(expanded->pkey.kem_key->secret_key, test.secret_key_len));

  // ... the seed is retained, matching the seed-only encoding ...
  ASSERT_TRUE(both->pkey.kem_key->seed);
  EXPECT_EQ(Bytes(both->pkey.kem_key->seed, test.seed_len),
            Bytes(seed->pkey.kem_key->seed, test.seed_len));

  // ... and the public key derived from the seed matches both the seed-only
  // encoding and the example public key.
  EXPECT_EQ(1, EVP_PKEY_cmp(both.get(), seed.get()));
  EXPECT_EQ(1, EVP_PKEY_cmp(both.get(), pub.get()));
}

// RFC 9935 section 6 RECOMMENDS the seed format. A key parsed from |both|
// retains its seed, so re-encoding produces the seed-only example byte for
// byte.
TEST_P(KEMBothFormatTest, BothFormatReEncodesAsSeed) {
  const KEMBothFormatTestVector &test = GetParam();

  uint8_t *der_both = nullptr, *der_seed = nullptr;
  long der_both_len = 0, der_seed_len = 0;
  ASSERT_TRUE(PEM_to_DER(test.both_pem_str, &der_both, &der_both_len));
  bssl::UniquePtr<uint8_t> free_both(der_both);
  ASSERT_TRUE(PEM_to_DER(test.seed_pem_str, &der_seed, &der_seed_len));
  bssl::UniquePtr<uint8_t> free_seed(der_seed);

  CBS cbs;
  CBS_init(&cbs, der_both, der_both_len);
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(pkey);

  bssl::ScopedCBB cbb;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(cbb.get(), pkey.get()));
  uint8_t *der_out = nullptr;
  size_t der_out_len = 0;
  ASSERT_TRUE(CBB_finish(cbb.get(), &der_out, &der_out_len));
  bssl::UniquePtr<uint8_t> free_out(der_out);

  EXPECT_EQ(Bytes(der_seed, der_seed_len), Bytes(der_out, der_out_len));
}

// A key parsed from |both| must be usable for decapsulation.
TEST_P(KEMBothFormatTest, BothFormatEncapsDecapsRoundTrip) {
  const KEMBothFormatTestVector &test = GetParam();

  uint8_t *der = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(test.both_pem_str, &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  CBS cbs;
  CBS_init(&cbs, der, der_len);
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(pkey);

  bssl::UniquePtr<EVP_PKEY_CTX> enc_ctx(EVP_PKEY_CTX_new(pkey.get(), nullptr));
  ASSERT_TRUE(enc_ctx);
  size_t ct_len = 0, ss_len = 0;
  ASSERT_TRUE(
      EVP_PKEY_encapsulate(enc_ctx.get(), nullptr, &ct_len, nullptr, &ss_len));
  std::vector<uint8_t> ct(ct_len), ss_enc(ss_len);
  ASSERT_TRUE(EVP_PKEY_encapsulate(enc_ctx.get(), ct.data(), &ct_len,
                                   ss_enc.data(), &ss_len));

  bssl::UniquePtr<EVP_PKEY_CTX> dec_ctx(EVP_PKEY_CTX_new(pkey.get(), nullptr));
  ASSERT_TRUE(dec_ctx);
  std::vector<uint8_t> ss_dec(ss_len);
  ASSERT_TRUE(EVP_PKEY_decapsulate(dec_ctx.get(), ss_dec.data(), &ss_len,
                                   ct.data(), ct_len));

  EXPECT_EQ(Bytes(ss_enc), Bytes(ss_dec));
}

// RFC 9935 section 8 requires the seed consistency check, and mandates that an
// inconsistent private key be rejected as malformed. These are the two |both|
// examples from Appendix C.4.1.
TEST(KEMTest, ParsePrivateKeyBothInconsistent) {
  const struct {
    const char *name;
    const char *pem_str;
  } kInconsistent[] = {
      {"C.4.1 example 1: seed and expandedKey disagree",
       mlkem_512_priv_both_inconsistent_pem_str},
      {"C.4.1 example 4: expandedKey differs from the seed only in z",
       mlkem_512_priv_both_inconsistent_z_pem_str},
  };

  for (const auto &t : kInconsistent) {
    SCOPED_TRACE(t.name);

    uint8_t *der = nullptr;
    long der_len = 0;
    ASSERT_TRUE(PEM_to_DER(t.pem_str, &der, &der_len));
    bssl::UniquePtr<uint8_t> free_der(der);

    CBS cbs;
    CBS_init(&cbs, der, der_len);
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_parse_private_key(&cbs));
    EXPECT_FALSE(pkey);

    uint32_t err = ERR_get_error();
    EXPECT_EQ(ERR_GET_LIB(err), ERR_LIB_EVP);
    EXPECT_EQ(ERR_GET_REASON(err), EVP_R_DECODE_ERROR);
    ERR_clear_error();
  }
}

// FIPS 203 section 7.3, which RFC 9935 section 8 points at for the expandedKey
// format, requires a hash check before an expanded key is used. Parsing runs
// that check plus a pairwise consistency test, which between them reject the
// two expandedKey-only examples from Appendix C.4.1. Each example fails a
// different check, and the reason codes distinguish them.
TEST(KEMTest, ParsePrivateKeyExpandedInconsistent) {
  const struct {
    const char *name;
    const char *pem_str;
    int reason;
  } kInconsistent[] = {
      // s_0 is mutated but H(ek) is intact, so the hash check passes and only
      // the PCT catches the key.
      {"C.4.1 example 2: mutated s_0, valid H(ek)",
       mlkem_512_priv_expanded_mutated_s0_pem_str, EVP_R_KEM_PCT_FAILED},
      // H(ek) no longer matches the embedded ek, so the hash check catches it
      // before the PCT runs.
      {"C.4.1 example 3: mutated H(ek)",
       mlkem_512_priv_expanded_mutated_hek_pem_str, EVP_R_INVALID_PRIVATE_KEY},
  };

  for (const auto &t : kInconsistent) {
    SCOPED_TRACE(t.name);

    uint8_t *der = nullptr;
    long der_len = 0;
    ASSERT_TRUE(PEM_to_DER(t.pem_str, &der, &der_len));
    bssl::UniquePtr<uint8_t> free_der(der);

    ERR_clear_error();
    CBS cbs;
    CBS_init(&cbs, der, der_len);
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_parse_private_key(&cbs));
    EXPECT_FALSE(pkey);

    uint32_t err = ERR_get_error();
    EXPECT_EQ(ERR_GET_LIB(err), ERR_LIB_EVP);
    EXPECT_EQ(ERR_GET_REASON(err), t.reason);
    ERR_clear_error();
  }
}

// Re-encodes the PKCS#8 in |der| with one extra byte appended inside the
// privateKey OCTET STRING, so the CHOICE element is followed by trailing data.
static bool AppendTrailingByteToPrivateKey(const uint8_t *der, size_t der_len,
                                           std::vector<uint8_t> *out) {
  CBS pkcs8, algorithm, private_key;
  uint64_t version = 0;
  CBS_init(&pkcs8, der, der_len);
  if (!CBS_get_asn1(&pkcs8, &pkcs8, CBS_ASN1_SEQUENCE) ||
      !CBS_get_asn1_uint64(&pkcs8, &version) ||
      !CBS_get_asn1_element(&pkcs8, &algorithm, CBS_ASN1_SEQUENCE) ||
      !CBS_get_asn1(&pkcs8, &private_key, CBS_ASN1_OCTETSTRING)) {
    return false;
  }

  bssl::ScopedCBB cbb;
  CBB seq, pk;
  if (!CBB_init(cbb.get(), der_len + 16) ||
      !CBB_add_asn1(cbb.get(), &seq, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1_uint64(&seq, version) ||
      !CBB_add_bytes(&seq, CBS_data(&algorithm), CBS_len(&algorithm)) ||
      !CBB_add_asn1(&seq, &pk, CBS_ASN1_OCTETSTRING) ||
      !CBB_add_bytes(&pk, CBS_data(&private_key), CBS_len(&private_key)) ||
      !CBB_add_u8(&pk, 0x00) || !CBB_flush(cbb.get())) {
    return false;
  }

  uint8_t *buf = nullptr;
  size_t buf_len = 0;
  if (!CBB_finish(cbb.get(), &buf, &buf_len)) {
    return false;
  }
  out->assign(buf, buf + buf_len);
  OPENSSL_free(buf);
  return true;
}

// The CHOICE occupies the whole privateKey OCTET STRING, so trailing data after
// it is malformed DER and must be rejected for every CHOICE. |EVP_parse_private_key|
// rejects trailing data inside the outer PKCS#8 SEQUENCE but does not re-examine
// the privateKey contents, so |kem_priv_decode| is what has to catch this.
TEST_P(KEMBothFormatTest, TrailingDataAfterChoiceRejected) {
  const KEMBothFormatTestVector &test = GetParam();

  const struct {
    const char *name;
    const char *pem_str;
  } kCases[] = {
      {"seed [0]", test.seed_pem_str},
      {"expandedKey", test.expanded_pem_str},
      {"both SEQUENCE", test.both_pem_str},
  };

  for (const auto &t : kCases) {
    SCOPED_TRACE(t.name);

    uint8_t *der = nullptr;
    long der_len = 0;
    ASSERT_TRUE(PEM_to_DER(t.pem_str, &der, &der_len));
    bssl::UniquePtr<uint8_t> free_der(der);

    // The unmodified key parses, so the rejection below is attributable to the
    // trailing byte rather than to the re-encoding.
    CBS cbs;
    CBS_init(&cbs, der, der_len);
    bssl::UniquePtr<EVP_PKEY> ok(EVP_parse_private_key(&cbs));
    ASSERT_TRUE(ok);

    std::vector<uint8_t> extended;
    ASSERT_TRUE(AppendTrailingByteToPrivateKey(der, der_len, &extended));

    ERR_clear_error();
    CBS bad_cbs;
    CBS_init(&bad_cbs, extended.data(), extended.size());
    bssl::UniquePtr<EVP_PKEY> bad(EVP_parse_private_key(&bad_cbs));
    EXPECT_FALSE(bad);
    EXPECT_EQ(ERR_GET_REASON(ERR_get_error()), EVP_R_DECODE_ERROR);
    ERR_clear_error();
  }
}

// A |both| SEQUENCE whose seed or expandedKey has the wrong length must be
// rejected before any key generation is attempted.
TEST(KEMTest, ParsePrivateKeyBothInvalidLength) {
  uint8_t *der = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(mlkem_512_priv_both_pem_str, &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  // Truncating the DER leaves a |both| SEQUENCE whose contents no longer parse
  // as two complete OCTET STRINGs.
  CBS cbs;
  CBS_init(&cbs, der, der_len - 1);
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_parse_private_key(&cbs));
  EXPECT_FALSE(pkey);
  ERR_clear_error();
}


// Wycheproof test vector mapping for KEMs
struct WycheproofKEM {
  const char name[20];
  const int nid;
  size_t ciphertext_len;
  size_t shared_secret_len;
  const char *encaps_test;
  const char *decaps_seed_test;
  const char *decaps_noseed_test;
};

//= third_party/vectors/vectors_spec.md#wycheproof
//# AWS-LC MUST test against `testvectors_v1/mlkem_1024_test.txt`.
//# AWS-LC MUST test against `testvectors_v1/mlkem_512_test.txt`.
//# AWS-LC MUST test against `testvectors_v1/mlkem_768_test.txt`.
//# AWS-LC MUST test against `testvectors_v1/mlkem_1024_encaps_test.txt`.
//# AWS-LC MUST test against `testvectors_v1/mlkem_1024_semi_expanded_decaps_test.txt`.
//# AWS-LC MUST test against `testvectors_v1/mlkem_512_encaps_test.txt`.
//# AWS-LC MUST test against `testvectors_v1/mlkem_512_semi_expanded_decaps_test.txt`.
//# AWS-LC MUST test against `testvectors_v1/mlkem_768_encaps_test.txt`.
//# AWS-LC MUST test against `testvectors_v1/mlkem_768_semi_expanded_decaps_test.txt`.
static const struct WycheproofKEM kWycheproofKEMs[] = {
    {
        "ML-KEM-512",
        NID_MLKEM512,
        768,
        32,
        "mlkem_512_encaps_test.txt",
        "mlkem_512_test.txt",
        "mlkem_512_semi_expanded_decaps_test.txt",
    },
    {
        "ML-KEM-768",
        NID_MLKEM768,
        1088,
        32,
        "mlkem_768_encaps_test.txt",
        "mlkem_768_test.txt",
        "mlkem_768_semi_expanded_decaps_test.txt",
    },
    {
        "ML-KEM-1024",
        NID_MLKEM1024,
        1568,
        32,
        "mlkem_1024_encaps_test.txt",
        "mlkem_1024_test.txt",
        "mlkem_1024_semi_expanded_decaps_test.txt",
    },
};

class WycheproofKEMTest : public testing::TestWithParam<WycheproofKEM> {};

INSTANTIATE_TEST_SUITE_P(
    All, WycheproofKEMTest, testing::ValuesIn(kWycheproofKEMs),
    [](const testing::TestParamInfo<WycheproofKEM> &params) -> std::string {
      std::string name = params.param.name;
      // Replace dashes with underscores for valid C++ test names
      std::replace(name.begin(), name.end(), '-', '_');
      return name;
    });

TEST_P(WycheproofKEMTest, Encaps) {
  std::string test_path =
      std::string(kWycheproofV1Path) + GetParam().encaps_test;
  FileTestGTest(test_path.c_str(), [&](FileTest *t) {
    std::vector<uint8_t> ek, m, expected_k, expected_c;
    std::string param_set;

    ASSERT_TRUE(t->GetInstruction(&param_set, "parameterSet"));
    ASSERT_EQ(param_set, GetParam().name);

    ASSERT_TRUE(t->GetBytes(&ek, "ek"));
    ASSERT_TRUE(t->GetBytes(&m, "m"));
    ASSERT_TRUE(t->GetBytes(&expected_k, "K"));
    ASSERT_TRUE(t->GetBytes(&expected_c, "c"));

    WycheproofResult result;
    ASSERT_TRUE(GetWycheproofResult(t, &result));

    bssl::UniquePtr<EVP_PKEY> pkey(
        EVP_PKEY_kem_new_raw_public_key(GetParam().nid, ek.data(), ek.size()));

    if (!result.IsValid() && result.HasFlag("ModulusOverflow")) {
      if (pkey) {
        // FIPS 203 only requires doing this check before encapsulation.
        fprintf(stderr,
                "WARNING: Successfully imported %s encapsulation key with "
                "ModulusOverflow. This is allowed by FIPS 203.\n",
                param_set.c_str());
      }
    }
    if (pkey) {
      bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new(pkey.get(), nullptr));
      ASSERT_TRUE(ctx);

      // Perform deterministic encapsulation using the m field as seed
      // see https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf#algorithm.17
      std::vector<uint8_t> ciphertext(GetParam().ciphertext_len);
      std::vector<uint8_t> shared_secret(GetParam().shared_secret_len);
      size_t ciphertext_len = ciphertext.size();
      size_t shared_secret_len = shared_secret.size();
      size_t seed_len = m.size();
      int encaps_result =
          EVP_PKEY_encapsulate_deterministic(ctx.get(), ciphertext.data(), &ciphertext_len,
                               shared_secret.data(), &shared_secret_len, m.data(), &seed_len);

      if (result.IsValid()) {
        EXPECT_TRUE(encaps_result);
        EXPECT_EQ(Bytes(ciphertext.data(), ciphertext_len), Bytes(expected_c));
        EXPECT_EQ(Bytes(shared_secret.data(), shared_secret_len),
                  Bytes(expected_k));
      } else {
        EXPECT_FALSE(encaps_result)
            << "Expected encapsulation to fail for flags: "
            << result.StringifyFlags();
      }
    }
  });
}

TEST_P(WycheproofKEMTest, DecapsSeed) {
  std::string test_path =
      std::string(kWycheproofV1Path) + GetParam().decaps_seed_test;
  FileTestGTest(test_path.c_str(), [&](FileTest *t) {
    std::vector<uint8_t> ek, seed, expected_k, ciphertext;
    std::string param_set;

    ASSERT_TRUE(t->GetInstruction(&param_set, "parameterSet"));
    ASSERT_EQ(param_set, GetParam().name);

    ASSERT_TRUE(t->GetBytes(&expected_k, "K"));
    ASSERT_TRUE(t->GetBytes(&ciphertext, "c"));
    
    WycheproofResult result;
    ASSERT_TRUE(GetWycheproofResult(t, &result));
    ASSERT_TRUE(t->GetBytes(&seed, "seed"));

    // Initialize using provided seed
    bssl::UniquePtr<EVP_PKEY_CTX> ctx(
        EVP_PKEY_CTX_new_id(EVP_PKEY_KEM, nullptr));
    ASSERT_TRUE(ctx);
    ASSERT_TRUE(EVP_PKEY_CTX_kem_set_params(ctx.get(), GetParam().nid));
    EVP_PKEY *raw = nullptr;
    ASSERT_TRUE(EVP_PKEY_keygen_init(ctx.get()));
    size_t seed_len = seed.size();
    int keygen_result = EVP_PKEY_keygen_deterministic(ctx.get(), &raw, seed.data(), &seed_len);
    
    // For invalid test cases, key generation might fail
    if (!result.IsValid() && !keygen_result) {
      // Expected failure in key generation for invalid cases
      return;
    }
    
    ASSERT_TRUE(keygen_result);
    ASSERT_TRUE(raw);
    bssl::UniquePtr<EVP_PKEY> pkey(raw);

    // Verify the generated public key matches the expected public key (if provided)
    if (t->HasAttribute("ek")) {
      ASSERT_TRUE(t->GetBytes(&ek, "ek"));
      size_t actual_ek_len = 0;
      ASSERT_TRUE(
          EVP_PKEY_get_raw_public_key(pkey.get(), nullptr, &actual_ek_len));
      ASSERT_EQ(actual_ek_len, ek.size());
      std::vector<uint8_t> actual_ek(actual_ek_len);
      ASSERT_TRUE(EVP_PKEY_get_raw_public_key(pkey.get(), actual_ek.data(),
                                              &actual_ek_len));
      EXPECT_EQ(Bytes(actual_ek), Bytes(ek));
    }

    // Perform decapsulation
    ctx.reset(EVP_PKEY_CTX_new(pkey.get(), nullptr));
    ASSERT_TRUE(ctx);
    std::vector<uint8_t> shared_secret(GetParam().shared_secret_len);
    size_t shared_secret_len = shared_secret.size();
    int decaps_result = EVP_PKEY_decapsulate(
        ctx.get(), shared_secret.data(), &shared_secret_len, ciphertext.data(),
        ciphertext.size());

    if (result.IsValid()) {
      EXPECT_TRUE(decaps_result);
      EXPECT_EQ(Bytes(shared_secret.data(), shared_secret_len),
                Bytes(expected_k));
    } else {
      EXPECT_FALSE(decaps_result)
          << "Expected decapsulation to fail for flags: "
          << result.StringifyFlags();
    }
  });
}

// Test decapsulation with expanded decaps keys
TEST_P(WycheproofKEMTest, DecapsNoSeed) {
  std::string test_path =
      std::string(kWycheproofV1Path) + GetParam().decaps_noseed_test;
  FileTestGTest(test_path.c_str(), [&](FileTest *t) {
    std::vector<uint8_t> dk, ciphertext;
    std::string param_set;

    ASSERT_TRUE(t->GetInstruction(&param_set, "parameterSet"));
    ASSERT_EQ(param_set, GetParam().name);

    ASSERT_TRUE(t->GetBytes(&dk, "dk"));
    ASSERT_TRUE(t->GetBytes(&ciphertext, "c"));

    WycheproofResult result;
    ASSERT_TRUE(GetWycheproofResult(t, &result));

    // Create key from raw private key bytes
    bssl::UniquePtr<EVP_PKEY> pkey(
        EVP_PKEY_kem_new_raw_secret_key(GetParam().nid, dk.data(), dk.size()));

    // Key creation should fail for incorrect key length
    if (result.HasFlag("IncorrectDecapsulationKeyLength")) {
      EXPECT_FALSE(pkey)
          << "Expected key creation to fail for incorrect key length";
      return;
    }

    // Warn if we successfully imported an invalid private key
    if (pkey && result.HasFlag("InvalidDecapsulationKey")) {
      fprintf(stderr,
              "WARNING: Successfully imported correct-length-but-invalid %s "
              "decapsulation key. This is allowed by FIPS 203.\n",
              param_set.c_str());
    }

    // For valid test cases, key creation should succeed
    if (result.IsValid()) {
      ASSERT_TRUE(pkey) << "Key creation failed unexpectedly for flags: "
                        << result.StringifyFlags();
    }

    // Perform decapsulation
    bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new(pkey.get(), nullptr));
    ASSERT_TRUE(ctx);

    std::vector<uint8_t> shared_secret(GetParam().shared_secret_len);
    size_t shared_secret_len = shared_secret.size();
    int decaps_result = EVP_PKEY_decapsulate(
        ctx.get(), shared_secret.data(), &shared_secret_len, ciphertext.data(),
        ciphertext.size());

    if (result.IsValid()) {
      EXPECT_TRUE(decaps_result)
          << "Expected decapsulation to succeed for valid test case";
    } else {
      EXPECT_FALSE(decaps_result)
          << "Expected decapsulation to fail for flags: "
          << result.StringifyFlags();
    }
  });
}
