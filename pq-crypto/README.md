# Post-quantum cryptography
This directory contains code for new post-quantum key exchange mechanisms. There are no known computationally feasible
attacks (classical or quantum) against these algorithms when used with the recommended key lengths.

## Post-quantum cryptography
Post-quantum public-key cryptographic algorithms run on a classical computer and are conjectured secure against both
classical and quantum attacks. NIST is in the process of reviewing submissions and standardizing them,
see more info on the [NIST website](https://csrc.nist.gov/Projects/Post-Quantum-Cryptography/Post-Quantum-Cryptography-Standardization).


## SIKE (Supersingular Isogeny Key Encapsulation)
The code in the pq-crypto/sike_r3 directory was moved from [S2N](https://github.com/aws/s2n-tls/tree/main/pq-crypto), 
which imports code from [SIKE's](https://github.com/microsoft/PQCrypto-SIDH/tree/effa607f244768cdd38f930887076373604eaa78) repository.