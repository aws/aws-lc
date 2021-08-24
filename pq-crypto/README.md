# Post-quantum cryptography
This directory contains code for new post-quantum key exchange mechanisms. There are no known computationally feasible
attacks (classical or quantum) against these algorithms when used with the recommended key lengths.

## Quantum computers
Quantum computers use the properties of quantum mechanics to evaluate quantum algorithms. These algorithms can solve some
classically hard (exponential time) problems quickly (polynomial time). Shor's algorithm is one such algorithm which can
factor large integers, thus breaking RSA encryption and digital signature, and another quantum algorithm can solve the
discrete logarithm problem over arbitrary groups thus breaking Diffie–Hellman and elliptic curve Diffie–Hellman key
exchange.

## Post-quantum cryptography
Post-quantum public-key cryptographic algorithms run on a classical computer and are conjectured secure against both
classical and quantum attacks. NIST is in the process of reviewing submissions and standardizing them,
see more info on the [NIST website](https://csrc.nist.gov/Projects/Post-Quantum-Cryptography/Post-Quantum-Cryptography-Standardization).
Until the review and standardization is complete the post-quantum key exchanges in s2n **must not** be used for key
establishment by themselves. Instead they should only be used as part of a hybrid key exchange, which combines a
post-quantum key exchange scheme and a classical key exchange scheme.

## SIKE (Supersingular Isogeny Key Encapsulation)
The code in the pq-crypto/sike_r3 directory was imported from [S2N](https://github.com/aws/s2n-tls/tree/main/pq-crypto).