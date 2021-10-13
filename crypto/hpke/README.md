## Overview
This folder contains the implementation of the Hybrid Public Key Encryption Standard, which integrates the use of asymmetric and symmetric cryptograohic primitives. The initial implementaiton is a fork of boringssl, where the changes made are sumurized as follow:

	- Integrate the post-quantum Supersingular Isogeny Key Encapsulation (SIKE) candidate into the HPKE.
	- Integrate the use of classical elliptic curve crypto scheme based on curve25519  with the post-quantum secure algorithm SIKE, where to reach a shared secret the communication parties should execute both schemes and append the resulting data before passing it to key shceduling.
	- Integrate the Kyber post-quantum algorithm into the HPKE design.
	- Implement the hybrid ECC + Kyber version of HPKE (where we designed the files for easy integration of further schemes into the standard).
	- Implemented several test and benchmarking functions (testing the algorithms separately or all together in an automated test function).
	
	 

### Install the library and run the tests

Usage is as follows: 
`mkdir aws-lc-build aws-lc-install && cd aws-lc-build`
`cmake -GNinja -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=../aws-lc-install ../`
`ninja install && ./crypto/crypto_test --gtest_filter=HPKETest.{x25519, SIKE, x25519_SIKE, KYBER, x25519_KYBER, HPKERoundTrip}`
The number of tests per algorithm may be adjusted by changing the value of the `NUMBER_TESTS constant inside hpke_test.cc`
The length of the encrypted plaintext starts from 1KB and is increased x10 in each iteration until 10MB. The maxinum length of the encrypted plaintext may be adjusted by changing the value of the `SIZE_PLAINTEXT constant inside hpke_test.cc`
