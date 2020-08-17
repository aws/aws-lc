## AWS LibCrypto Formal Verification

This repository contains specifications, proof scripts, and other artifacts required to formally verify portions of AWS LibCrypto. Formal verification is used to locate bugs and increase assurance of the correctness and security of the library.

## Verified Code

AWS LibCrypto includes many cryptographic algorithm implementations for several different platforms. Only a subset of algorithms are formally verified, and only for certain platforms. The verified implementations are:

(None)

For more details about each verified implementation, including details of the verification tool used, see the README in each tool-specific directory:

* [SAW](SAW/README.md)

## License

This project is licensed under the [Apache-2.0 License](LICENSE). See [Contributing](CONTRIBUTING.md) for information about contributions to this repository.
