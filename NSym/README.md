# AWS libcrypto Verification using NSym
Proofs in this directory are carried out in NSym using [Cryptol](https://cryptol.net/) specifications. Cryptol specifications are automatically translated into Ocaml to be used in NSym proofs. The NSym proofs cover the verification of Arm assembly programs.

## Safety Guarantee in NSym proofs

* Memory region accesses are aligned and inbound.
