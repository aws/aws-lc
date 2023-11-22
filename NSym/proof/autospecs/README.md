# Autospecs

This dune package contains automatically generated Ocaml specifications and auxiliary Ocaml files associated with the automatically generated specifications. We use Cryptol specifications (for SAW proofs) as input and translate them into Ocaml specifications that work with NSym. Auxiliary Ocaml files contain functions or lemmas that are needed in the NSym proofs. We keep the automatically generated files in the repository to keep a record of them.

## SHA512

The automatically generated specifications include:
1. `SHA384rec.ml`: A translation from NSym/spec/SHA384rec.cry
2. `SHA512rec.ml`: A translation from NSym/spec/SHA512rec.cry

The auxiliary files are:
1. `sha2.ml`: A parameterization of the NSym proofs to allow both SHA384 and SHA512
2. `sha512rec_theorems.ml`: Base case and inductive case theorems for the recursive function `air_processBlocks_rec`
