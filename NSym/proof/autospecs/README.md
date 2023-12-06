# Autospecs

This dune package contains automatically generated Ocaml specifications. We use Cryptol specifications (for SAW proofs) as input and translate them into Ocaml specifications that work with NSym. We keep the automatically generated files in the repository to keep a record of them.

## SHA512

The automatically generated specifications include:
1. `SHA384rec.ml`: A translation from NSym/spec/SHA384rec.cry
2. `SHA512rec.ml`: A translation from NSym/spec/SHA512rec.cry
