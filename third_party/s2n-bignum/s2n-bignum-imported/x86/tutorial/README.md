# Tutorials for s2n-bignum

This directory includes examples for verifying x86 programs using s2n-bignum
and HOL Light.
To verify programs in Arm, see `arm/tutorial`.

### Unary reasoning

1. `simple.ml`: Verifying a simple arithmetic property of a linear program.
2. `sequence.ml`: Verifying a program by splitting into smaller chunks.
3. `branch.ml`: Verifying a program that has a conditional branch.
4. `memory.ml`: Verifying a program that manipulates a memory.
5. `loop.ml`: Verifying a program that has a simple loop.
6. `bignum.ml`: Writing a specification of a program dealing with big numbers & proving it.

### Relational reasoning

Note that Arm tutorial has more examples in this topic.

1. `rel_simp.ml`: Proving equivalence of two simple programs.
2. `rel_equivtac.ml`: Proving equivalence of two programs that have small differences.
3. `rel_reordertac.ml`: Proving equivalence of two programs where the second one has instructions reordered from that of the first one.
