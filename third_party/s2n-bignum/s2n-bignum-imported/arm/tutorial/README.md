# Tutorials for s2n-bignum

This directory includes examples for verifying Arm programs using s2n-bignum
and HOL Light.
To verify programs in x86, see `x86/tutorial`.

### Unary reasoning

1. `simple.ml`: Verifying a simple arithmetic property of a linear program.
2. `sequence.ml`: Verifying a program by splitting into smaller chunks.
3. `branch.ml`: Verifying a program that has a conditional branch.
4. `memory.ml`: Verifying a program that manipulates a memory.
5. `loop.ml`: Verifying a program that has a simple loop.
6. `bignum.ml`: Writing a specification of a program dealing with big numbers & proving it.
7. `rodata.ml`: Reading data from the read-only section.

### Relational reasoning

1. `rel_simp.ml`: Proving equivalence of two simple programs.
2. `rel_equivtac.ml`: Proving equivalence of two programs that have small differences.
3. `rel_reordertac.ml`: Proving equivalence of two programs where the second one has instructions reordered from that of the first one.
4. `rel_loop.ml`: Proving equivalence of two simple loops.
5. `rel_veceq.ml`: Proving equivalence of scalar vs. vectorized 128x128->256-bit squaring.
