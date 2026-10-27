# Program Equivalence Proofs in s2n-bignum

## 1. Introduction

This file explains how program equivalence proofs are written for correctness of
NIST curves in s2n-bignum as well as the optimized Montgomery reduction algorithm.
The theoretical foundation for these proofs is the relational Hoare logic `L2`
described in Mazzucato et al., *"Relational Hoare Logic for Realistically Modelled
Machine Code"* ([arXiv 2505.14348](https://arxiv.org/abs/2505.14348), CAV'25)

The [`arm/tutorial/`](https://github.com/awslabs/s2n-bignum/tree/main/arm/tutorial)
directory has a few small examples starting with `rel_`. The `x86/tutorial`
directory also has a few, but Arm has more because program equivalence has been
more extensively used in Arm's NEON vectorization proofs targeting Graviton2.

## 2. Program Equivalence of Field Operations

There are several proofs of linear optimizations for the field operations of the
P-256/384/521 elliptic curves:

- [`arm/proofs/bignum_montmul_p256.ml`](../arm/proofs/bignum_montmul_p256.ml),
  [`bignum_montmul_p384.ml`](../arm/proofs/bignum_montmul_p384.ml),
  [`bignum_montmul_p521.ml`](../arm/proofs/bignum_montmul_p521.ml),
- corresponding `bignum_montsqr_*` files,
- [`bignum_mul_p521.ml`](../arm/proofs/bignum_mul_p521.ml) and
  [`bignum_sqr_p521.ml`](../arm/proofs/bignum_sqr_p521.ml).

Each of these composes (1) NEON vectorization followed by (2) SLOTHY instruction
reordering. Each step proves a separate `ensures2` equivalence theorem; the two are
then composed into a single scalar↔optimized equivalence; and the composed
equivalence is combined with the pre-existing `ensures`-style functional correctness
of the scalar reference to yield functional correctness of the optimized program.

We use `bignum_montmul_p256` as the running example and call out P384/P521
differences in passing. All name references below are from
[`arm/proofs/bignum_montmul_p256.ml`](../arm/proofs/bignum_montmul_p256.ml) unless
noted otherwise.

### 2.1 The three machine-code versions

Three versions of the routine coexist in the proof script:

| variable | role | source |
|---|---|---|
| `bignum_montmul_p256_unopt_mc` | original, scalar reference | `arm/p256/unopt/bignum_montmul_p256_base.o` |
| `bignum_montmul_p256_interm1_mc` | NEON-vectorized intermediate | inline opcode list in the `.ml` proof script |
| `bignum_montmul_p256_mc` | final, NEON + SLOTHY-scheduled | `arm/p256/bignum_montmul_p256.o` |

Each is stripped of function prologue/epilogue into a `_core_mc` slice (`bignum_montmul_p256_unopt_core_mc`,
`bignum_montmul_p256_interm1_core_mc`, `bignum_montmul_p256_core_mc`) used by the
`ensures2` statements.

### 2.2 State equivalence relations

Because the two programs manipulate the same scalar-level *input* and need to produce
the same scalar-level *output*, the input and output state relations are both small:

```
montmul_p256_eqin (s1,s1') x y z ⇔
   C_ARGUMENTS [z; x; y] s1 ∧ C_ARGUMENTS [z; x; y] s1' ∧
   (∃a. bignum_from_memory (x,4) s1 = a ∧ bignum_from_memory (x,4) s1' = a) ∧
   (∃b. bignum_from_memory (y,4) s1 = b ∧ bignum_from_memory (y,4) s1' = b)

montmul_p256_eqout (s1,s1') z ⇔
   ∃a. bignum_from_memory (z,4) s1 = a ∧ bignum_from_memory (z,4) s1' = a
```

Three points are worth noting.

1. **Pointers are concrete and equal** — `C_ARGUMENTS [z; x; y]` pins both states to
   the same caller-provided addresses (and register assignments via the AArch64 ABI).
2. **Memory contents are abstract and equal** — we say "there exists `a` such that
   both sides read `a` at `(x,4)`", rather than naming `a`. Existential quantification
   over `a, b` is the canonical way to state "the two states happen to agree on this
   memory", and it scales to the output relation without plumbing the actual modular
   value through the equivalence proof.
3. **No other components are constrained by `eqin`/`eqout`.** Their free variation
   is also encoded instead in the *frame* (`MAYCHANGE`) clauses of each `ensures2` goal
   which will be explained later (e.g. `equiv_goal1` and `equiv_goal2` in the proof script).
   The equivalence only ever asserts the scalar result deposited at `(z,4)` is the same on both
   sides, and both sides are free to scribble on e.g., SIMD regs in any way they like.

The *same* `eqin`/`eqout` pair is reused for both the scalar↔NEON and NEON↔SLOTHY
equivalences — a nontrivial fact that only works because the NEON intermediate
happens to agree with both the scalar reference *and* the SLOTHY-scheduled output on
the value deposited at `(z,4)`, despite the vast differences in their traces.

**Building the full `ensures2` spec (`equiv_goal` term).** Each `equiv_goal1` / `equiv_goal2` is
constructed by the helper `mk_equiv_statement` (in `arm/proofs/equiv.ml`) —
this is the standard way to produce an `ensures2` goal in s2n-bignum. It
takes the following arguments:

- A side-condition assumption (typically `nonoverlapping (…)` clauses);
- The input and output state relations `eqin` / `eqout`;
- The two executables, each together with its PC offset range
  `(pc_ofs, pc_ofs_to)` identifying the slice of code to relate;
- The two `MAYCHANGE` frames, one per side;
- Two step-count functions, one per side.

It assembles the universally quantified `ensures2` term with the expected
`aligned_bytes_loaded` / `read PC` boilerplate already in place.

The convenience wrapper `mk_equiv_statement_simple` covers
the common case of "the whole of each `_mc`, start to end" without requiring
explicit PC offsets. The same helpers are used everywhere an `ensures2` goal
is built in the rest of this document.

### 2.3 Proving the two equivalences

```
BIGNUM_MONTMUL_P256_CORE_EQUIV1   -- unopt_core  ↔  interm1_core
BIGNUM_MONTMUL_P256_CORE_EQUIV2   -- interm1_core ↔  core (SLOTHY)
```

For each of the two optimizations there exists a proof whose definition is
`prove(equiv_goal, …)`. Their theorem statements are almost the same, but their
proofs use very different tactics.

**Scalar ↔ NEON (`EQUIV1`).** After `EQUIV_INITIATE_TAC montmul_p256_eqin` unfolds
the input relation, the main work is done by

```
EQUIV_STEPS_TAC actions
    BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
    BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC
```

`EQUIV_STEPS_TAC` traverses an `actions : (string * int * int * int * int) list`
describing per-range correspondences between the two programs:

- `"equal"` ranges run as *lock-step* symbolic simulation — one step on each side,
  both instructions produce the same symbolic output, and the common value is
  immediately abbreviated by a fresh variable to prevent expression blow-up.
- `"replace"`, `"insert"`, `"delete"` ranges run *stuttering* simulation — one side
  advances while the other does nothing (or vice versa), and the resulting output
  expressions are matched up by rewriting.

The hard case for NEON↔scalar is the `"replace"` one: a single vector instruction
computes the same 64-bit word as a group of scalar `mul`/`umulh`/carry-chain
instructions, but their *syntactic* symbolic expressions look nothing alike. This is
where *user-registered bit-vector equality theorems* come in. The proof script
temporarily extends `extra_word_CONV`:

```ocaml
let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI]]
  @ (!extra_word_CONV);;
```

and restores it after the `EQUIV1` proof. `WORD_MUL64_LO`/`WORD_MUL64_HI` (in
[`arm/proofs/neon_helper.ml`](../arm/proofs/neon_helper.ml)) rewrite the NEON compound-
multiplication idiom (sequences of `UMULL`/`UZP`/`USRA`/`UMLAL` computing
`mul_lo`/`mul_hi` of two 64-bit lanes) into the corresponding scalar `MUL`/`UMULH`
outputs. `WORD_BITMANIP_SIMP_LEMMAS` cleans up small bit-permutation helpers
(`xtn`, `uzp1`, `rev64`, …). Once these rewrites close the stutter-step, the tactic
converges and proceeds.

**NEON ↔ SLOTHY (`EQUIV2`).** Here the two programs contain *the same set of
instructions* in a permuted order. `EQUIV_STEPS_TAC` is not used; instead the proof
uses the two-phase tactic pair

```
ARM_N_STEPS_AND_ABBREV_TAC  BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC (1--N) state_to_abbrevs None
ARM_N_STEPS_AND_REWRITE_TAC BIGNUM_MONTMUL_P256_CORE_EXEC         (1--N) inst_map state_to_abbrevs None
```

The first tactic stuttering-simulates the left (`interm1`) program, abbreviating
each instruction's symbolic output and storing the mapping from state number to
abbreviation in the OCaml ref `state_to_abbrevs`. The second tactic then simulates
the right (SLOTHY) program one instruction at a time; at step `k` on the right it
looks up the abbreviation via `inst_map[k]` — the permutation from SLOTHY's schedule
back to original order — and discharges the step by equating the right output with
the stored abbreviation. `inst_map` is emitted by SLOTHY and pasted into the proof
script.

### 2.4 Horizontal composition

`BIGNUM_MONTMUL_P256_CORE_EQUIV` states `unopt_core ↔ core (SLOTHY)`. Its proof
is essentially a single call to `EQUIV_TRANS_TAC` — the tactic form of Lemma 4
(*frame-condition composition*) of the paper:

```
EQUIV_TRANS_TAC
  (BIGNUM_MONTMUL_P256_CORE_EQUIV1, BIGNUM_MONTMUL_P256_CORE_EQUIV2)
  (montmul_p256_eqin, montmul_p256_eqin, montmul_p256_eqin)
  montmul_p256_eqout_TRANS
  (…_UNOPT_CORE_EXEC, …_INTERM1_CORE_EXEC, …_CORE_EXEC)
```

The first argument pairs the two stage theorems; the second declares that the *same*
input relation bridges all three programs; the third is a trivial transitivity
lemma for `eqout` (`montmul_p256_eqout_TRANS`); the fourth supplies the three
executables. A preceding `SUBGOAL_THEN` existentially introduces the intermediate
program's load address `pc3` and discharges its `nonoverlapping` obligations via
`FIND_HOLE_TAC`; this intermediate `pc3` does not appear in the final specification.

**What is this `FIND_HOLE_TAC`?** To chain the two stage equivalences we
need a 64-bit address `pc3` at which the intermediate program (`interm1_mc`) can
be loaded such that `pc3` does not overlap any of the already-fixed regions —
the original program at `pc`, the SLOTHY program at `pc2`, the input/output
buffers at `x`, `y`, `z`, and so on. `FIND_HOLE_TAC` proves that such a `pc3`
exists by arithmetic on the given size bounds of all those regions: the total
occupied space has to be less than `2^64`, leaving a hole somewhere to slot the
intermediate program into.

This 'find an empty memory area to place the intermediate machine code' is also
the reason why `bignum_emontredc_8n_cdiff` carries the extra
`k < 2^32` criterion (where k is the number of words) in its precondition,
which didn't exist in `bignum_emontredc_8n`.
Without that bound, the input/output buffers alone would be allowed to be so large
that no hole of the intermediate program's size would be guaranteed to exist in
the remaining 64-bit address space, and `FIND_HOLE_TAC` would not go through.

### 2.5 Lifting the result to `ensures` on the optimized program

The composed equivalence alone is *not* yet a functional-correctness theorem for the
optimized program; it says "the optimized program produces the same output as the
scalar one *if* the scalar program produces some output at all". We need to bridge
it with an `ensures_n` fact about the scalar program. This is the content of
Appendix D of the paper.

**Step 1 — prove `eventually_n_at_pc` for the scalar core**
(`BIGNUM_MONTMUL_P256_EVENTUALLY_N_AT_PC`). The goal is stated against
`APPEND bignum_montmul_p256_unopt_core_mc barrier_inst_bytes` — the scalar code
followed by the *stopper* (a non-decodable 4-byte word). The stopper is essential:
it forces the number of steps to the terminal PC to be *unique*, which is exactly
the hypothesis of Lemma 6. The proof itself is mechanical, driven by
`PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC`. Note that
`PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC` only works when the program is
supposed to have a *constant* number of steps to finish — it cannot handle a
program containing a loop that iterates a symbolic `n` times, because it needs to
statically unroll every step. Routines with data-dependent loops (such as
`bignum_emontredc_8n_cdiff`'s main loop in §4) therefore require a different lifting
strategy.

**Step 2 — promote `ensures` to `ensures_n`**
(`BIGNUM_MONTMUL_P256_UNOPT_CORE_CORRECT_N`). One call to `prove_ensures_n`
combines the scalar `ensures` theorem with the `eventually_n_at_pc` lemma and emits
the `ensures_n` version mechanically (Lemma 6).

**Step 3 — combine equivalence with `ensures_n`**. The optimized-core correctness
theorem `BIGNUM_MONTMUL_P256_CORE_CORRECT` is proved with a single invocation of

```
PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTMUL_P256_CORE_EQUIV
    BIGNUM_MONTMUL_P256_UNOPT_CORE_CORRECT_N
    (BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC, BIGNUM_MONTMUL_P256_CORE_EXEC)
    (montmul_p256_eqin, montmul_p256_eqout)
```

The tactic instantiates the existentially quantified intermediate `pc` of the
scalar program (discharged by a `FIND_HOLE_TAC` just above) and applies the hybrid-
ensures theorem (Theorem 4 in the paper). Crucially, because `P`, `Q`, `R` appear
under existentials in that theorem, *the stopper condition disappears from the
final specification*: `BIGNUM_MONTMUL_P256_CORE_CORRECT` is a pure `ensures`
statement about `bignum_montmul_p256_core_mc`, with no trace of the barrier.

Wrapping the core theorem back into the subroutine form
(`BIGNUM_MONTMUL_P256_SUBROUTINE_CORRECT`) is then a routine application of
`ARM_ADD_RETURN_NOSTACK_TAC`.

**P384/P521.** The structure is identical. Same three-versions layout
(`…_unopt_core_mc`, `…_interm1_core_mc`, `…_core_mc`), same `eqin`/`eqout` (with
6-word and 9-word bignums respectively), same `EQUIV1`/`EQUIV2`/composed-`EQUIV`
names, same final `PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC`.

## 3. Program Equivalence of Point Operations

The proofs of [`p256_montjadd.ml`](../arm/proofs/p256_montjadd.ml) and
[`p384_montjadd.ml`](../arm/proofs/p384_montjadd.ml) follow the same master plan as §2
but at a much larger scale: the unoptimized routine makes several `bl` calls to
Montgomery multiplication/squaring subroutines and has significant redundancy across
those call boundaries, which is exploited by two *extra* optimizations:

1. **Function inlining.** Every `bl bignum_montmul_p256` etc. is expanded into the
   callee's body, the trailing `ret` is dropped, and the argument-setup code is
   merged with the callee's prologue.
2. **Redundant memory-access elimination.** Across the just-removed call boundary
   the optimizer identifies store/reload pairs that are bypassable (the value is
   still in a register) and deletes the memory access.

These are followed by NEON vectorization and SLOTHY scheduling of the individual
field operations.
Importantly, SLOTHY is only applied to the individual inlined field operations
(`bignum_montmul_p*`, `bignum_montsqr_p*`, `bignum_sub_p*`), *not* to the whole
inlined point-operation routine: running SLOTHY on the entire inlined body was
infeasible because SLOTHY's scheduling search did not converge in a reasonable time.

The optimizations themselves were produced by a custom (and ad-hoc) OCaml script,
but it is the `ensures2` equivalence proof that *verifies* the rewrites are
semantics-preserving.

### 3.1 Proving equivalence after the two optimizations in one shot

Unlike §2, only two machine-code definitions are introduced for each point
operation, because all rewrites above are bundled into a single monolithic
transformation in the final `.o`:

| variable | role |
|---|---|
| `p256_montjadd_unopt_mc` | original, with `bl` calls |
| `p256_montjadd_mc` | final: inlined + mem-elim |

Note that the two optimizations that this single `EQUIV_STEPS_TAC` actually
has to verify are only (1) function inlining and (2) redundant memory-access
elimination. The NEON vectorization and SLOTHY scheduling have already been
applied, and separately verified, at the level of the inlined field operations
(`BIGNUM_MONTSQR_P256_CORE_CORRECT`, `BIGNUM_MONTSQR_P256_CORE_CORRECT`, …, from §2);
what gets inlined into the point-op body.

The `actions` argument consumed by the main `EQUIV_STEPS_TAC` invocation is
assembled progressively to match this decomposition. Each individual rewrite
contributes its own action list (`"call montsqr_p256"`, `"call montmul_p256"`,
`"call sub_p256"`, identity `"equal"` blocks, `"replace"`/`"insert"`/`"delete"`
for mem-elim), and the `merge_actions` helper in
[`arm/proofs/utils/p256_montjadd_params.ml`](../arm/proofs/utils/p256_montjadd_params.ml)
composes them into a single `actions_merged` list that is passed to the main
equivalence proof.

### 3.2 Input / output relation

`p256_montjadd_eqin` again puts the three operand pointers in `C_ARGUMENTS` and
requires SP to match, then asks the 12-word Jacobian points at `p1` and `p2` to be
abstract-and-equal. `p256_montjadd_eqout` is carefully split into *three* 4-word
reads at offsets 0, 32, 64 of `p3` — one per projective coordinate (x, y, z).
Splitting this way makes the final postcondition easier to discharge because each
coordinate gets its own existential `a0`/`a1`/`a2`.

### 3.3 For faster symbolic simulation: dead-value information and caching tricks

The core equivalence `P256_MONTJADD_EQUIV` uses `EQUIV_STEPS_TAC` as in §2.3, but
its arguments are much richer:

```
EQUIV_STEPS_TAC
    ~dead_value_info_left:p256_montjadd_unopt_dead_value_info
    ~dead_value_info_right:p256_montjadd_dead_value_info
    actions_merged P256_MONTJADD_UNOPT_CORE_EXEC P256_MONTJADD_EXEC
```

Two things to notice.

- `dead_value_info_left`/`right` are *precomputed per-instruction liveness
  annotations*. At each step, the symbolic simulator is told which registers and
  memory locations are *dead* (not used on any path to the terminal PC). Dead
  values are allowed to differ across the two states, which is what licenses the
  removal of redundant stores: after the optimizer deletes a store, the right-hand
  memory cell holds stale data while the left-hand one holds the freshly written
  value — but since the cell is dead from that point, the simulator doesn't need
  to reconcile the two. Without `dead_value_info`, redundant-store elimination
  would induce spurious proof obligations that never close.
- A global result-cache ref `orthogonal_components_conv_custom_cache` is installed
  before `P256_MONTJADD_EQUIV` and reset after it. It short-circuits expensive
  component-orthogonality checks (the ones that decide whether two memory writes
  can safely commute) by caching `(state-component, state-component)` results
  across the whole symbolic simulation. Empirically this brings roughly a 20%
  speedup on the point-op equivalence proofs.

### 3.4 End-to-end correctness

Same recipe as §2.5, just with a slightly different closing tactic:

```
VCGEN_EQUIV_TAC P256_MONTJADD_EQUIV P256_MONTJADD_UNOPT_CORE_CORRECT_N
  [fst P256_MONTJADD_UNOPT_CORE_EXEC; fst P256_MONTJADD_EXEC]
```

`VCGEN_EQUIV_TAC` (in [`arm/proofs/equiv.ml`](../arm/proofs/equiv.ml)) is a slightly
heavier cousin of `PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC`: it exposes three
remaining subgoals (precondition, postcondition, frame) that the caller then
discharges, instead of packaging them behind a canned pattern. For the point
operations the precondition subgoal in particular requires custom work because the
input-state relation mentions SP and a 224-byte stack scratch area, which
`PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC`'s canned strategy cannot anticipate.

[`p384_montjadd.ml`](../arm/proofs/p384_montjadd.ml) follows exactly the same pattern
with a different register set and 6×3-word Jacobian coordinates.

## 4. Program Equivalence of `bignum_emontredc_8n_cdiff`

`bignum_emontredc_8n_cdiff` is the extended Montgomery reduction of an arbitrary
bignum, used inside bignum modular multiplication. Compared to the existing
[`bignum_emontredc_8n`](../arm/proofs/bignum_emontredc_8n.ml), the `_cdiff` variant
adds:

1. **NEON vectorization** of the expensive `MUL`/`UMULH` quartets in both the outer-
   loop prologue and the inner add-multiply loop (this is what `bignum_emontredc_8n_neon`
   already achieves, but the `_cdiff` variant folds it in too).
2. **SLOTHY instruction reordering + software pipelining** of every basic block.
   The software pipelining hoists work for iteration `i+1` up into iteration
   `i`.
3. **Cached multiplied differences** — an ADK-style trick: pairwise differences of
   the four-word outer-loop-iteration bignum digits are computed once and reused
   by the inner loop, avoiding redundant subtractions. (This is what the `_cdiff`
   suffix stands for; see §4.1 for details.)

The software-pipelining part of (2) is new relative to §2 and §3: it requires
rotating the inner loop, which in turn forces us to introduce an extra
intermediate program beyond the plain scalar/NEON/SLOTHY stack. The
equivalence proof for the pipelined loop is not attempted in one shot; instead
§4.2 below will decompose it into a chain of smaller equivalences -
(1) partitioning the loop body into two smaller parts `[A; B]`,
(2) rotating the loop into `A; [B; A]; B`, and
(3) finally applying instruction reordering to the instructions in basic blocks
`A`, `[B; A]` and `B` separately.

The proof is in
[`arm/proofs/bignum_emontredc_8n_cdiff.ml`](../arm/proofs/bignum_emontredc_8n_cdiff.ml).
All name references in this section are from that file unless noted.

### 4.1 Where are the cached multiplied differences computed?

Computing the cached differences is done by a *precomputation loop* placed at the
very entry of the optimized routine. The loop walks over the modulus words
and fills a dedicated `m_precalc` buffer with pairwise absolute differences and
their sign bits, following the recursive definition

```
get_m_precalc n 0                   = 0
get_m_precalc n (i_div_4 + 1)       = get_m_precalc n i_div_4
                                    + 2 EXP (64 * 12 * i_div_4)
                                    * bignum_of_wordlist (precalc_diffs n (i_div_4+1))
```

(`get_m_precalc`, `precalc_diffs`). The precomputation-loop correctness lemma
`BIGNUM_EMONTREDC_8N_CDIFF_PRECALCLOOP` says exactly that, after executing this
entry block, `m_precalc` holds `get_m_precalc m (k DIV 4 − 1)`.

Because the original `bignum_emontredc_8n` has no such precomputation step, the
equivalence between original and optimized is necessarily conditional — the
`eqin` state relation of the main-loop equivalence assumes that the `m_precalc`
buffer is already populated with the cdiff content when the main loop is entered.
The unconditional top-level correctness of the optimized routine is then
recovered by sequentially composing `BIGNUM_EMONTREDC_8N_CDIFF_PRECALCLOOP`
(which establishes this assumption) with the main-loop equivalence (which
consumes it).

### 4.2 Basic-block decomposition

Each outer-loop body is split into three basic blocks, named uniformly via
`bignum_emontredc_8n_labels`, `outerloop_step{1,2,3}_labels`, and
`bignum_emontredc_8n_cdiff_labels`:

```
[ outerloop-prologue ]  →  [ maddloop inner loop ]  →  [ inner_loop_postamble ]
```

The outerloop prologue is the setup that runs once per outer iteration (loading
the four-word chunk of `z`, computing the Montgomery words, kicking off the inner
loop); the `maddloop` is the inner word-multiply-accumulate loop proper; the
`inner_loop_postamble` is the epilogue that absorbs the carry into the tail of
`z` and decrements the outer-loop counter.

### 4.3 Five programs, one per stage

All intermediate programs encode only the body of the outer loop plus its inner
maddloop plus its inner-loop postamble — i.e. one iteration of the outer loop.

| name in the file | role |
|---|---|
| `bignum_emontredc_8n_mc` (step 0 / "original") | unoptimized scalar reference, from `unopt/bignum_emontredc_8n_base.o` |
| `outerloop_step1_mc` (step 1) | NEON-vectorized outer-loop body; nothing else changed |
| `outerloop_step2_mc` (step 2) | step 1 with inner-loop instructions reordered so that instructions that are to be pipelined sits at the top of the basic block |
| `outerloop_step3_mc` (step 3) | step 2 with the inner loop rotated: a `maddloop_prologue` precedes the body and an epilogue (`inner_loop_postamble_noepilogue`) trails it |
| `bignum_emontredc_8n_cdiff_mc` (step 4 / final) | individual basic blocks SLOTHY-reordered, from `arm/fastmul/bignum_emontredc_8n_cdiff.o` |

An auxiliary `maddloop_step2_x30_mc` is used to bridge step 1 and step 2 — it
is step 2's inner loop with the `x30` base register re-based, so that the
address-register abbreviations computed on step 1 can be textually matched against
step 2.


Control-flow-graph-wise, each of the five versions of the outer loop has the
following shape. Rectangular nodes are basic blocks; arrows are control transfers;
the back-edge on `maddloop` is the inner loop's own back-edge, and the back-edge
on `inner_loop_postamble` is the outer loop's.

`<A>` and `<B>` label the two halves of step 1's maddloop body: `<A>` is the
prefix of instructions that step 3 peels out into `maddloop_prologue` (and,
starting from step 2, gets reordered to the top of the basic block), and
`<B>` is the remaining suffix that step 3 peels out into
`inner_loop_postamble_noepilogue`. In the real code, `<A>` corresponds roughly
to the first ~44 instructions of the 149-instruction body (the NEON
`ldr q …`/`xtn`/`umull`/… setup for iteration `i+1`'s next `m` word), and
`<B>` corresponds to the rest (the multiply-accumulate chain that consumes the
values loaded in `<A>`).

```
original (step 0)    step 1 (NEON)             step 2             step 3 (rotate)  step 4 (SLOTHY final)
                                         (reorder maddloop)
================     ================     ================      ==================     ================
 ┌──────────────┐     ┌──────────────┐     ┌──────────────┐      ┌──────────────┐      ┌──────────────┐
 │ outerloop    │     │ outerloop    │     │ outerloop    │      │ outerloop    │      │ outerloop    │
 │ prologue     │     │ prologue     │     │ prologue     │      │ prologue     │      │ prologue     │
 │ (scalar)     │     │ (NEON)       │     │ (NEON,       │      │ (NEON, + one │      │ (SLOTHY-     │
 │              │     │              │     │  identical   │      │ extra x27-=1 │      │ scheduled)   │
 │              │     │              │     │  to step 1)  │      │ for rotation)│      │              │
 └──────┬───────┘     └──────┬───────┘     └──────┬───────┘      └──────┬───────┘      └──────┬───────┘
        │                    │                    │                     │                     │
        │                    │                    │                     v                     v
        │                    │                    │              ┌──────────────┐      ┌──────────────┐
        │                    │                    │              │ maddloop_    │      │ maddloop_    │
        │                    │                    │              │ prologue     │      │ prologue     │
        │                    │                    │              │     <A>      │      │ (SLOTHY-     │
        │                    │                    │              │              │      │ scheduled)   │
        │                    │                    │              └──────┬───────┘      └──────┬───────┘
        v                    v                    v                     v                     v
 ┌──────────────┐     ┌──────────────┐     ┌──────────────┐      ┌──────────────┐      ┌──────────────┐
 │ maddloop     │     │ maddloop_    │     │ maddloop_    │      │ maddloop_    │      │ maddloop_    │
 │ (scalar,     │<┐   │ neon (NEON,  │<┐   │ neon         │<┐    │ neon         │<┐    │ neon         │<┐
 │ k/4−1 iters) │ │   │ k/4−1 iters) │ │   │      <A>     │ │    │     <B>      │ │    │ (SLOTHY-     │ │
 │              │ │   │              │ │   │--------------│ │    |--------------│ │    │ scheduled,   │ │
 │              │ │   │              │ │   │      <B>     │ │    │     <A>      │ │    │ k/4−2 iters) │ │
 │              │─┘   │              │─┘   │              │─┘    │ (k/4−2 iters)│─┘    │              │─┘
 └──────┬───────┘     └──────┬───────┘     └──────┬───────┘      └──────┬───────┘      └──────┬───────┘
        │                    │                    │                     │                     │
        │                    │                    │                     v                     v
        │                    │                    │              ┌──────────────┐      ┌──────────────┐
        │                    │                    │              │ inner_loop_  │      │ inner_loop_  │
        │                    │                    │              │ postamble_   │      │ postamble_   │
        │                    │                    │              │ noepilogue   │      │ noepilogue   │
        │                    │                    │              │      <B>     │      │ (SLOTHY-     │
        │                    │                    │              │              │      │ scheduled)   │
        │                    │                    │              └──────┬───────┘      └──────┬───────┘
        v                    v                    v                     v                     v
 ┌──────────────┐     ┌──────────────┐     ┌──────────────┐      ┌──────────────┐      ┌──────────────┐
 │ inner_loop_  │     │ inner_loop_  │     │ inner_loop_  │      │ inner_loop_  │      │ inner_loop_  │
 │ postamble    │     │ postamble    │     │ postamble    │      │ postamble    │      │ postamble    │
 │ (scalar)     │     │ (NEON)       │     │ (NEON)       │      │              │      │ (SLOTHY-     │
 │              │     │              │     │              │      │              │      │ scheduled)   │
 │              │     │              │     │              │      │              │      │              │
 └──────────────┘     └──────────────┘     └──────────────┘      └──────────────┘      └──────────────┘
        │                    │                    │                     │                     │
        v                    v                    v                     v                     v
     (outer)              (outer)             (outer)               (outer)               (outer)
```

For each pair of adjacent steps, **three per-block equivalences** are proved and
then **vertically composed** (by `prove_equiv_seq_composition`, i.e. Lemma 3 of the
paper) into one `OUTERLOOP_FULL_STEP{i}_STEP{i+1}_EQUIV`. Then the four
`OUTERLOOP_FULL_*` lemmas are **horizontally composed** (by `EQUIV_TRANS_GEN_TAC`,
Lemma 4) into `OUTERLOOP_FULL_EQUIV`. Finally the outer-loop back-edge is wrapped
by `ENSURES2_WHILE_PAUP_TAC` to yield `MAINLOOP_EQUIV`.

### 4.4 Per-stage vertical equivalences

#### (a) Original ↔ Step 1 — NEON vectorization

| lemma | code compared (outerloop block ↔ step-1 block) |
|---|---|
| `OUTERLOOP_ORIGINAL_STEP1_EQUIV` | original `outerloop..maddloop` ↔ step1 prologue |
| `MADDLOOP_ORIGINAL_STEP1_EQUIV` | original `maddloop..madddone` ↔ step1 `maddloop_neon..inner_loop_postamble` |
| `INNER_LOOP_POSTAMBLE_ORIGINAL_STEP1_EQUIV` | original `madddone..outerloop_end` ↔ step1 `inner_loop_postamble..end` |
| `OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV` | sequential composition of the three above |

This stage is NEON vs. scalar, so the symbolic simulation relies on the same
`extra_word_CONV` hook as in §2.3. The `MADDLOOP_ORIGINAL_STEP1_EQUIV` proof saves
and restores `_org_extra_word_CONV` and temporarily registers `ITE_WORD_NOT_XOR`.
Because the two inner loops share an *identical iteration count* (`k/4 − 1`), this
stage uses `ENSURES2_WHILE_PAUP_TAC` with the obvious 1–1 body correspondence.

#### (b) Step 1 ↔ Step 2 — instruction reordering

Step 2 reshuffles instructions *within* the `maddloop_neon` basic block
to hide latencies, without crossing any basic-block boundary. The outer-
loop prologue and the `inner_loop_postamble` are byte-for-byte identical
to step 1's, the loop still iterates `k/4 − 1` times, and the maddloop
body is a true permutation of step 1's (with a few destination-register
renames to break false dependencies). See the worked example in §4.3
for a concrete illustration of what moves and what doesn't.

Because the two `maddloop_neon` bodies are a true permutation of the same
instruction sequence, the inner-loop equivalence is split via the auxiliary
program `maddloop_step2_x30_mc`:

| lemma | code compared |
|---|---|
| `OUTERLOOP_STEP1_STEP2_EQUIV` | outer-loop prologues (identical instructions) |
| `MADDLOOP_STEP1_STEP2_X30_EQUIV` | step1 maddloop ↔ `maddloop_step2_x30_mc` |
| `MADDLOOP_STEP2_X30_STEP2_EQUIV` | `maddloop_step2_x30_mc` ↔ step2 maddloop |
| `MADDLOOP_STEP1_STEP2_EQUIV` | horizontal composition of the two above |
| `INNER_LOOP_POSTAMBLE_STEP1_STEP2_EQUIV` | postambles (identical) |
| `OUTERLOOP_FULL_STEP1_STEP2_EQUIV` | sequential composition |

`MADDLOOP_STEP1_STEP2_EQUIV` recomposes the two half-stages using `EQUIV_TRANS_TAC`
— the same horizontal-composition tactic we saw in §2.4, but *inside* a single
stage. This is why the `_X30` auxiliary has to be introduced: without it, step 1's
and step 2's address-register usage does not align, and the symbolic abbreviations
cannot be cross-referenced.

The proofs of the "identical" blocks use `ARM_N_STEPS_AND_ABBREV_TAC` +
`ARM_N_STEPS_AND_REWRITE_TAC` with the identity permutation as `inst_map`, in the
style of §2.3's `EQUIV2`.

#### (c) Step 2 ↔ Step 3 — inner-loop rotation

The step 2's single `maddloop_neon` block is split in three
places to produce, in step 3, a prologue (`maddloop_prologue`) before
the loop, a loop body (iterating `k/4 − 2` times instead of
`k/4 − 1`), and an epilogue (`inner_loop_postamble_noepilogue`) after the
loop.

| lemma | code compared |
|---|---|
| `OUTERLOOP_STEP2_STEP3_EQUIV` | step2 prologue ↔ step3 prologue (identical instructions) |
| `PROLOG_STEP2_STEP3_EQUIV` | step2 `maddloop_neon..maddloop_rotated` ↔ step3 `maddloop_prologue..maddloop_neon`: "first-iteration work pulled out of the loop" |
| `MADDLOOP_STEP2_STEP3_EQUIV` | step2 `maddloop_rotated..maddloop_rotated` (k/4 − 2 iterations) ↔ step3 `maddloop_neon..inner_loop_postamble` |
| `EPILOG_STEP2_STEP3_EQUIV` | step2 final rotated-body copy ↔ step3 `inner_loop_postamble..inner_loop_postamble_noepilogue` |
| `INNER_LOOP_POSTAMBLE_STEP2_STEP3_EQUIV` | step2 postamble ↔ step3 postamble (identical) |
| `OUTERLOOP_FULL_STEP2_STEP3_EQUIV` | sequential composition: outerloop → prolog → rotated body → epilog → postamble |

Because the *number of loop iterations differs* between step 2 and step 3
(`k/4 − 1` on step 2, `k/4 − 2` on step 3), `ENSURES2_WHILE_PAUP_TAC` cannot use a
1–1 body correspondence; the "missing" first iteration becomes the prolog and
the "missing" last iteration becomes the epilog, both hoisted out into their own
`ensures2` lemmas and composed around the middle.

#### (d) Step 3 ↔ Step 4 — SLOTHY rescheduling

Same shape as §2.3's `EQUIV2`, but applied independently to each of the three
blocks:

| lemma | code compared |
|---|---|
| `OUTERLOOP_STEP3_STEP4_EQUIV` | step3 prologue ↔ final `outerloop..maddloop_neon` |
| `MADDLOOP_STEP3_STEP4_EQUIV` | step3 rotated maddloop ↔ final `maddloop_neon..inner_loop_postamble` |
| `INNER_LOOP_POSTAMBLE_STEP3_STEP4_EQUIV` | step3 postamble ↔ final `inner_loop_postamble..outerloop_end` |
| `OUTERLOOP_FULL_STEP3_STEP4_EQUIV` | sequential composition |

Each uses a hand-tuned `inst_map` emitted by SLOTHY, driving
`ARM_N_STEPS_AND_ABBREV_TAC` / `ARM_N_STEPS_AND_REWRITE_TAC`.

### 4.5 Preventing abbreviation of memory addresses and loop counter

Abbreviating a register that holds a
memory-access base address (e.g. `word_add z (word (8 * 4 * i))`) or a loop
counter (e.g. `word (k4 - (i + 1))`) would make subsequent symbolic simulation of
`ldr`/`str` unable to identify from which memory invariants values should be loaded.
To avoid the destructive abbreviations, the step-abbreviate/rewrite tactic pair
(`ARM_N_STEPS_AND_ABBREV_TAC` / `ARM_N_STEPS_AND_REWRITE_TAC`) takes two extra arguments,
`regs_no_abbrev_left` and `regs_no_abbrev_right`, that list per instruction
slot the registers whose symbolic expression must not be replaced by a fresh
variable.

Both lists are typically computed by `backward_taint_analysis` over each
program: starting from "sinks" (the base register of every load/store, plus
`X27`/`X0`/`X1`/`X2`/`SP`/`X30` at the block exit, which appear in the
postcondition) and walking the instruction stream backwards, it marks every
register that data-flow-feeds a sink. The two lists can differ because the
two programs have different schedules. The same mechanism is reused in
`MADDLOOP_STEP2_STEP3_EQUIV` and `MADDLOOP_STEP1_STEP2_X30_EQUIV`.

For `EQUIV_STEPS_TAC` (used in §2.3 and §3.3), the analogous escape hatch is
the `"replace"` action: a range marked `"replace"` skips the default
abbreviation and instead asks the tactic to close the stutter by rewriting
the two sides' symbolic outputs against each other, so any pointer or counter
expressions survive the range unaltered.

Manually writing the `"replace"` ranges by hand needs efforts however, and
the helper `break_equal_loads` (in `arm/proofs/equiv.ml`) post-processes an
`actions` list and converts every
contiguous run of `arm_LD*` instructions inside an `"equal"` range into a
`"replace"` range.

### 4.6 Horizontal composition across stages

The four `OUTERLOOP_FULL_STEP{i}_STEP{i+1}_EQUIV` lemmas have *different* input
state relations (each stage's `_eqin` is tailored to that stage) and slightly
different frame conditions. Before chaining them transitively, the proof performs
three kinds of bookkeeping:

- `add_Q29_to_precond` injects an additional `mk_equiv_regs [Q29]` into the
  precondition of the STEP1–STEP2, STEP2–STEP3 and STEP3–STEP4 equivs. This is
  needed because the original–STEP1 proof establishes Q29 as a specific constant
  (`word_join 0xffffffff 0xffffffff`) on the right-hand side, which subsequent
  stages expect.
- `extend_first_equiv_for_seq_composition` enriches each stage's input relation
  with register equalities that the *next* stage expects but this stage doesn't
  mention — this is where the `_EXT` suffix in names like
  `OUTERLOOP_FULL_STEP1_STEP2_EQUIV_EXT` comes from.
- Canonicalized `maychange_eq_thm`s rewrite each stage's MAYCHANGE set into a
  common form, without which Lemma 4 cannot line the stages up.

The three transitive composition steps are then:

```
OUTERLOOP_FULL_ORIGINAL_STEP2_EQUIV   -- original ↔ step2
OUTERLOOP_FULL_ORIGINAL_STEP3_EQUIV   -- original ↔ step3
OUTERLOOP_FULL_EQUIV                  -- original ↔ step4
```

each proved by a single `EQUIV_TRANS_GEN_TAC` invocation, with an `eqout_TRANS`
helper that propagates Q29 through the chain.

### 4.7 Adding the outer-loop backedge

`OUTERLOOP_FULL_EQUIV` concerns one iteration of the outer loop. To lift it to
the full main loop, `OUTERLOOP_FULL_EQUIV_EXT` specializes `z ↦ z + 32·i` and adds
frame equalities for `X28` and the counter memory; `MAINLOOP_EQUIV` then applies
`ENSURES2_WHILE_PAUP_TAC` to wrap the per-iteration equivalence into an equivalence
of the actual main loop between the labels `main..main_end` on both programs.

### 4.8 From equivalence to functional correctness

The pattern from §2.5 / §3.4 is reused, with one twist forced by the fact that
`bignum_emontredc_8n`'s main loop iterates a *symbolic* number of times (so
`PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC` from §2.5 is not applicable):

1. The functional correctness `BIGNUM_EMONTREDC_8N_MAINLOOP_ENSURES_N` is proved directly for the scalar
   main loop — the script does not re-derive it via `prove_ensures_n` from a
   pre-existing `ensures`-style theorem, because the main loop has a
   data-dependent iteration count. Instead, the `ensures_n` proof is written from
   scratch using symbolic-simulation tactics that track the step count through the
   loop. (This is what the header comment at the top of the file refers to as
   "step 1 of the proof structure".)
2. `BIGNUM_EMONTREDC_8N_CDIFF_MAINLOOP_CORRECT` combines the two via
   `VCGEN_EQUIV_TAC MAINLOOP_EQUIV BIGNUM_EMONTREDC_8N_MAINLOOP_ENSURES_N_NSTEP_REWRITTEN`,
   in the point-op style of §3.4.
3. `BIGNUM_EMONTREDC_8N_CDIFF_CORE_CORRECT` prepends the precomputation-loop
   correctness `BIGNUM_EMONTREDC_8N_CDIFF_PRECALCLOOP` (see §4.1) to obtain the
   full routine's spec: the conditional `eqin` precondition "`m_precalc` already
   holds `get_m_precalc m (k DIV 4 − 1)`" is discharged by the precomputation
   loop's output, yielding an unconditional correctness theorem. Finally
   `BIGNUM_EMONTREDC_8N_CDIFF_CORRECT` / `_SUBROUTINE_CORRECT` wrap the prologue/
   epilogue and ABI frame to yield the top-level subroutine correctness theorem.
