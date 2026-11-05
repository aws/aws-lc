# s2n-bignum PR Review Checklist

## Type 0: Common Checks (All PR Types)

- [ ] **Cross-platform build**
  - [ ] `make` in both `arm/` and `x86/` on both ARM and x86 machines
  - [ ] Also try on macOS (different assembler — e.g., `objdump` may print instruction names slightly differently, which can trip up the textual checks that verify simulator coverage matches the code)
  - [ ] Verify no errors from assembler differences across platforms

## Type 1: Adding a New Instruction

- [ ] **Instruction decoding** (`decode.ml`)
  - [ ] Eyeball the bit pattern against the ARM/x86 manual
  - [ ] Verify bit fields (Q bit, RM, immediates, etc.) correspond to the manual
  - [ ] Note: s2n-bignum may express things differently than the manual (e.g., explicit subwords vs bit masks), but they should be equivalent
  - [ ] Check that the new bit pattern is disjoint from all existing patterns — the HOL Light match construct uses first-to-last order, but the evaluation machinery requires disjointness, and overlapping patterns could silently shadow existing instructions
  - [ ] Watch for ARM instructions where a zero immediate field changes the instruction entirely (e.g., becomes a MOVI instruction) — this makes patterns more verbose but is necessary for disjointness

- [ ] **Instruction semantics** (`instruction.ml` for ARM, also `x86.ml` for x86)
  - [ ] Verify the core instruction semantics match what you'd expect from the manual
  - [ ] Note: ARM has complete executable specs in the manual, but they can be very low-level/idiomatic — use judgement when comparing against the HOL Light model
  - [ ] Most encodings are analogous to existing instructions, so check for a similar existing instruction as a reference

- [ ] **Simulator entry** (`simulator_iclasses`)
  - [ ] New instruction has a simulator entry
  - [ ] For ARM: check the bit pattern with `X`s (random bits) is present
  - [ ] For x86: the situation is more complex — there are three classes of simulator entries:
    1. **Register-to-register** (`iclasses_reg`): mix of auto-generated (grepped from sources) and manually added entries
    2. **Full memory harnesses**: comprehensive memory operand testing with various address forms (base+displacement, RSP-relative, etc.) — written by Yan, this is the gold standard
    3. **Simple memory backup**: auto-converted from code-used instructions with memory operand simplified to `[RSP+32]` — ensures every memory instruction gets at least one sanity check
  - [ ] If adding an instruction not yet used in code, add manual entries to the register-register list
  - [ ] For x86 instructions with memory forms: add entries to at least the simple memory backup list, ideally the full memory harness — memory vs register can differ subtly (e.g., zero extension behavior)
  - [ ] In the worst case for x86, you may need to add to 2-3 different lists
  - [ ] Memory harness addresses must fit within the 256-byte buffer at RSP (RSP to RSP+256) that the simulator allocates
  - [ ] Consider adding corner cases not exercised by existing code (e.g., out-of-range immediates, memory operand variants, both 32-bit and 64-bit argument forms, different register names)
  - [ ] With Claude available, it should become the norm to write fuller harnesses for new instructions

- [ ] **Run focused simulation**
  - [ ] Temporarily trim `iclasses` to only the new instructions (delete all other entries from the auto-generated and manual lists)
  - [ ] Run `make sematest` (under the architecture folder, e.g. `cd arm`) to heavily exercise just the new instructions
  - [ ] This applies more when making the PR than reviewing — by review time, it's likely correct
  - [ ] For debugging failures: you can run the simulator interactively in HOL Light instead of using `make sematest`:
    ```
    loadt "x86/proofs/simulator.ml";;
    ```
    This lets you trace through code, inspect failing goal states, and see what the simulator expected vs. what it got

## Type 2: Adding a New Function

- [ ] **Makefile entries**
  - [ ] Entry in the main Makefile (`arm/Makefile` and/or `x86/Makefile`)
  - [ ] For x86: also entry in `x86_att/Makefile`
  - [ ] Note: subdirectory mini-Makefiles (e.g., `p256/Makefile`) exist but are poorly maintained and not used by consumers — don't worry about updating those

- [ ] **Assembly source** (`.S` file in appropriate subdirectory)
  - [ ] Standardized comment banner at the top with:
    - [ ] Copyright boilerplate
    - [ ] One-line summary (also reproduced in header file)
    - [ ] Input/output description
    - [ ] C prototype
    - [ ] Register-to-argument mapping (standard ABI; for x86, both standard and Windows/Microsoft x64 ABI) — watch for copy-paste errors where argument names don't match the prototype
    - [ ] Longer explanation of what the function does (if non-trivial)
  - [ ] The comment banner format is used programmatically (e.g., for generating constant-time proofs), so follow the standardized style closely
  - [ ] Compare with analogous existing functions for consistency
  - [ ] **CFI directives**: use CFI-decorated macros (e.g., `CFI_PUSH` instead of raw `push`) for stack pointer modifications and callee-saved register save/restore — these don't affect object bytes or verification but support debugging/tracing/profiling
  - [ ] Comments in the assembly are encouraged where feasible — SLOTHY-optimized code won't have them, but should reference the pre-SLOTHY original; hand-written code should explain the algorithm
  - [ ] Indentation is traditionally 8 characters, but not strictly enforced

- [ ] **x86-specific: AT&T syntax** (`x86_att/` directory)
  - [ ] Run `cd x86_att && make clobber && make`
  - [ ] Verify no errors (the `sed`-based conversion script `atrophy` is brittle — new syntactic forms like 4-operand instructions may need script updates)
  - [ ] Verify `git diff` shows no changes (AT&T version is up to date)
  - [ ] This matters because AT&T forms are what AWS-LC imports

- [ ] **Header files**
  - [ ] `include/s2n-bignum.h` updated with the new function prototype (one-line description + `extern` prototype)
  - [ ] C89 variant header updated — run `cd include && make clobber && make` to regenerate and verify consistency (the C89 version strips C99 features like `static` array size qualifiers)

- [ ] **Tests** (`tests/test.c`)
  - [ ] New function has test entries
  - [ ] Tests are doing something sensible, not trivially succeeding
  - [ ] Function appears in the test list (preferably alphabetical order; architecture-specific functions may be in a separate list)
  - [ ] Can run all tests: `cd tests && make go`
  - [ ] Can test individual function: `./tests/s2nbignum_test bignum_mul_p256` with optional iteration count

- [ ] **Benchmarks** (`benchmarks/benchmark.c`)
  - [ ] New function has a benchmark entry (usually 2-3 lines, copy from similar function)
  - [ ] Can run all benchmarks: `cd benchmarks && make go` (takes a few minutes)
  - [ ] Can benchmark individual function: `./benchmarks/s2nbignum_benchmark bignum_mul_p256`

- [ ] **Proof** (`proofs/` directory)
  - [ ] Proof file exists for the new function (`.ml` file)
  - [ ] Run `make <function_name>.correct` to verify the individual proof succeeds
  - [ ] Visually inspect the specification/theorem — this is the most important review step:
    - [ ] Are the assumptions reasonable and not too strong?
    - [ ] Is the conclusion strong enough?
    - [ ] Does it match documentation and expectations?
    - [ ] The prover's soundness gives leverage: if the spec and model are right, the proof is almost certainly correct

- [ ] **Specifications list** (`specifications.txt`)
  - [ ] All subroutine correctness theorems listed
  - [ ] Entries in strict alphabetical order (the `make proofs` target sorts and compares — non-alphabetical entries will fail)
  - [ ] For ARM: 1 variant per function (BTI variants may come in the future)
  - [ ] For x86: 4 variants per function (standard ABI, Windows ABI, with/without `endbr64`)
  - [ ] This file is intentionally manual as a human sanity check ("I expect to see a correctness proof for this")

- [ ] **Subroutine signatures** (`collect_signatures.py`)
  - [ ] Updated if needed (especially for constant-time safety properties)
  - [ ] If function exists only on one architecture, may need an "only arm" or "only x86" annotation
  - [ ] Auto-generated by the Python script — signatures are used for generating constant-time specs

- [ ] **Full proof run** (optional but recommended)
  - [ ] `make -j 90 proofs` in both `arm/` and `x86/` on a large machine
  - [ ] Verify the `specifications.txt` check passes
  - [ ] This now also runs in CI, so individual runs are less critical but still recommended if you have access to big machines

## Type 3: Adding a New Specification

- [ ] **Specification style**
  - [ ] Top-level specification should be as abstract and mathematical as possible — avoid code-like pseudocode that mirrors the implementation
  - [ ] Specification states an implication (model implies spec), not necessarily an equivalence — it's OK for the spec to leave some aspects undetermined (e.g., Jacobian representation choice)
  - [ ] Keeping the spec stylistically different from the code reduces common-mode errors (same mistake in both spec and implementation)
  - [ ] For functions that are inherently non-mathematical (AES, SHA-3, Keccak round constants), accept that the spec will resemble code — but validate more aggressively (see below)

- [ ] **Layered specifications**
  - [ ] Consider multiple specification levels: a low-level (close to code) spec, a medium-level spec, and a high-level mathematical spec
  - [ ] Prove implications between layers (low implies medium implies high)
  - [ ] The low-level spec can track a standards document (e.g., NIST pseudocode); the high-level spec captures the mathematical essence

- [ ] **Spec validation (closing "gap A")**
  - [ ] For mathematical specs (bignum arithmetic, elliptic curves, GHASH polynomial math): the spec is short and abstract enough to inspect by eye — low risk
  - [ ] For code-like specs (AES, SHA, symmetric crypto round functions): higher risk of spec bugs — apply additional validation:
    - [ ] Run known-answer tests / test vectors against the specification (make the spec executable or prove equivalence to an executable form)
    - [ ] Compare against specifications in other formal systems (Cryptol, Isabelle/HOL, Coq, Lean, ACL2) — look for structural similarities and flag disparities
    - [ ] Cross-check with the authoritative standards document (NIST FIPS, RFC) — have a human verify the correspondence, not just an LLM (to avoid common-mode LLM errors)
  - [ ] For byte-level concerns: verify byte ordering, endianness, and encoding conventions match the standard (e.g., GHASH bit-reversal per NIST SP 800-38D)

- [ ] **Executability considerations (for abstract/mathematical specs)**
  - [ ] Abstract mathematical specs may not be directly executable — that's acceptable, but requires compensating validation
  - [ ] If the spec is not executable, ensure there is a proven-equivalent executable form or test vectors that validate the proof chain end-to-end
  - [ ] For under-determined specs using existential quantifiers (output is "some value such that ..."), verify the spec is satisfiable — i.e., a valid output exists for all valid inputs
  - [ ] Note: code-like specs (AES, SHA) are inherently executable and testable — this tradeoff does not apply to them

- [ ] **Relationship to standards documents**
  - [ ] Identify the authoritative informal spec (RFC, NIST FIPS, original paper)
  - [ ] Document which document and section the formal spec corresponds to
  - [ ] If the informal spec uses pseudocode, prefer formalizing the mathematical intent rather than transliterating the pseudocode
  - [ ] Watch for implicit behaviors buried in pseudocode (e.g., X25519 returning 0 for input 0 is implicit in the Fermat inverse, not stated explicitly)
