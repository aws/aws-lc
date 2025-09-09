## Arm Instruction Modeling

The s2n-bignum symbolic simulator contains models of AArch64 instructions. The instructions are modeled by need. Often when verifying new programs, new instructions need to be added to s2n-bignum. This is a tutorial for adding new AArch64 instructions.

The instruction modeling is composed of three basic steps: instruction decoding, instruction semantics modeling and instruction cosimulation test.

### Instruction Decoding

[Location: arm/proofs/decode.ml](proofs/decode.ml)

Given an instruction, which is represented as a 32-bit value (of type `int32`), the decoding step will dispatch the instruction to the corresponding semantic function. For example, the following code snippet shows how to bitmatch the SIMD vector `AND` instruction:

```
| [0:1; q; 0b001110001:9; Rm:5; 0b000111:6; Rn:5; Rd:5] ->
    // AND
    SOME (arm_AND_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (if q then 128 else 64))
```
When a 32-bit value is undefined (either currently not supported or not a valid instruction), the function `decode` returns `NONE`.

#### Registers

In the above example, `QREG'` could be think of as a register constructor. s2n-bignum supports general-purpose registers and SIMD registers (defined in *arm/proofs/instruction.ml*). These definitions also specify the behaviour when read from or write to these registers.

### Instruction Semantics

[Location: arm/proofs/instruction.ml](proofs/instruction.ml)

After the decoding step, instructions are interpreted by the semantics function. They are defined as `arm_xxx`. For example, the following function `arm_AND_VEC` is the semantic function for modeling the SIMD vector `AND` (note that `_VEC` is added to differetiate from non-SIMD `AND`).

```
let arm_AND_VEC = define
 `arm_AND_VEC Rd Rn Rm datasize =
    \s. let m = read Rm s
        and n = read Rn s in
        if datasize = 128 then
          let d:(128)word = word_and m n in
          (Rd := d) s
        else
          let d:(64)word = word_subword (word_and m n) (0,64) in
          (Rd := word_zx d:(128)word) s`;;
```
The semantics definition is a statement universally quantified over the *armstate* `s`. It says that forall *armstate*, executing the `arm_AND_VEC` instruction is defined as setting the `Rd` register to the result of applying `word_and` to the two values read from register `Rm` and register `Rn`. Note that the syntax
```
(... ,, ... ,, ...) s
```
is a way of assigning values to the state variables in *armstate* `s` to create a new state. The `,,` function called `seq` sequence a list of assignments. For more detail, check *common/relational.ml*.

Often, one will need access to supported word functions for implementing the semantics. Usually it is enough to read the [HOL Light word library](https://github.com/jrh13/hol-light/blob/master/Library/words.ml) for this purpose.

#### Conversions

s2n-bignum supports generic framework for adding conversion rules or tactics for new instructions. The `ARM_OPERATION_CLAUSES` and `ARM_LOAD_STORE_CLAUSES` defintions store clauses that specify rewrite rules for instructions semantic definitions. They are used in the symbolic simulation and cosimulation testing for supporting definition expansion of these instructions.

SIMD instructions could be a bit more involved because of the helper word functions. It essentially adds one more step to what needs to be expanded out. See `all_simd_rules` and `EXPAND_SIMD_RULE` for detail.

More complex instructions that are defined with a deeper chain of functions will require dedicated conversion rules. Check the modeling of SHA2 and AES instructions in this case.

### Cosimulation Test

[Location: arm/proofs/simulator.ml](proofs/simulator.ml)

s2n-bignum conducts cosimulation tests against real machines to ensure correctness of instruction modeling. s2n-bignum will generate randomized 32-bit instructions using patterns. For the cosimulation testing, it generates random values for PC, registers, flags, and memory in the *armstate*, run the instruction on the actual machine with state values pre-set to the randomly generated values and then compare the resulting *armstate* on the machine against the model.

For Arm, the instructions are fixed-length, so it is easier to do random instruction generation. The file *arm/proofs/simulator_iclasses.ml* contains patterns for generating the randomized instructions.

Note that LD/ST instructions are tested in a slightly different way. This is because load from or store to random memory locations is not permitted by the OS. As a workaround, the cosimulation testing framework allocates a 256-byte memory on the stack for testing LD/ST. Special harness functions need to be defined for pointing memory address to the right location in the 256-byte memory on stack. Check *arm/proofs/simulator.ml* for detail.

### Examples

Here are some examples of adding instructions:
* A simple example: [Adding instructions for SHA3](https://github.com/awslabs/s2n-bignum/pull/165)
* Adding cosimulation tests for LD/ST: [Enable memory operations in ARM cosimulator](https://github.com/awslabs/s2n-bignum/pull/186)
* Modeling complex instructions that require dedicated conversions: [Adding Cryptographic AES intrinsics for Armv8](https://github.com/awslabs/s2n-bignum/pull/171)

### Resources

* [The Arm A-profile A64 Instruction Set Architecture](https://developer.arm.com/documentation/ddi0602/2023-12?lang=en)
* [How to Evaluate Expression in HOL Light](https://github.com/aqjune/hol-light-materials/blob/main/EvalExpression.md)
