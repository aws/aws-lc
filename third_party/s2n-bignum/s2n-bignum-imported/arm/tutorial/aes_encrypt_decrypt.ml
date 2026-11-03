(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  AES-256 encryption proof.
******************************************************************************)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;

(* The following program performs an AES-256 encryption:
   - input: 128-bit block stored in memory at address in x1
   - output: 128-bit block to be stored in memory at address in x0
   - round keys: 15 128-bit values stored starting at address in x2, k0 to k14.
                 After the round keys, the number of rounds is stored
                 at offset 240 of address in x2. This number is 14 for AES-256 (see below)
   w6 is the round counter.
   2 round keys are loaded in v0 and v1 before the loop and then in the loop and
   the counter is decremented by 2 in each iteration.

   The instructions AESE and AESMC form one AES encryption round:
   AESE: AESSubBytes(AESShiftRows(operand1 XOR operand2),   // XOR = AddRoundKey
   AESMC: AESMixColumns(operand)
   The last round doesn't use AESMC, only AESE and XOR.
   The output is stored at the end.

   In the specs, the first round key is used in AddRoundKey in the initialization
   then 13 regular rounds, each ending with AddRoundKey,
   then a last round that doesn't have MixColumns and ends with AddRoundKey
   In the implementation, there are 14 rounds that start with AddRoundKey in AESE
   and one last round (with no MixColumns) ending with AddRoundKey.
*)

let aes256_encrypt_mc = define_assert_from_elf "aes256_encrypt_mc" "arm/tutorial/aes_encrypt.o" [
  0xb940f046;       (* arm_LDR W6 X2 (Immediate_Offset (word 240)) *)
  0x4cdf7040;       (* arm_LDR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x4cdf7041;       (* arm_LDR Q1 X2 (Postimmediate_Offset (word 16)) *)
  0x4c407026;       (* arm_LDR Q6 X1 No_Offset *)
  0x510008c6;       (* arm_SUB W6 W6 (rvalue (word 2)) *)
  0x4e284806;       (* arm_AESE Q6 Q0 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4cdf7840;       (* arm_LDR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x710008c6;       (* arm_SUBS W6 W6 (rvalue (word 2)) *)
  0x4e284826;       (* arm_AESE Q6 Q1 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4cdf7841;       (* arm_LDR Q1 X2 (Postimmediate_Offset (word 16)) *)
  0x54ffff2c;       (* arm_BGT (word 2097124) *)
  0x4e284806;       (* arm_AESE Q6 Q0 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4c407840;       (* arm_LDR Q0 X2 No_Offset *)
  0x4e284826;       (* arm_AESE Q6 Q1 *)
  0x6e201cc6;       (* arm_EOR_VEC Q6 Q6 Q0 128 *)
  0x4c007806        (* arm_STR Q6 X0 No_Offset *)
];;

(*
You can get the above OCaml list data structure from
First generating the <file.o> by running at the command line under arm directory:
  $ make tutorial/<file.o>
`print_literal_from_elf "arm/tutorial/<file.o>"` or
`save_literal_from_elf "<file.txt>" "<file.o>"`.
*)

(* ARM_MK_EXEC_RULE decodes the byte sequence into an OCaml array of
  theorems describing the instruction decoded at each PC (only when
  it is multiple of 4). *)
let AES256_ENCRYPT_EXEC = ARM_MK_EXEC_RULE aes256_encrypt_mc;;

let AES256_ENCRYPT_CORRECT = prove(
  `!ciphertext plaintext key pt_in k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 pc.
    nonoverlapping (word pc,LENGTH aes256_encrypt_mc) (ciphertext,16)
    ==> ensures arm
      // precondition
      (\s. aligned_bytes_loaded s (word pc) aes256_encrypt_mc /\
           read PC s = word pc /\
           // uses the C ABI which puts the arguments in their order in registers x0 to x7.
           // Here only 3 arguments are passed in.
           C_ARGUMENTS [ciphertext; plaintext; key] s /\
           read(memory :> bytes128 plaintext) s = pt_in /\
           read(memory :> bytes32 (word_add key (word 240))) s = word 14 /\
           read(memory :> bytes128 key) s = k0 /\
           read(memory :> bytes128 (word_add key (word 16))) s = k1 /\
           read(memory :> bytes128 (word_add key (word 32))) s = k2 /\
           read(memory :> bytes128 (word_add key (word 48))) s = k3 /\
           read(memory :> bytes128 (word_add key (word 64))) s = k4 /\
           read(memory :> bytes128 (word_add key (word 80))) s = k5 /\
           read(memory :> bytes128 (word_add key (word 96))) s = k6 /\
           read(memory :> bytes128 (word_add key (word 112))) s = k7 /\
           read(memory :> bytes128 (word_add key (word 128))) s = k8 /\
           read(memory :> bytes128 (word_add key (word 144))) s = k9 /\
           read(memory :> bytes128 (word_add key (word 160))) s = k10 /\
           read(memory :> bytes128 (word_add key (word 176))) s = k11 /\
           read(memory :> bytes128 (word_add key (word 192))) s = k12 /\
           read(memory :> bytes128 (word_add key (word 208))) s = k13 /\
           read(memory :> bytes128 (word_add key (word 224))) s = k14
      )
      // postcondition
      (\s. read PC s = word (pc + LENGTH aes256_encrypt_mc) /\
           read(memory :> bytes128 ciphertext) s =
              aes256_encrypt pt_in
                [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]
      )
      // Registers (and memory locations) that may change after execution
      (MAYCHANGE [PC;X2;X6],, MAYCHANGE [Q0;Q1;Q6],, MAYCHANGE [events],,
       MAYCHANGE SOME_FLAGS,, MAYCHANGE [memory :> bytes128 ciphertext])`,

  (* Convert C_ARGUMENTS to reading registers x0, x1, x2 and expand SOME_FLAGS *)
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

  (* Find the length of the program using a Conversion *)
  REWRITE_TAC [(REWRITE_CONV [aes256_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_encrypt_mc`] THEN

 (* Strips the outermost universal quantifier from the conclusion of a goal *)
  REPEAT STRIP_TAC THEN
  (* Start symbolic execution with state 's0' *)
  ENSURES_INIT_TAC "s0" THEN
  (* Symbolic execution *)
  ARM_STEPS_TAC AES256_ENCRYPT_EXEC (1--6) THEN
  ARM_STEPS_TAC AES256_ENCRYPT_EXEC (7--59) THEN
  (* Returned; Finalize symbolic execution. *)
  ENSURES_FINAL_STATE_TAC THEN

  (* Use ASM_REWRITE_TAC[] to rewrite the goal using equalities in assumptions. *)
  ASM_REWRITE_TAC[] THEN
  (* Use the specs to expand defintions *)
  REWRITE_TAC [aes256_encrypt] THEN

  (* Replace the elements selection, EL, with the selected element
     from the key round list. *)
  REWRITE_TAC EL_15_128_CLAUSES THEN

  (* Expand definitions and evaluate `let` terms. *)
  REWRITE_TAC [aes256_encrypt_round; aese; aesmc] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN

  (* Evaluate the logical expression on both sides as a gate circuit between bits. *)
  BITBLAST_TAC
  (* Alternatively, use the XOR symmetry *)
  (* GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
    REFL_TAC *)
);;

(******************************************************************************
  AES-256 decryption proof.
******************************************************************************)

needs "arm/proofs/utils/aes_decrypt_spec.ml";;

(* The following program performs an AES-256 decryption,
   with the following differences from encryption (see tutorial/aes_encrypt.ml):

   procedure EQINVCIPHER(in, Nr, dw) is the one used from the standard in order
   to be able to use the same round keys in the same order as with encrypt.

   The instructions AESD and AESIMC form one AES decryption round:
   AESD: AESInvSubBytes(AESInvShiftRows(operand1 XOR operand2),   // XOR = AddRoundKey
   AESIMC: AESInvMixColumns(operand)
   The last round doesn't use AESIMC, only AESD and XOR.
*)

let aes256_decrypt_mc = define_assert_from_elf "aes256_decrypt_mc" "arm/tutorial/aes_decrypt.o"
[
  0xb940f046;       (* arm_LDR W6 X2 (Immediate_Offset (word 240)) *)
  0x4cdf7040;       (* arm_LDR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x4cdf7041;       (* arm_LDR Q1 X2 (Postimmediate_Offset (word 16)) *)
  0x4c407026;       (* arm_LDR Q6 X1 No_Offset *)
  0x510008c6;       (* arm_SUB W6 W6 (rvalue (word 2)) *)
  0x4e285806;       (* arm_AESD Q6 Q0 *)
  0x4e2878c6;       (* arm_AESIMC Q6 Q6 *)
  0x4cdf7840;       (* arm_LDR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x710008c6;       (* arm_SUBS W6 W6 (rvalue (word 2)) *)
  0x4e285826;       (* arm_AESD Q6 Q1 *)
  0x4e2878c6;       (* arm_AESIMC Q6 Q6 *)
  0x4cdf7841;       (* arm_LDR Q1 X2 (Postimmediate_Offset (word 16)) *)
  0x54ffff2c;       (* arm_BGT (word 2097124) *)
  0x4e285806;       (* arm_AESD Q6 Q0 *)
  0x4e2878c6;       (* arm_AESIMC Q6 Q6 *)
  0x4c407840;       (* arm_LDR Q0 X2 No_Offset *)
  0x4e285826;       (* arm_AESD Q6 Q1 *)
  0x6e201cc6;       (* arm_EOR_VEC Q6 Q6 Q0 128 *)
  0x4c007806        (* arm_STR Q6 X0 No_Offset *)
];;

let AES256_DECRYPT_EXEC = ARM_MK_EXEC_RULE aes256_decrypt_mc;;

let AES256_DECRYPT_CORRECT = prove(
  `!plaintext ciphertext key ib k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 pc.
    nonoverlapping (word pc,LENGTH aes256_decrypt_mc) (plaintext,16)
    ==> ensures arm
      // precondition
      (\s. aligned_bytes_loaded s (word pc) aes256_decrypt_mc /\
           read PC s = word pc /\
           // uses the C ABI which puts the arguments in their order in registers x0 to x7.
           // Here only 3 arguments are passed in.
           C_ARGUMENTS [plaintext; ciphertext; key] s /\
           read(memory :> bytes128 ciphertext) s = ib /\
           read(memory :> bytes32 (word_add key (word 240))) s = word 14 /\
           read(memory :> bytes128 key) s = k0 /\
           read(memory :> bytes128 (word_add key (word 16))) s = k1 /\
           read(memory :> bytes128 (word_add key (word 32))) s = k2 /\
           read(memory :> bytes128 (word_add key (word 48))) s = k3 /\
           read(memory :> bytes128 (word_add key (word 64))) s = k4 /\
           read(memory :> bytes128 (word_add key (word 80))) s = k5 /\
           read(memory :> bytes128 (word_add key (word 96))) s = k6 /\
           read(memory :> bytes128 (word_add key (word 112))) s = k7 /\
           read(memory :> bytes128 (word_add key (word 128))) s = k8 /\
           read(memory :> bytes128 (word_add key (word 144))) s = k9 /\
           read(memory :> bytes128 (word_add key (word 160))) s = k10 /\
           read(memory :> bytes128 (word_add key (word 176))) s = k11 /\
           read(memory :> bytes128 (word_add key (word 192))) s = k12 /\
           read(memory :> bytes128 (word_add key (word 208))) s = k13 /\
           read(memory :> bytes128 (word_add key (word 224))) s = k14)
      // postcondition
      (\s. read PC s = word (pc + LENGTH aes256_decrypt_mc) /\
           read (memory :> bytes128 plaintext) s =
             aes256_decrypt ib [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]
        )
      // Registers (and memory locations) that may change after execution
      (MAYCHANGE [PC;X6;X2] ,, MAYCHANGE [Q0; Q1; Q6],,
       MAYCHANGE [memory :> bytes128 plaintext],,
       MAYCHANGE SOME_FLAGS,, MAYCHANGE [events])`,

  MAP_EVERY X_GEN_TAC
   [`plaintext:int64`; `ciphertext:int64`; `key:int64`;
    `ib:int128`; `k0:int128`; `k1:int128`; `k2:int128`;
    `k3:int128`; `k4:int128`; `k5:int128`; `k6:int128`;
    `k7:int128`; `k8:int128`; `k9:int128`; `k10:int128`;
    `k11:int128`; `k12:int128`; `k13:int128`; `k14:int128`; `pc:num`] THEN

  (* Convert C_ARGUMENTS to reading registers x0, x1, x2 and expand SOME_FLAGS *)
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

  (* Find the length of the program using a Conversion *)
  REWRITE_TAC [(REWRITE_CONV [aes256_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_decrypt_mc`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (* Start symbolic execution with state 's0' *)
  ENSURES_INIT_TAC "s0" THEN
  (* Symbolic execution of all instructions *)
  ARM_ACCSTEPS_TAC AES256_DECRYPT_EXEC [] (1--59) THEN
  (* Returned; Finalize symbolic execution. *)
  ENSURES_FINAL_STATE_TAC THEN
  (* Use ASM_REWRITE_TAC[] to rewrite the goal using equalities in assumptions. *)
  ASM_REWRITE_TAC[] THEN

  (* Use the specs to expand defintions *)
  REWRITE_TAC [aes256_decrypt] THEN

  (* Replace the elements selection, EL, with the selected element
     from the key round list. *)
  REWRITE_TAC EL_15_128_CLAUSES THEN

  (* Expand definitions and evaluate `let` terms *)
  REWRITE_TAC [aes256_decrypt_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC [aesd;aesimc] THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
  REFL_TAC
);;
