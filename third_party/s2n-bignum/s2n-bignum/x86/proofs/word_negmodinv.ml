(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Word-level negated modular inverse.                                       *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/word_negmodinv.o";;
 ****)

let word_negmodinv_mc = define_assert_from_elf "word_negmodinv_mc" "x86/generic/word_negmodinv.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x89; 0xf9;        (* MOV (% rcx) (% rdi) *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0xc1; 0xe1; 0x02;  (* SHL (% rcx) (Imm8 (word 2)) *)
  0x48; 0x29; 0xc8;        (* SUB (% rax) (% rcx) *)
  0x48; 0x83; 0xf0; 0x02;  (* XOR (% rax) (Imm8 (word 2)) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0x0f; 0xaf; 0xcf;  (* IMUL (% rcx) (% rdi) *)
  0xba; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 2)) *)
  0x48; 0x01; 0xca;        (* ADD (% rdx) (% rcx) *)
  0x48; 0x83; 0xc1; 0x01;  (* ADD (% rcx) (Imm8 (word 1)) *)
  0x48; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xc9;  (* IMUL (% rcx) (% rcx) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x48; 0x01; 0xca;        (* ADD (% rdx) (% rcx) *)
  0x48; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xc9;  (* IMUL (% rcx) (% rcx) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x48; 0x01; 0xca;        (* ADD (% rdx) (% rcx) *)
  0x48; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xc9;  (* IMUL (% rcx) (% rcx) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x48; 0x01; 0xca;        (* ADD (% rdx) (% rcx) *)
  0x48; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% rdx) *)
  0xc3                     (* RET *)
];;

let word_negmodinv_tmc = define_trimmed "word_negmodinv_tmc" word_negmodinv_mc;;

let WORD_NEGMODINV_EXEC = X86_MK_CORE_EXEC_RULE word_negmodinv_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** This actually works mod 32 but if anything this is more convenient ***)

let WORD_NEGMODINV_SEED_LEMMA_16 = prove
 (`!a x:int64.
        ODD a /\
        word_xor (word_sub (word a) (word_shl (word a) 2)) (word 2) = x
        ==> (a * val x + 1 == 0) (mod 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONG; MOD_0] THEN
  TRANS_TAC EQ_TRANS
   `(val(word a:int64) MOD 16 * val(x:int64) MOD 16 + 1) MOD 16` THEN
  REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`] THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    REWRITE_TAC[VAL_MOD; NUMSEG_LT; ARITH_EQ; ARITH]] THEN
  SUBGOAL_THEN `bit 0 (word a:int64)` MP_TAC THENL
   [ASM_REWRITE_TAC[BIT_LSB_WORD];
    EXPAND_TAC "x" THEN POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 1 (word a:int64)`;`bit 2 (word a:int64)`;`bit 3 (word a:int64)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_NEGMODINV_CORRECT = prove
 (`!a pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST word_negmodinv_tmc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = word(pc + 0x58) /\
               (ODD(val a)
                ==> (val a * val(C_RETURN s) + 1 == 0) (mod (2 EXP 64))))
          (MAYCHANGE [RIP; RAX; RCX; RDX] ,,
           MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `a:num` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x11`
    `\s. read RDI s = word a /\
         (ODD a ==> (a * val (read RAX s) + 1 == 0) (mod 16))` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC WORD_NEGMODINV_EXEC (1--5) THEN
    ASM_SIMP_TAC[WORD_NEGMODINV_SEED_LEMMA_16];
    GHOST_INTRO_TAC `x0:int64` `read RAX` THEN
    X86_SIM_TAC WORD_NEGMODINV_EXEC (1--18) THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 16 EXP (2 EXP 4)`) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SPEC_TAC(`16`,`e:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUMBER_RULE]);;

let WORD_NEGMODINV_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_negmodinv_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (ODD(val a)
                ==> (val a * val(C_RETURN s) + 1 == 0) (mod (2 EXP 64))))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC word_negmodinv_tmc WORD_NEGMODINV_CORRECT);;

let WORD_NEGMODINV_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_negmodinv_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (ODD(val a)
                ==> (val a * val(C_RETURN s) + 1 == 0) (mod (2 EXP 64))))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_NEGMODINV_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let word_negmodinv_windows_mc = define_from_elf
   "word_negmodinv_windows_mc" "x86/generic/word_negmodinv.obj";;

let word_negmodinv_windows_tmc = define_trimmed "word_negmodinv_windows_tmc" word_negmodinv_windows_mc;;

let WORD_NEGMODINV_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_negmodinv_windows_tmc)
        ==>  ensures x86
              (\s. bytes_loaded s (word pc) word_negmodinv_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   (ODD(val a)
                    ==> (val a * val(WINDOWS_C_RETURN s) + 1 == 0)
                        (mod (2 EXP 64))))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC word_negmodinv_windows_tmc word_negmodinv_tmc
    WORD_NEGMODINV_CORRECT);;

let WORD_NEGMODINV_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_negmodinv_windows_mc)
        ==>  ensures x86
              (\s. bytes_loaded s (word pc) word_negmodinv_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   (ODD(val a)
                    ==> (val a * val(WINDOWS_C_RETURN s) + 1 == 0)
                        (mod (2 EXP 64))))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_NEGMODINV_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

