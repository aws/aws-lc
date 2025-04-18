(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Creation of a power-of-2 bignum using the input word as the index.        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_pow2.o";;
 ****)

let bignum_pow2_mc =
  define_assert_from_elf "bignum_pow2_mc" "x86/generic/bignum_pow2.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x28;              (* JE (Imm8 (word 40)) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xd3; 0xe0;        (* SHL (% rax) (% cl) *)
  0x48; 0xc1; 0xea; 0x06;  (* SHR (% rdx) (Imm8 (word 6)) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x48; 0x39; 0xd1;        (* CMP (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc0;  (* CMOVE (% r8) (% rax) *)
  0x4c; 0x89; 0x04; 0xce;  (* MOV (Memop Quadword (%%% (rsi,3,rcx))) (% r8) *)
  0x48; 0xff; 0xc1;        (* INC (% rcx) *)
  0x48; 0x39; 0xf9;        (* CMP (% rcx) (% rdi) *)
  0x72; 0xea;              (* JB (Imm8 (word 234)) *)
  0xc3                     (* RET *)
];;

let bignum_pow2_tmc = define_trimmed "bignum_pow2_tmc" bignum_pow2_mc;;

let BIGNUM_POW2_EXEC = X86_MK_CORE_EXEC_RULE bignum_pow2_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_POW2_CORRECT = prove
 (`!k z n pc.
        nonoverlapping (word pc,0x2e) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_pow2_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [k;z;n] s)
             (\s. read RIP s = word(pc + 0x2d) /\
                  bignum_from_memory (z,val k) s =
                  lowdigits (2 EXP (val n)) (val k))
             (MAYCHANGE [RIP; RDX; RAX; RCX; R8] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** The trivial case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_POW2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0];
    ALL_TAC] THEN

  (*** Main loop setup ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x17` `pc + 0x28`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read RDX s = word(n DIV 64) /\
          read RAX s = word(2 EXP (n MOD 64)) /\
          read RCX s = word i /\
          bignum_from_memory(z,i) s = lowdigits (2 EXP n) i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_POW2_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_8; ARITH; MOD_LT_EQ] THEN
    REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8 /\ 64 = 2 EXP 6`] THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
    ASM_REWRITE_TAC[word_ushr; word_shl; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[word_shl; VAL_WORD_1; MULT_CLAUSES];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_POW2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    X86_SIM_TAC BIGNUM_POW2_EXEC (1--2)] THEN

  (*** Main loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; LOWDIGITS_CLAUSES] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_POW2_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  VAL_INT64_TAC `n DIV 64` THEN ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM COND_RAND] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `2 EXP n = 2 EXP (64 * n DIV 64 + n MOD 64)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ARITH_TAC; REWRITE_TAC[EXP_ADD; bigdigit]] THEN
  CONV_TAC SYM_CONV THEN
  ASM_CASES_TAC `n DIV 64 = i` THEN ASM_REWRITE_TAC[] THENL
   [SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[LT_EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(a = b) ==> a < b \/ b < a`))
  THENL
   [MATCH_MP_TAC(MESON[MOD_0] `n = 0 ==> n MOD p = 0`) THEN
    SIMP_TAC[DIV_EQ_0; GSYM EXP_ADD; EXP_EQ_0; ARITH_EQ; LT_EXP] THEN
    UNDISCH_TAC `n DIV 64 < i` THEN ARITH_TAC;
    SIMP_TAC[DIV_MOD; DIV_EQ_0; ARITH_EQ; EXP_EQ_0] THEN
    MATCH_MP_TAC(ARITH_RULE `m = 0 /\ ~(n = 0) ==> m < n`) THEN
    REWRITE_TAC[GSYM EXP_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM DIVIDES_MOD] THEN MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
    UNDISCH_TAC `i < n DIV 64` THEN ARITH_TAC]);;

let BIGNUM_POW2_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_pow2_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_pow2_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;n] s)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  lowdigits (2 EXP (val n)) (val k))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_pow2_tmc BIGNUM_POW2_CORRECT);;

let BIGNUM_POW2_SUBROUTINE_CORRECT = prove
 (`!k z n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_pow2_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_pow2_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;n] s)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  lowdigits (2 EXP (val n)) (val k))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_POW2_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_pow2_windows_mc = define_from_elf
   "bignum_pow2_windows_mc" "x86/generic/bignum_pow2.obj";;

let bignum_pow2_windows_tmc = define_trimmed "bignum_pow2_windows_tmc" bignum_pow2_windows_mc;;

let BIGNUM_POW2_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_pow2_windows_tmc)] /\
        nonoverlapping (word pc,LENGTH bignum_pow2_windows_tmc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_pow2_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;n] s)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  lowdigits (2 EXP (val n)) (val k))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_pow2_windows_tmc bignum_pow2_tmc
    BIGNUM_POW2_CORRECT);;

let BIGNUM_POW2_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_pow2_windows_mc)] /\
        nonoverlapping (word pc,LENGTH bignum_pow2_windows_mc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_pow2_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;n] s)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  lowdigits (2 EXP (val n)) (val k))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_POW2_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

