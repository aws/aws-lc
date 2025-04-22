(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional negation of bignums.                                             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_optneg.o";;
 ****)

let bignum_optneg_mc =
  define_assert_from_elf "bignum_optneg_mc" "x86/generic/bignum_optneg.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x32;              (* JE (Imm8 (word 50)) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0x19; 0xd2;        (* SBB (% rdx) (% rdx) *)
  0x48; 0x29; 0xd0;        (* SUB (% rax) (% rdx) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4e; 0x8b; 0x04; 0xc9;  (* MOV (% r8) (Memop Quadword (%%% (rcx,3,r9))) *)
  0x49; 0x31; 0xd0;        (* XOR (% r8) (% rdx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x4e; 0x89; 0x04; 0xce;  (* MOV (Memop Quadword (%%% (rsi,3,r9))) (% r8) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xf9;        (* CMP (% r9) (% rdi) *)
  0x72; 0xe1;              (* JB (Imm8 (word 225)) *)
  0x48; 0x31; 0xd0;        (* XOR (% rax) (% rdx) *)
  0x48; 0x83; 0xe0; 0x01;  (* AND (% rax) (Imm8 (word 1)) *)
  0xc3                     (* RET *)
];;

let bignum_optneg_tmc = define_trimmed "bignum_optneg_tmc" bignum_optneg_mc;;

let BIGNUM_OPTNEG_EXEC = X86_MK_CORE_EXEC_RULE bignum_optneg_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_OPTNEG_CORRECT = prove
 (`!k z p x a pc.
       nonoverlapping (word pc,0x3b) (z,8 * val k) /\
       (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
       ==> ensures x86
            (\s. bytes_loaded s (word pc) (BUTLAST bignum_optneg_tmc) /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [k;z;p;x] s /\
                 bignum_from_memory (x,val k) s = a)
            (\s. read RIP s = word(pc + 0x3a) /\
                 bignum_from_memory(z,val k) s =
                 (if p = word 0 \/ a = 0 then a else 2 EXP (64 * val k) - a) /\
                 C_RETURN s = word(bitval(~(p = word 0) /\ ~(a = 0))))
            (MAYCHANGE [RIP; RAX; RDX; R8; R9] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `p:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `a:num` THEN

  (*** The trivial k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN RULE_ASSUM_TAC
    (REWRITE_RULE[ARITH_RULE `a < 2 EXP (64 * 0) <=> a = 0`]) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_OPTNEG_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[BITVAL_CLAUSES];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Main loop setup ***)

  ABBREV_TAC `m <=> ~(p:int64 = word 0)` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x14` `pc + 0x2e`
   `\i s. read RSI s = z /\
          read RCX s = x /\
          read RDX s = word_neg(word(bitval m)) /\
          read RDI s = word k /\
          read R9 s = word i /\
          val(read RAX s) <= 1 /\
          bignum_from_memory (word_add x (word(8 * i)),k - i) s =
          highdigits a i /\
          2 EXP (64 * i) * val(read RAX s) + bignum_from_memory(z,i) s =
          (if p:int64 = word 0 then lowdigits a i
           else 2 EXP (64 * i) - lowdigits a i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_OPTNEG_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; ADD_CLAUSES; MULT_CLAUSES;
                SUB_0; BITVAL_CLAUSES; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    SIMP_TAC[WORD_SUB_LZERO; WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
    EXPAND_TAC "m" THEN
    REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; bitval; COND_SWAP] THEN
    ASM_REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    ASM_CASES_TAC `p:int64 = word 0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_OPTNEG_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    GHOST_INTRO_TAC `cinn:num` `\s. val(read RAX s)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN

    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_OPTNEG_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; WORD_SUB_LZERO; WORD_NEG_NEG] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
    UNDISCH_THEN `~(p:int64 = word 0) <=> m` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; WORD_XOR_CONDITIONS] THEN DISCH_THEN(fun th ->
     MP_TAC(AP_TERM `\x. x DIV 2 EXP (64 * k)` th) THEN
     MP_TAC(AP_TERM `\x. x MOD 2 EXP (64 * k)` th)) THEN
    SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[DIV_LT; MOD_LT; BIGNUM_FROM_MEMORY_BOUND; ADD_CLAUSES] THEN
    ASM_CASES_TAC `p:int64 = word 0` THEN
    ASM_SIMP_TAC[BITVAL_CLAUSES; MOD_LT; DIV_LT] THEN
    ASM_CASES_TAC `a = 0` THEN
    ASM_SIMP_TAC[SUB_0; BITVAL_CLAUSES; BITVAL_EQ_1; BITVAL_EQ_0;
                 DIV_LT; MOD_LT; DIV_REFL; MOD_REFL; EXP_EQ_0; ARITH_EQ;
                 ARITH_RULE `~(m = 0) /\ ~(n = 0) ==> m - n < m`] THEN
    CONV_TAC WORD_REDUCE_CONV] THEN

  (*** Proof of the main invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  GHOST_INTRO_TAC `cinn:num` `\s. val(read RAX s)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_ACCSTEPS_TAC BIGNUM_OPTNEG_EXEC [3] (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_BOUND] THEN

  FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN

  FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; LOWDIGITS_BOUND; LT_IMP_LE] THEN
  REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_POW_ADD] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `c + s:real = x ==> s = x - c`)) THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_XOR_MASK] THEN
  UNDISCH_THEN `~(p:int64 = word 0) <=> m` (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
  ASM_CASES_TAC `p:int64 = word 0` THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64;
               REAL_VAL_WORD_NOT] THEN
  REAL_ARITH_TAC);;

let BIGNUM_OPTNEG_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z p x a pc stackpointer returnaddress.
       nonoverlapping (word pc,LENGTH bignum_optneg_tmc) (z,8 * val k) /\
       nonoverlapping (stackpointer,8) (z,8 * val k) /\
       (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
       ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_optneg_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [k;z;p;x] s /\
                 bignum_from_memory (x,val k) s = a)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory(z,val k) s =
                 (if p = word 0 \/ a = 0 then a else 2 EXP (64 * val k) - a) /\
                 C_RETURN s = word(bitval(~(p = word 0) /\ ~(a = 0))))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_optneg_tmc BIGNUM_OPTNEG_CORRECT);;

let BIGNUM_OPTNEG_SUBROUTINE_CORRECT = prove
 (`!k z p x a pc stackpointer returnaddress.
       nonoverlapping (word pc,LENGTH bignum_optneg_mc) (z,8 * val k) /\
       nonoverlapping (stackpointer,8) (z,8 * val k) /\
       (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
       ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_optneg_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [k;z;p;x] s /\
                 bignum_from_memory (x,val k) s = a)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory(z,val k) s =
                 (if p = word 0 \/ a = 0 then a else 2 EXP (64 * val k) - a) /\
                 C_RETURN s = word(bitval(~(p = word 0) /\ ~(a = 0))))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OPTNEG_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_optneg_windows_mc = define_from_elf
   "bignum_optneg_windows_mc" "x86/generic/bignum_optneg.obj";;

let bignum_optneg_windows_tmc = define_trimmed "bignum_optneg_windows_tmc" bignum_optneg_windows_mc;;

let BIGNUM_OPTNEG_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z p x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_optneg_windows_tmc); (x,8 * val k)] /\
       nonoverlapping (word pc,LENGTH bignum_optneg_windows_tmc) (z,8 * val k) /\
       nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
       (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
       ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_optneg_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [k;z;p;x] s /\
                 bignum_from_memory (x,val k) s = a)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory(z,val k) s =
                 (if p = word 0 \/ a = 0 then a else 2 EXP (64 * val k) - a) /\
                 WINDOWS_C_RETURN s = word(bitval(~(p = word 0) /\ ~(a = 0))))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,val k);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_optneg_windows_tmc bignum_optneg_tmc
    BIGNUM_OPTNEG_CORRECT);;

let BIGNUM_OPTNEG_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z p x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_optneg_windows_mc); (x,8 * val k)] /\
       nonoverlapping (word pc,LENGTH bignum_optneg_windows_mc) (z,8 * val k) /\
       nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
       (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
       ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_optneg_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [k;z;p;x] s /\
                 bignum_from_memory (x,val k) s = a)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory(z,val k) s =
                 (if p = word 0 \/ a = 0 then a else 2 EXP (64 * val k) - a) /\
                 WINDOWS_C_RETURN s = word(bitval(~(p = word 0) /\ ~(a = 0))))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,val k);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OPTNEG_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

