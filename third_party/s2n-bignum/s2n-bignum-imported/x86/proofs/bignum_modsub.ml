(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Modular subtraction of bignums.                                           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_modsub.o";;
 ****)

let bignum_modsub_mc =
  define_assert_from_elf "bignum_modsub_mc" "x86/generic/bignum_modsub.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x3c;              (* JE (Imm8 (word 60)) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x49; 0x89; 0xfa;        (* MOV (% r10) (% rdi) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4a; 0x8b; 0x04; 0xca;  (* MOV (% rax) (Memop Quadword (%%% (rdx,3,r9))) *)
  0x4a; 0x1b; 0x04; 0xc9;  (* SBB (% rax) (Memop Quadword (%%% (rcx,3,r9))) *)
  0x4a; 0x89; 0x04; 0xce;  (* MOV (Memop Quadword (%%% (rsi,3,r9))) (% rax) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0xff; 0xca;        (* DEC (% r10) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4b; 0x8b; 0x04; 0xc8;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,r9))) *)
  0x4c; 0x21; 0xd8;        (* AND (% rax) (% r11) *)
  0x49; 0xf7; 0xda;        (* NEG (% r10) *)
  0x4a; 0x11; 0x04; 0xce;  (* ADC (Memop Quadword (%%% (rsi,3,r9))) (% rax) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xf9;        (* CMP (% r9) (% rdi) *)
  0x72; 0xe7;              (* JB (Imm8 (word 231)) *)
  0xc3                     (* RET *)
];;

let bignum_modsub_tmc = define_trimmed "bignum_modsub_tmc" bignum_modsub_mc;;

let BIGNUM_MODSUB_EXEC = X86_MK_CORE_EXEC_RULE bignum_modsub_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODSUB_CORRECT = prove
 (`!k z x y m a b n pc.
        nonoverlapping (word pc,0x42) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_modsub_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = word(pc + 0x41) /\
                  &(bignum_from_memory (z,val k) s) = (&a - &b) rem &n)
            (MAYCHANGE [RIP; RAX; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`;` n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`; `n:num`] THEN

  (*** Deal with degenerate case k = 0 first ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; ADD_CLAUSES; MOD_0] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODSUB_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_REM_0; INT_SUB_REFL];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  MP_TAC(ASSUME
   `nonoverlapping_modulo (2 EXP 64) (pc,66) (val(z:int64),8 * k)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Main subtraction, subloop ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0xe` `pc + 0x20`
    `\i s. (read RDI s = word k /\
            read RSI s = z /\
            read RDX s = x /\
            read RCX s = y /\
            read R8 s = m /\
            bignum_from_memory (m,k) s = n /\
            read R9 s = word i /\
            read R10 s = word(k - i) /\
            read R11 s = word 0 /\
            bignum_from_memory (word_add x (word(8 * i)),k - i) s =
            highdigits a i /\
            bignum_from_memory (word_add y (word(8 * i)),k - i) s =
            highdigits b i /\
            &(bignum_from_memory(z,i) s):real =
            &2 pow (64 * i) * &(bitval(read CF s)) +
            &(lowdigits a i) - &(lowdigits b i)) /\
           (read ZF s <=> i = k)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODSUB_EXEC (1--5) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN REAL_ARITH_TAC;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     X86_ACCSTEPS_TAC BIGNUM_MODSUB_EXEC [2] (1--5) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WORD_ADD] THEN REPEAT CONJ_TAC THENL
      [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       REWRITE_TAC[LOWDIGITS_CLAUSES];
       REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
       VAL_INT64_TAC `k - i:num` THEN
       ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1] THEN ARITH_TAC] THEN
     ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
     ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
     REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; REAL_POW_ADD] THEN
     CONV_TAC REAL_RING;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODSUB_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** Masked addition operation "addloop" ***)

  GHOST_INTRO_TAC `hi:bool` `read CF` THEN
  GHOST_INTRO_TAC `lo:num` `bignum_from_memory(z,k)` THEN
  ASM_CASES_TAC
   `&2 pow (64 * k) * &(bitval hi) + &a - &b:real = &lo` THEN
  ASM_REWRITE_TAC[ENSURES_TRIVIAL] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `lo:num` THEN

  SUBGOAL_THEN `hi <=> a:num < b` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `64 * k` THEN
    ASM_REWRITE_TAC[GSYM REAL_BITVAL_NOT] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN

  (*** Masked addition operation "addloop" ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x28` `pc + 0x3c`
    `\i s. read RDI s = word k /\
           read RSI s = z /\
           read R8 s = m /\
           read R9 s = word i /\
           val(word_neg(read R10 s)) <= 1 /\
           read R11 s = word_neg(word(bitval(a < b))) /\
           bignum_from_memory (word_add z (word(8 * i)),k - i) s =
           highdigits lo i /\
           bignum_from_memory (word_add m (word(8 * i)),k - i) s =
           highdigits n i /\
           &(bignum_from_memory(z,i) s):real =
           (&(lowdigits lo i) + &(bitval(a < b)) * &(lowdigits n i)) -
           &2 pow (64 * i) * &(val(word_neg(read R10 s)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODSUB_EXEC (1--3) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
     REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; LE_0; WORD_SUB_LZERO] THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BITVAL_CLAUSES] THEN
     REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_REFL; REAL_ADD_LID];

     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cval:num` `\s. val(word_neg(read R10 s))` THEN
     GLOBALIZE_PRECONDITION_TAC THEN
     FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
       GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
     REWRITE_TAC[VAL_EQ_BITVAL] THEN
     REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     X86_ACCSTEPS_TAC BIGNUM_MODSUB_EXEC [4] (1--6) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
     REWRITE_TAC[WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; WORD_BITVAL_EQ_0;
                 LOWDIGITS_CLAUSES; WORD_NEG_EQ_0; BITVAL_BOUND; NOT_LT] THEN
     REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[NOT_LT] THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0;
              BITVAL_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
     REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODSUB_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** The finale ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODSUB_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  TRANS_TAC EQ_TRANS `(&a - &b) + &(bitval(a < b)) * &n:int` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[int_eq; int_add_th; int_sub_th; int_mul_th; int_of_num_th];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
    EXISTS_TAC `--(&(bitval(a < b))):int` THEN REWRITE_TAC[INT_ABS_NUM] THEN
    MAP_EVERY UNDISCH_TAC [`a:num < n`; `b:num < n`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_LT; bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a:num < n`; `b:num < n`; `n < 2 EXP (64 * k)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `&2 pow (64 * k) * &(bitval (a < b)) + &a - &b:real = &lo`
   (SUBST1_TAC o SYM) THEN
  ASM_CASES_TAC `a:num < b` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  REWRITE_TAC[real_sub; REAL_ADD_RID; GSYM REAL_ADD_ASSOC] THEN
  REWRITE_TAC[REAL_ARITH `x / y:real = inv y * x`; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_MUL_RNEG; REAL_MUL_ASSOC] THEN
  SIMP_TAC[REAL_MUL_LINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REAL_INTEGER_TAC);;

let BIGNUM_MODSUB_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_modsub_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modsub_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  &(bignum_from_memory (z,val k) s) = (&a - &b) rem &n)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_modsub_tmc BIGNUM_MODSUB_CORRECT);;

let BIGNUM_MODSUB_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_modsub_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modsub_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  &(bignum_from_memory (z,val k) s) = (&a - &b) rem &n)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODSUB_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_modsub_windows_mc = define_from_elf
   "bignum_modsub_windows_mc" "x86/generic/bignum_modsub.obj";;

let bignum_modsub_windows_tmc = define_trimmed "bignum_modsub_windows_tmc" bignum_modsub_windows_mc;;

let BIGNUM_MODSUB_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_modsub_windows_tmc); (x,8 * val k); (y,8 * val k); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_modsub_windows_tmc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modsub_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  &(bignum_from_memory (z,val k) s) = (&a - &b) rem &n)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_modsub_windows_tmc bignum_modsub_tmc
    BIGNUM_MODSUB_CORRECT);;

let BIGNUM_MODSUB_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_modsub_windows_mc); (x,8 * val k); (y,8 * val k); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_modsub_windows_mc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modsub_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  &(bignum_from_memory (z,val k) s) = (&a - &b) rem &n)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODSUB_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

