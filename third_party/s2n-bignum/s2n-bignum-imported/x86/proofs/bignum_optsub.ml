(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* "Optional subtraction" function, subtracting iff a flag is nonzero.       *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_optsub.o";;
 ****)

let bignum_optsub_mc =
  define_assert_from_elf "bignum_optsub_mc" "x86/generic/bignum_optsub.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x2c;              (* JE (Imm8 (word 44)) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4e; 0x8b; 0x1c; 0xca;  (* MOV (% r11) (Memop Quadword (%%% (rdx,3,r9))) *)
  0x4f; 0x8b; 0x14; 0xc8;  (* MOV (% r10) (Memop Quadword (%%% (r8,3,r9))) *)
  0x49; 0x21; 0xca;        (* AND (% r10) (% rcx) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x4d; 0x19; 0xd3;        (* SBB (% r11) (% r10) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x4e; 0x89; 0x1c; 0xce;  (* MOV (Memop Quadword (%%% (rsi,3,r9))) (% r11) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xf9;        (* CMP (% r9) (% rdi) *)
  0x72; 0xe0;              (* JB (Imm8 (word 224)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0xc3                     (* RET *)
];;

let bignum_optsub_tmc = define_trimmed "bignum_optsub_tmc" bignum_optsub_mc;;

let BIGNUM_OPTSUB_EXEC = X86_MK_CORE_EXEC_RULE bignum_optsub_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_OPTSUB_CORRECT = prove
 (`!k z x p y m n pc.
        nonoverlapping (word pc,0x35) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_optsub_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [k; z; x; p; y] s /\
                  bignum_from_memory (x,val k) s = m /\
                  bignum_from_memory (y,val k) s = n)
             (\s. read RIP s = word (pc + 0x34) /\
                  (bignum_from_memory (z,val k) s =
                   if p = word 0 then m
                   else if n <= m then m - n
                   else (2 EXP (64 * val k) + m) - n) /\
                  (C_RETURN s =
                   if ~(p = word 0) /\ m < n then word 1 else word 0))
          (MAYCHANGE [RIP; RAX; RCX; R9; R10; R11] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `b:int64`; `y:int64`;
    `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`m:num`; `n:num`] THEN

  (*** The trivial k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN RULE_ASSUM_TAC
     (REWRITE_RULE[ARITH_RULE `a < 2 EXP (64 * 0) <=> a = 0`]) THEN
    X86_SIM_TAC BIGNUM_OPTSUB_EXEC (1--3) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[COND_ID];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Main loop setup ***)

  ABBREV_TAC `p <=> ~(b:int64 = word 0)` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x11` `pc + 0x2c`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read RDX s = x /\
          read R8 s = y /\
          read R9 s = word i /\
          read RCX s = word_neg(word(bitval p)) /\
          bignum_from_memory (word_add x (word(8 * i)),k - i) s =
          highdigits m i /\
          bignum_from_memory (word_add y (word(8 * i)),k - i) s =
          highdigits n i /\
          val(word_neg(read RAX s)) <= 1 /\
          &(bignum_from_memory(z,i) s):real =
          &(lowdigits m i) - &(bitval p) * &(lowdigits n i) +
          &2 pow (64 * i) * &(val(word_neg(read RAX s)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_OPTSUB_EXEC (1--6) THEN
    REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES; BITVAL_CLAUSES] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; VAL_WORD_0; VAL_EQ_0; WORD_ADD_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0; HIGHDIGITS_0] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; LE_0] THEN REAL_ARITH_TAC;
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_OPTSUB_EXEC (1--2);
    GHOST_INTRO_TAC `cval:num` `\s. val(word_neg(read RAX s))` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `cout:bool` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
    X86_SIM_TAC BIGNUM_OPTSUB_EXEC (1--3) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `&(read (memory :> bytes (z,8 * k)) s3) =
      &(lowdigits m k) - &(bitval p) * &(lowdigits n k) +
      &2 pow (64 * k) * &(bitval cout)` THEN
    UNDISCH_THEN `~(b:int64 = word 0) <=> p` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; WORD_NEG_NEG] THEN
    ASM_CASES_TAC `b:int64 = word 0` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [ASM_CASES_TAC `cout:bool` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_MUL_RZERO; REAL_MUL_LZERO;
        REAL_ADD_LID; REAL_ADD_RID; REAL_SUB_RZERO] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ASM_SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND;
                   ARITH_RULE `a:num < e ==> ~(a = m + e * 1)`];
      REWRITE_TAC[GSYM NOT_LT; REAL_MUL_LID; COND_SWAP] THEN
      ASM_CASES_TAC `cout:bool` THEN
      ASM_SIMP_TAC[BITVAL_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THENL
       [DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
         `&x:real = m - n + p * &1 ==> &x < p ==> m < n`)) THEN
        ASM_SIMP_TAC[REAL_OF_NUM_CLAUSES; GSYM BIGNUM_FROM_MEMORY_BYTES;
                     BIGNUM_FROM_MEMORY_BOUND] THEN
        ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE
         `n:num < e ==> n <= e + m`] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
         `&x:real = m - n + p * &0 ==> ~(m < n)`)) THEN
        SIMP_TAC[] THEN
        SIMP_TAC[REAL_OF_NUM_CLAUSES; NOT_LT; REAL_OF_NUM_SUB] THEN
        ARITH_TAC]]] THEN

  (*** Proof of the main invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cval:num` `\s. val(word_neg(read RAX s))` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `cout:bool` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  X86_ACCSIM_TAC BIGNUM_OPTSUB_EXEC [5] (1--8) THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; LOWDIGITS_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[WORD_AND_MASK] THEN
  REWRITE_TAC[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
  ASM_REWRITE_TAC[VAL_WORD_BIGDIGIT; REAL_VAL_WORD_NOT; BITVAL_CLAUSES] THEN
  REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
  REAL_ARITH_TAC);;

let BIGNUM_OPTSUB_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z x p y m n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_optsub_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optsub_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; x; p; y] s /\
                  bignum_from_memory (x,val k) s = m /\
                  bignum_from_memory (y,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,val k) s =
                   if p = word 0 then m
                   else if n <= m then m - n
                   else (2 EXP (64 * val k) + m) - n) /\
                  (C_RETURN s =
                   if ~(p = word 0) /\ m < n then word 1 else word 0))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_optsub_tmc BIGNUM_OPTSUB_CORRECT);;

let BIGNUM_OPTSUB_SUBROUTINE_CORRECT = prove
 (`!k z x p y m n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_optsub_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optsub_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; x; p; y] s /\
                  bignum_from_memory (x,val k) s = m /\
                  bignum_from_memory (y,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,val k) s =
                   if p = word 0 then m
                   else if n <= m then m - n
                   else (2 EXP (64 * val k) + m) - n) /\
                  (C_RETURN s =
                   if ~(p = word 0) /\ m < n then word 1 else word 0))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OPTSUB_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_optsub_windows_mc = define_from_elf
   "bignum_optsub_windows_mc" "x86/generic/bignum_optsub.obj";;

let bignum_optsub_windows_tmc = define_trimmed "bignum_optsub_windows_tmc" bignum_optsub_windows_mc;;

let BIGNUM_OPTSUB_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x p y m n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_optsub_windows_tmc); (x,8 * val k); (y,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_optsub_windows_tmc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optsub_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; x; p; y] s /\
                  bignum_from_memory (x,val k) s = m /\
                  bignum_from_memory (y,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,val k) s =
                   if p = word 0 then m
                   else if n <= m then m - n
                   else (2 EXP (64 * val k) + m) - n) /\
                  (WINDOWS_C_RETURN s =
                   if ~(p = word 0) /\ m < n then word 1 else word 0))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_optsub_windows_tmc bignum_optsub_tmc
    BIGNUM_OPTSUB_CORRECT);;

let BIGNUM_OPTSUB_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x p y m n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_optsub_windows_mc); (x,8 * val k); (y,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_optsub_windows_mc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optsub_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; x; p; y] s /\
                  bignum_from_memory (x,val k) s = m /\
                  bignum_from_memory (y,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,val k) s =
                   if p = word 0 then m
                   else if n <= m then m - n
                   else (2 EXP (64 * val k) + m) - n) /\
                  (WINDOWS_C_RETURN s =
                   if ~(p = word 0) /\ m < n then word 1 else word 0))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OPTSUB_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

