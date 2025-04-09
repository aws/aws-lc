(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional modular negation of bignum.                                      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_modoptneg.o";;
 ****)

let bignum_modoptneg_mc =
  define_assert_from_elf "bignum_modoptneg_mc" "x86/generic/bignum_modoptneg.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x49;              (* JE (Imm8 (word 73)) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4e; 0x0b; 0x0c; 0xd9;  (* OR (% r9) (Memop Quadword (%%% (rcx,3,r11))) *)
  0x49; 0xff; 0xc3;        (* INC (% r11) *)
  0x49; 0x39; 0xfb;        (* CMP (% r11) (% rdi) *)
  0x72; 0xf4;              (* JB (Imm8 (word 244)) *)
  0x49; 0x83; 0xf9; 0x00;  (* CMP (% r9) (Imm8 (word 0)) *)
  0x49; 0x0f; 0x44; 0xd1;  (* CMOVE (% rdx) (% r9) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0x19; 0xd2;        (* SBB (% rdx) (% rdx) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x4f; 0x8b; 0x0c; 0xd8;  (* MOV (% r9) (Memop Quadword (%%% (r8,3,r11))) *)
  0x49; 0x21; 0xd1;        (* AND (% r9) (% rdx) *)
  0x4e; 0x8b; 0x14; 0xd9;  (* MOV (% r10) (Memop Quadword (%%% (rcx,3,r11))) *)
  0x49; 0x31; 0xd2;        (* XOR (% r10) (% rdx) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x4d; 0x11; 0xd1;        (* ADC (% r9) (% r10) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x4e; 0x89; 0x0c; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,r11))) (% r9) *)
  0x49; 0xff; 0xc3;        (* INC (% r11) *)
  0x49; 0x39; 0xfb;        (* CMP (% r11) (% rdi) *)
  0x72; 0xdd;              (* JB (Imm8 (word 221)) *)
  0xc3                     (* RET *)
];;

let bignum_modoptneg_tmc = define_trimmed "bignum_modoptneg_tmc" bignum_modoptneg_mc;;

let BIGNUM_MODOPTNEG_EXEC = X86_MK_CORE_EXEC_RULE bignum_modoptneg_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODOPTNEG_CORRECT = prove
 (`!k z p x m a n pc.
        nonoverlapping (word pc,0x4f) (z,8 * val k) /\
        (m = z \/ nonoverlapping (m,8 * val k) (z,8 * val k)) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_modoptneg_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [k;z;p;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = word(pc + 0x4e) /\
                  (a <= n
                   ==> bignum_from_memory(z,val k) s =
                       if p = word 0 \/ a = 0 then a else n - a))
             (MAYCHANGE [RIP; RAX; RDX; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `p:int64`; `x:int64`; `m:int64`] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `n:num`] THEN

  (*** Deal with degenerate case k = 0 first ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[CONJUNCT1 LT] THEN X86_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--2)THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** The initial zero comparison loop "cmploop" ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0xb` `pc + 0x12`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read RDX s = p /\
          read RCX s = x /\
          read R8 s = m /\
          bignum_from_memory (x,k) s = a /\
          bignum_from_memory (m,k) s = n /\
          read R11 s = word i /\
          bignum_from_memory (word_add x (word(8 * i)),k - i) s =
          highdigits a i /\
          (read R9 s = word 0 <=> lowdigits a i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--4) THEN
    REWRITE_TAC[HIGHDIGITS_0; LOWDIGITS_0; SUB_0; MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `zorro:int64` `read R9` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - i = 0 <=> ~(i < k)`] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    X86_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--2) THEN
    REWRITE_TAC[GSYM WORD_ADD; LOWDIGITS_CLAUSES] THEN
    ASM_REWRITE_TAC[WORD_OR_EQ_0; ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[WORD_EQ_0; DIMINDEX_64; BIGDIGIT_BOUND] THEN CONV_TAC TAUT;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--2);
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** The main masked addition/subtraction loop "mainloop" ***)

  ABBREV_TAC `q <=> ~(p:int64 = word 0) /\ ~(a = 0)` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x2b` `pc + 0x49`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read RDX s = word_neg(word(bitval q)) /\
          read RCX s = x /\
          read R8 s = m /\
          bignum_from_memory (word_add x (word(8 * i)),k - i) s =
          highdigits a i /\
          bignum_from_memory (word_add m (word(8 * i)),k - i) s =
          highdigits n i /\
          read R11 s = word i /\
          val(word_neg(read RAX s)) <= 1 /\
          &(bignum_from_memory(z,i) s):real =
          &2 pow (64 * i) * (&(bitval q) - &(val(word_neg(read RAX s)))) +
          &(bitval q) * &(lowdigits n i) +
          --(&1) pow bitval q * &(lowdigits a i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GHOST_INTRO_TAC `zorro:int64` `read R9` THEN
    X86_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--8) THEN
    ASM_REWRITE_TAC[WORD_UNMASK_64; VAL_WORD_0; VAL_EQ_0] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_REWRITE_TAC[MESON[] `~(if p then p else q) <=> ~q /\ ~p`] THEN
    ASM_REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; HIGHDIGITS_0; LOWDIGITS_0] THEN
    REWRITE_TAC[real_pow; BIGNUM_FROM_MEMORY_TRIVIAL; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    BOOL_CASES_TAC `q:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `cinn:num` `\s. val(word_neg(read RAX s))` THEN
    GLOBALIZE_PRECONDITION_TAC THEN FIRST_X_ASSUM
     (X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN
    REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - i = 0 <=> ~(i < k)`] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    X86_ACCSIM_TAC BIGNUM_MODOPTNEG_EXEC [6] (1--9) THEN
    REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
    REWRITE_TAC[GSYM WORD_ADD; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; LOWDIGITS_CLAUSES] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; REAL_POW_ADD] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0] THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0] THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64; VAL_WORD_BIGDIGIT] THEN
    CONV_TAC REAL_RING;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--2);
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** The finale with the case analysis ***)

  X86_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--2) THEN
  ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[LE_0; BIGNUM_FROM_MEMORY_BOUND];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a:num <= n`; `n < 2 EXP (64 * k)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_ADD_RID]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(RAND_CONV(LAND_CONV REAL_POLY_CONV)) THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_FIELD `&2 pow n * inv(&2 pow n) = &1`] THEN
  REAL_INTEGER_TAC);;

let BIGNUM_MODOPTNEG_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z p x m a n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_modoptneg_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        (m = z \/ nonoverlapping (m,8 * val k) (z,8 * val k)) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modoptneg_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;p;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a <= n
                   ==> bignum_from_memory(z,val k) s =
                       if p = word 0 \/ a = 0 then a else n - a))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_modoptneg_tmc BIGNUM_MODOPTNEG_CORRECT);;

let BIGNUM_MODOPTNEG_SUBROUTINE_CORRECT = prove
 (`!k z p x m a n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_modoptneg_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        (m = z \/ nonoverlapping (m,8 * val k) (z,8 * val k)) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modoptneg_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;p;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a <= n
                   ==> bignum_from_memory(z,val k) s =
                       if p = word 0 \/ a = 0 then a else n - a))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODOPTNEG_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_modoptneg_windows_mc = define_from_elf
   "bignum_modoptneg_windows_mc" "x86/generic/bignum_modoptneg.obj";;

let bignum_modoptneg_windows_tmc = define_trimmed "bignum_modoptneg_windows_tmc" bignum_modoptneg_windows_mc;;

let BIGNUM_MODOPTNEG_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z p x m a n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_modoptneg_windows_tmc); (x,8 * val k); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_modoptneg_windows_tmc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        (m = z \/ nonoverlapping (m,8 * val k) (z,8 * val k)) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modoptneg_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;p;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a <= n
                   ==> bignum_from_memory(z,val k) s =
                       if p = word 0 \/ a = 0 then a else n - a))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_modoptneg_windows_tmc bignum_modoptneg_tmc
    BIGNUM_MODOPTNEG_CORRECT);;

let BIGNUM_MODOPTNEG_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z p x m a n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_modoptneg_windows_mc); (x,8 * val k); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_modoptneg_windows_mc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        (m = z \/ nonoverlapping (m,8 * val k) (z,8 * val k)) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modoptneg_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;p;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a <= n
                   ==> bignum_from_memory(z,val k) s =
                       if p = word 0 \/ a = 0 then a else n - a))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODOPTNEG_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

