(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiply by 10 and add another word.                                      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_muladd10.o";;
 ****)

let bignum_muladd10_mc =
  define_assert_from_elf "bignum_muladd10_mc" "x86/generic/bignum_muladd10.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x26;              (* JE (Imm8 (word 38)) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x41; 0xb9; 0x0a; 0x00; 0x00; 0x00;
                           (* MOV (% r9d) (Imm32 (word 10)) *)
  0x4a; 0x8b; 0x04; 0xc6;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,r8))) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x4a; 0x89; 0x04; 0xc6;  (* MOV (Memop Quadword (%%% (rsi,3,r8))) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x49; 0x39; 0xf8;        (* CMP (% r8) (% rdi) *)
  0x72; 0xe3;              (* JB (Imm8 (word 227)) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0xc3                     (* RET *)
];;

let bignum_muladd10_tmc = define_trimmed "bignum_muladd10_tmc" bignum_muladd10_mc;;

let BIGNUM_MULADD10_EXEC = X86_MK_CORE_EXEC_RULE bignum_muladd10_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MULADD10_CORRECT = time prove
 (`!k z d n pc.
        nonoverlapping (word pc,0x32) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_muladd10_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [k; z; d] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read RIP s = word (pc + 0x31) /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (10 * n + val d) (val k) /\
                  C_RETURN s = word(highdigits (10 * n + val d) (val k)))
              (MAYCHANGE [RIP; RDI; RAX; RCX; RDX; R8; R9] ,,
               MAYCHANGE SOME_FLAGS ,,
               MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN W64_GEN_TAC `d:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Degenerate case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    X86_SIM_TAC BIGNUM_MULADD10_EXEC (1--4) THEN
    ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; ADD_CLAUSES; MULT_CLAUSES];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** Setup of the loop ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x11` `pc + 0x29`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read R9 s = word 10 /\
          read R8 s = word i /\
          2 EXP (64 * i) * val(read RCX s) + bignum_from_memory(z,i) s =
          10 * lowdigits n i + d /\
          bignum_from_memory(word_add z (word (8 * i)),k - i) s =
          highdigits n i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_MULADD10_EXEC (1--5) THEN
    ASM_SIMP_TAC[LOWDIGITS_0; HIGHDIGITS_0; SUB_0] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; WORD_ADD_0] THEN ARITH_TAC;
    ALL_TAC; (*** The main loop invariant ***)
    REPEAT STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_MULADD10_EXEC (1--2);
    GHOST_INTRO_TAC `c:num` `\s. val(read RCX s)` THEN
    GHOST_INTRO_TAC `l:num` `bignum_from_memory(z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `l:num` THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; VAL_WORD_GALOIS; DIMINDEX_64] THEN
    X86_SIM_TAC BIGNUM_MULADD10_EXEC (1--3) THEN
    UNDISCH_THEN `2 EXP (64 * k) * c + l = 10 * n + d` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[lowdigits; highdigits; MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0;
                 MOD_LT; DIV_LT; ARITH_EQ; ADD_CLAUSES]] THEN

  (*** The loop invariant, starting with tweaking then simulation ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `c:num` `\s. val(read RCX s)` THEN
  GHOST_INTRO_TAC `l:num` `bignum_from_memory(z,i)` THEN
  BIGNUM_TERMRANGE_TAC `i:num` `l:num` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  X86_ACCSIM_TAC BIGNUM_MULADD10_EXEC [2;3;5] (1--7) THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * (i + 2))` THEN
  REWRITE_TAC[EXP_ADD; LEFT_ADD_DISTRIB] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `l < e /\ e * (2 EXP 64 * s + t + 1) <= e * 2 EXP 128
      ==> (e * 2 EXP 64) * s + l + e * t < e * 2 EXP 128`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    ASM BOUNDER_TAC[];
    MATCH_MP_TAC(ARITH_RULE
     `l < 2 EXP 64 * e /\ d < 2 EXP 64 /\ 2 EXP 64 * 1 <= 2 EXP 64 * e
      ==> 10 * l + d < e * 2 EXP 128`) THEN
    ASM_SIMP_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; LE_1] THEN
    REWRITE_TAC[GSYM EXP_ADD; ARITH_RULE `64 + 64 * i = 64 * (i + 1)`] THEN
    REWRITE_TAC[LOWDIGITS_BOUND];
    REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE
     `10 * (e * h + l) + d = e * 10 * h + 10 * l + d`]] THEN
  SUBST1_TAC(SYM(ASSUME`2 EXP (64 * i) * c + l = 10 * lowdigits n i + d`)) THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(w * s + t == 10 * d + c) (mod ww)
    ==> ((e * w) * s + l + e * t ==
         e * 10 * d + e * c + l) (mod (e * ww))`) THEN
  ONCE_REWRITE_TAC[GSYM VAL_WORD_BIGDIGIT] THEN
  REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN REAL_INTEGER_TAC);;

let BIGNUM_MULADD10_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!k z d n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_muladd10_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_muladd10_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; d] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (10 * n + val d) (val k) /\
                  C_RETURN s = word(highdigits (10 * n + val d) (val k)))
              (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_muladd10_tmc BIGNUM_MULADD10_CORRECT);;

let BIGNUM_MULADD10_SUBROUTINE_CORRECT = time prove
 (`!k z d n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_muladd10_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_muladd10_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; d] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (10 * n + val d) (val k) /\
                  C_RETURN s = word(highdigits (10 * n + val d) (val k)))
              (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MULADD10_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_muladd10_windows_mc = define_from_elf
   "bignum_muladd10_windows_mc" "x86/generic/bignum_muladd10.obj";;

let bignum_muladd10_windows_tmc = define_trimmed "bignum_muladd10_windows_tmc" bignum_muladd10_windows_mc;;

let BIGNUM_MULADD10_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z d n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_muladd10_windows_tmc) (z,8 * val k) /\
      ALL (nonoverlapping (word_sub stackpointer (word 16),24))
          [(word pc,LENGTH bignum_muladd10_windows_tmc); (z,8 * val k)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_muladd10_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [k; z; d] s /\
                bignum_from_memory (z,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory(z,val k) s =
                lowdigits (10 * n + val d) (val k) /\
                WINDOWS_C_RETURN s =
                word(highdigits (10 * n + val d) (val k)))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,val k);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_muladd10_windows_tmc bignum_muladd10_tmc
    BIGNUM_MULADD10_CORRECT);;

let BIGNUM_MULADD10_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z d n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_muladd10_windows_mc) (z,8 * val k) /\
      ALL (nonoverlapping (word_sub stackpointer (word 16),24))
          [(word pc,LENGTH bignum_muladd10_windows_mc); (z,8 * val k)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_muladd10_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [k; z; d] s /\
                bignum_from_memory (z,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory(z,val k) s =
                lowdigits (10 * n + val d) (val k) /\
                WINDOWS_C_RETURN s =
                word(highdigits (10 * n + val d) (val k)))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,val k);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MULADD10_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

