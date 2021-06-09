(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Tripling modulo p_384, the field characteristic for the NIST P-384 curve. *)
(* ========================================================================= *)

(**** print_literal_from_elf "X86/p384/bignum_triple_p384.o";;
 ****)

let bignum_triple_p384_mc = define_assert_from_elf "bignum_triple_p384_mc" "X86/p384/bignum_triple_p384.o"
[
  0x53;                    (* PUSH (% rbx) *)
  0xba; 0x03; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 3)) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0e;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x48; 0x11; 0xc3;        (* ADC (% rbx) (% rax) *)
  0xc4; 0xe2; 0xcb; 0xf6; 0x56; 0x28;
                           (* MULX4 (% rdx,% rsi) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x48; 0x11; 0xce;        (* ADC (% rsi) (% rcx) *)
  0x48; 0x83; 0xd2; 0x01;  (* ADC (% rdx) (Imm8 (word 1)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xc1; 0xe1; 0x20;  (* SHL (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0x29; 0xc8;        (* SUB (% rax) (% rcx) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd3; 0x00;  (* ADC (% rbx) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd1;        (* NOT (% rcx) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x21; 0xca;        (* AND (% rdx) (% rcx) *)
  0x48; 0x29; 0xd0;        (* SUB (% rax) (% rdx) *)
  0x48; 0x83; 0xe1; 0x01;  (* AND (% rcx) (Imm8 (word 1)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x5f; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rbx) *)
  0x48; 0x83; 0xde; 0x00;  (* SBB (% rsi) (Imm8 (word 0)) *)
  0x48; 0x89; 0x77; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rsi) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let BIGNUM_TRIPLE_P384_EXEC = X86_MK_EXEC_RULE bignum_triple_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let p384genshortredlemma = prove
 (`!n. n < 3 * 2 EXP 384
       ==> let q = (n DIV 2 EXP 384) + 1 in
           q <= 3 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

let BIGNUM_TRIPLE_P384_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0xa8) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p384_mc /\
                  read RIP s = word(pc + 0x1) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = word (pc + 0xa6) /\
                  bignum_from_memory (z,6) s = (3 * n) MOD p_384)
             (MAYCHANGE [RIP; RSI; RAX; RCX; RDX; R8; R9; R10; R11; RBX] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `6` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN

  (*** Input load and initial multiplication by 3 ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P384_EXEC (1--13) (1--13) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [mullo_s2; sum_s4; sum_s6; sum_s8; sum_s10; sum_s12; sum_s13] =
    2 EXP 384 + 3 * n`
  ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = (3 * n) DIV 2 EXP 384` THEN
  SUBGOAL_THEN `h < 3` ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 6)` THEN EXPAND_TAC "h" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s13:int64 = word(h + 1)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[ARITH_RULE
     `(3 * n) DIV 2 EXP 384 + 1 = (2 EXP 384 + 3 * n) DIV 2 EXP 384`] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[ARITH_RULE `384 = 64 + 64 + 64 + 64 + 64 + 64`] THEN
    REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_DIV; BIGNUM_OF_WORDLIST_SING; WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `3 * n` p384genshortredlemma) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 6)` THEN ARITH_TAC;
    CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Computation of 3 * n - (h + 1) * p_384 ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P384_EXEC (19--24) (14--26) THEN
  MP_TAC(SPECL
   [`word_neg(word(bitval(~carry_s24))):int64`;
    `&(bignum_of_wordlist
        [sum_s19; sum_s20; sum_s21; sum_s22; sum_s23; sum_s24]):real`;
    `384`; `3 * n`; `(h + 1) * p_384`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_384 <= 3 * n + p_384`;
        `3 * n < (h + 1) * p_384 + p_384`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC
     `bignum_of_wordlist
      [mullo_s2; sum_s4; sum_s6; sum_s8; sum_s10; sum_s12; word (h + 1)] =
      2 EXP 384 + 3 * n` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `a:real = b + x ==> x = a - b`)) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 3` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[REAL_VAL_WORD_MASK; REAL_BITVAL_NOT; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    GEN_REWRITE_TAC (funpow 3 LAND_CONV) [GSYM WORD_NOT_MASK] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P384_EXEC [32;34;36;38;40;42] (27--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `384`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> 3 * n < (h + 1) * p_384` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &(3 * n) - y + z ==> &(3 * n) = x + y - z`)) THEN
  REWRITE_TAC[p_384] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_TRIPLE_P384_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 8),8) (x,8 * 6) /\
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 8),16) /\
        ALL (nonoverlapping (word pc,0xa8))
            [(z,8 * 6); (word_sub stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p384_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,6) s = (3 * n) MOD p_384)
             (MAYCHANGE [RIP; RSP; RSI; RAX; RCX; RDX; R8; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,6);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`,
  X86_ADD_RETURN_STACK_TAC
    BIGNUM_TRIPLE_P384_EXEC BIGNUM_TRIPLE_P384_CORRECT
    `[RBX]` 8);;
