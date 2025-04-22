(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of Montgomery representation modulo p_384.                    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p384/bignum_demont_p384.o";;
 ****)

let bignum_demont_p384_mc =
  define_assert_from_elf "bignum_demont_p384_mc" "x86/p384/bignum_demont_p384.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x8b; 0x66; 0x20;  (* MOV (% r12) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x8b; 0x6e; 0x28;  (* MOV (% r13) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x89; 0xc2;        (* MOV (% rdx) (% r8) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc2;        (* ADD (% rdx) (% r8) *)
  0x48; 0x31; 0xf6;        (* XOR (% rsi) (% rsi) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0xbb; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r8) (% rdx,% rcx) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xf3;        (* SBB (% r11) (% rsi) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xca;        (* MOV (% rdx) (% r9) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xca;        (* ADD (% rdx) (% r9) *)
  0x48; 0x31; 0xf6;        (* XOR (% rsi) (% rsi) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0xb3; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r9) (% rdx,% rcx) *)
  0x4c; 0x11; 0xc8;        (* ADC (% rax) (% r9) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xf4;        (* SBB (% r12) (% rsi) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd2;        (* MOV (% rdx) (% r10) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd2;        (* ADD (% rdx) (% r10) *)
  0x48; 0x31; 0xf6;        (* XOR (% rsi) (% rsi) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0xab; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r10) (% rdx,% rcx) *)
  0x4c; 0x11; 0xd0;        (* ADC (% rax) (% r10) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xcc;        (* SBB (% r12) (% rcx) *)
  0x49; 0x19; 0xf5;        (* SBB (% r13) (% rsi) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xda;        (* ADD (% rdx) (% r11) *)
  0x48; 0x31; 0xf6;        (* XOR (% rsi) (% rsi) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0xa3; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r11) (% rdx,% rcx) *)
  0x4c; 0x11; 0xd8;        (* ADC (% rax) (% r11) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc4;        (* SUB (% r12) (% rax) *)
  0x49; 0x19; 0xcd;        (* SBB (% r13) (% rcx) *)
  0x49; 0x19; 0xf0;        (* SBB (% r8) (% rsi) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xe2;        (* MOV (% rdx) (% r12) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe2;        (* ADD (% rdx) (% r12) *)
  0x48; 0x31; 0xf6;        (* XOR (% rsi) (% rsi) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0x9b; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r12) (% rdx,% rcx) *)
  0x4c; 0x11; 0xe0;        (* ADC (% rax) (% r12) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc5;        (* SUB (% r13) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xf1;        (* SBB (% r9) (% rsi) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xea;        (* ADD (% rdx) (% r13) *)
  0x48; 0x31; 0xf6;        (* XOR (% rsi) (% rsi) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0x93; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r13) (% rdx,% rcx) *)
  0x4c; 0x11; 0xe8;        (* ADC (% rax) (% r13) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xf2;        (* SBB (% r10) (% rsi) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0xc3                     (* RET *)
];;

let bignum_demont_p384_tmc = define_trimmed "bignum_demont_p384_tmc" bignum_demont_p384_mc;;

let BIGNUM_DEMONT_P384_EXEC = X86_MK_CORE_EXEC_RULE bignum_demont_p384_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let swlemma = WORD_RULE
  `word_add (word_shl x 32) x:int64 = word(4294967297 * val x)`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &(val(word(4294967297 * val x):int64)) * &18446744069414584321
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(4294967297 * val x):int64)) * &18446744069414584321`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let trivsublemma = prove
 (`word_sub (word 0) (word (0 + bitval c)) = word_neg(word(bitval c))`,
  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC WORD_RULE);;

let BIGNUM_DEMONT_P384_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x1e7) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_demont_p384_tmc) /\
                  read RIP s = word(pc + 0x04) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = word (pc + 0x1e2) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a) MOD p_384))
             (MAYCHANGE [RIP; RSI; RAX; RCX; RDX;
                         R8; R9; R10; R11; R12; R13] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  MAP_EVERY (fun s ->
    X86_SINGLE_STEP_TAC BIGNUM_DEMONT_P384_EXEC s THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[trivsublemma]) THEN
    TRY(ACCUMULATE_ARITH_TAC s) THEN CLARIFY_TAC)
   (statenames "s" (1--120)) THEN

  (*** Do the congruential reasoning on the chosen multipliers ***)

  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Now finish the proof directly ***)

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(2 EXP 384 * t <= (2 EXP 384 - 1) * p_384 + a /\
     (2 EXP 384 * t == a) (mod p_384)
     ==> t = (inverse_mod p_384 (2 EXP 384) * a) MOD p_384) /\
    2 EXP 384 * t <= (2 EXP 384 - 1) * p_384 + a /\
    (2 EXP 384 * t == a) (mod p_384)
    ==> t = (inverse_mod p_384 (2 EXP 384) * a) MOD p_384`) THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM NOT_LT]) THEN
      UNDISCH_TAC `a < p_384` THEN REWRITE_TAC[p_384] THEN ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(NUMBER_RULE
       `(e * t == a) (mod p)
        ==> (e * i == 1) (mod p) ==> (i * a == t) (mod p)`)) THEN
      REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
      REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  EXPAND_TAC "a" THEN
  REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_EQ_CONV) THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a:real <= b + c <=> a - c <= b`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; REAL_INTEGER_TAC]);;

let BIGNUM_DEMONT_P384_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 16),24) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_demont_p384_tmc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_demont_p384_tmc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_demont_p384_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a) MOD p_384))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 16),16)])`,
  X86_PROMOTE_RETURN_STACK_TAC
   bignum_demont_p384_tmc BIGNUM_DEMONT_P384_CORRECT
   `[R12; R13]` 16);;

let BIGNUM_DEMONT_P384_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 16),24) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_demont_p384_mc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_demont_p384_mc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_demont_p384_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a) MOD p_384))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DEMONT_P384_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_demont_p384_windows_mc = define_from_elf
   "bignum_demont_p384_windows_mc" "x86/p384/bignum_demont_p384.obj";;

let bignum_demont_p384_windows_tmc = define_trimmed "bignum_demont_p384_windows_tmc" bignum_demont_p384_windows_mc;;

let BIGNUM_DEMONT_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 32),40) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_demont_p384_windows_tmc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_demont_p384_windows_tmc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_demont_p384_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a) MOD p_384))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 32),32)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   bignum_demont_p384_windows_tmc bignum_demont_p384_tmc
   BIGNUM_DEMONT_P384_CORRECT `[R12; R13]` 16);;

let BIGNUM_DEMONT_P384_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 32),40) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_demont_p384_windows_mc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_demont_p384_windows_mc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_demont_p384_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a) MOD p_384))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DEMONT_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

