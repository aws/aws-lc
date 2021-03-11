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
(* Multiplexing for raw bignums with same length.                            *)
(* ========================================================================= *)

(**** print_literal_from_elf "X86/bignum_mux.o";;
 ****)

let bignum_mux_mc =
  define_assert_from_elf "bignum_mux_mc" "X86/bignum_mux.o"
[
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x74; 0x2c;              (* JE (Imm8 (word 44)) *)
  0x48; 0xf7; 0xdf;        (* NEG (% rdi) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x4d; 0x89; 0xca;        (* MOV (% r10) (% r9) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4a; 0x8b; 0x04; 0xd9;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r11))) *)
  0x4b; 0x8b; 0x3c; 0xd8;  (* MOV (% rdi) (Memop Quadword (%%% (r8,3,r11))) *)
  0x4c; 0x21; 0xc8;        (* AND (% rax) (% r9) *)
  0x4c; 0x21; 0xd7;        (* AND (% rdi) (% r10) *)
  0x48; 0x09; 0xf8;        (* OR (% rax) (% rdi) *)
  0x4a; 0x89; 0x04; 0xda;  (* MOV (Memop Quadword (%%% (rdx,3,r11))) (% rax) *)
  0x49; 0xff; 0xc3;        (* INC (% r11) *)
  0x49; 0x39; 0xf3;        (* CMP (% r11) (% rsi) *)
  0x72; 0xe3;              (* JB (Imm8 (word 227)) *)
  0xc3                     (* RET *)
];;

let BIGNUM_MUX_EXEC = X86_MK_EXEC_RULE bignum_mux_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUX_CORRECT = prove
 (`!b k x y z m n pc.
     nonoverlapping (word pc,0x32) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
     (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_mc /\
                read RIP s = word pc /\
                C_ARGUMENTS [b; k; z; x; y] s /\
                bignum_from_memory (x,val k) s = m /\
                bignum_from_memory (y,val k) s = n)
           (\s. read RIP s =
                word (pc + 0x31) /\
                bignum_from_memory (z,val k) s =
                  if ~(b = word 0) then m else n)
          (MAYCHANGE [RIP; RAX; RDI; R9; R10; R11] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; BIGNUM_MUX_EXEC] THEN
  MAP_EVERY W64_GEN_TAC [`b:num`; `k:num`] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_RANGE_TAC "k") ["m"; "n"] THEN

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; COND_ID] THEN
    X86_SIM_TAC BIGNUM_MUX_EXEC (1--2);
    ALL_TAC] THEN

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x14` `pc + 0x2c`
   `\i s. read RCX s = x /\
          read R8 s = y /\
          read RDX s = z /\
          read RSI s = word k /\
          read R11 s = word i /\
          read R9 s = word_neg(word(bitval(~(b = 0)))) /\
          read R10 s = word_neg(word(bitval(b = 0))) /\
          bignum_from_memory(z,i) s = lowdigits (if b = 0 then n else m) i /\
          bignum_from_memory(word_add x (word(8 * i)),k - i) s =
          highdigits m i /\
          bignum_from_memory(word_add y (word(8 * i)),k - i) s =
          highdigits n i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_MUX_EXEC (1--7) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_0; LOWDIGITS_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; HIGHDIGITS_0] THEN
    ASM_REWRITE_TAC[WORD_ADD_0; BIGNUM_FROM_MEMORY_BYTES; MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0; WORD_NOT_MASK];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    X86_SIM_TAC BIGNUM_MUX_EXEC (1--7) THEN
    REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM WORD_ADD; WORD_AND_MASK] THEN
    ASM_CASES_TAC `b = 0` THEN
    ASM_REWRITE_TAC[WORD_OR_0; VAL_WORD_BIGDIGIT] THEN ARITH_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_MUX_EXEC (1--2);

    X86_SIM_TAC BIGNUM_MUX_EXEC (1--2) THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[LOWDIGITS_SELF]]);;

let BIGNUM_MUX_SUBROUTINE_CORRECT = prove
 (`!b k x y z m n pc stackpointer returnaddress.
     nonoverlapping (word pc,0x32) (z,8 * val k) /\
     nonoverlapping (stackpointer,8) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
     (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [b; k; z; x; y] s /\
                bignum_from_memory (x,val k) s = m /\
                bignum_from_memory (y,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s =
                  if ~(b = word 0) then m else n)
          (MAYCHANGE [RIP; RSP; RAX; RDI; R9; R10; R11] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_ADD_RETURN_NOSTACK_TAC BIGNUM_MUX_EXEC BIGNUM_MUX_CORRECT);;
