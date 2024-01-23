(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Deduce if a bignum is zero.                                               *)
(* ========================================================================= *)

(**** print_literal_from_elf "x86/generic/bignum_nonzero.o";;
 ****)

let bignum_nonzero_mc =
  define_assert_from_elf "bignum_nonzero_mc" "x86/generic/bignum_nonzero.o"
[
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x13;              (* JE (Imm8 (word 19)) *)
  0x48; 0x0b; 0x44; 0xfe; 0xf8;
                           (* OR (% rax) (Memop Quadword (%%%% (rsi,3,rdi,-- &8))) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xf6;              (* JNE (Imm8 (word 246)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0xc3                     (* RET *)
];;

let BIGNUM_NONZERO_EXEC = X86_MK_CORE_EXEC_RULE bignum_nonzero_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_NONZERO_CORRECT = prove
 (`!k a x pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST bignum_nonzero_mc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s'. read RIP s' = word(pc + 0x1b) /\
                C_RETURN s' = if ~(x = 0) then word 1 else word 0)
          (MAYCHANGE [RIP; RAX; RDI] ,,
           MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; BIGNUM_NONZERO_EXEC] THEN
  BIGNUM_RANGE_TAC "k" "x" THEN

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    X86_SIM_TAC BIGNUM_NONZERO_EXEC (1--3);
    ALL_TAC] THEN

  ENSURES_WHILE_PDOWN_TAC `k:num` `pc + 0x08` `pc + 0x10`
   `\i s. (bignum_from_memory (a,i) s = lowdigits x i /\
           read RSI s = a /\
           read RDI s = word i /\
           (read RAX s = word 0 <=> highdigits x i = 0)) /\
          (read ZF s <=> i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO] THEN
    X86_SIM_TAC BIGNUM_NONZERO_EXEC (1--3);
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i + 1` THEN
    GHOST_INTRO_TAC `d:int64` `read RAX` THEN
    MP_TAC(SPEC `i:num` WORD_INDEX_WRAP) THEN DISCH_TAC THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
    X86_SIM_TAC BIGNUM_NONZERO_EXEC (1--2) THEN
    REWRITE_TAC[WORD_OR_EQ_0; VAL_WORD_1] THEN REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC; ARITH_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [HIGHDIGITS_STEP] THEN
    ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_0; VAL_WORD_BIGDIGIT];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN X86_SIM_TAC BIGNUM_NONZERO_EXEC [1];
    X86_SIM_TAC BIGNUM_NONZERO_EXEC (1--4) THEN
    ASM_REWRITE_TAC[HIGHDIGITS_0; WORD_NEG_NEG; WORD_BITVAL]]);;

let BIGNUM_NONZERO_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_nonzero_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s'. read RIP s' = returnaddress /\
                read RSP s' = word_add stackpointer (word 8) /\
                C_RETURN s' = if ~(x = 0) then word 1 else word 0)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_nonzero_mc BIGNUM_NONZERO_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let windows_bignum_nonzero_mc = define_from_elf
   "windows_bignum_nonzero_mc" "x86/generic/bignum_nonzero.obj";;

let WINDOWS_BIGNUM_NONZERO_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,0x26); (a,8 * val k)]
        ==> ensures x86
              (\s. bytes_loaded s (word pc) windows_bignum_nonzero_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [k;a] s /\
                   bignum_from_memory(a,val k) s = x)
              (\s'. read RIP s' = returnaddress /\
                    read RSP s' = word_add stackpointer (word 8) /\
                    WINDOWS_C_RETURN s' = if ~(x = 0) then word 1 else word 0)
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC windows_bignum_nonzero_mc bignum_nonzero_mc
    BIGNUM_NONZERO_CORRECT);;
