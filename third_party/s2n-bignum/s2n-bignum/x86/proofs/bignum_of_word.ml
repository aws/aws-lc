(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a single word (digit) to a bignum.                          *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_of_word.o";;
 ****)

let bignum_of_word_mc =
  define_assert_from_elf "bignum_of_word_mc" "x86/generic/bignum_of_word.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x14;              (* JE (Imm8 (word 20)) *)
  0x48; 0x89; 0x16;        (* MOV (Memop Quadword (%% (rsi,0))) (% rdx) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x74; 0x0c;              (* JE (Imm8 (word 12)) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x48; 0x89; 0x14; 0xfe;  (* MOV (Memop Quadword (%%% (rsi,3,rdi))) (% rdx) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xf7;              (* JNE (Imm8 (word 247)) *)
  0xc3                     (* RET *)
];;

let bignum_of_word_tmc = define_trimmed "bignum_of_word_tmc" bignum_of_word_mc;;

let BIGNUM_OF_WORD_EXEC = X86_MK_CORE_EXEC_RULE bignum_of_word_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_OF_WORD_CORRECT = prove
 (`!k z n pc.
        nonoverlapping (word pc,0x1a) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_of_word_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [k; z; n] s)
             (\s. read RIP s = word (pc + 0x19) /\
                  bignum_from_memory (z,val k) s =
                  val n MOD (2 EXP (64 * val k)))
         (MAYCHANGE [RIP; RDX; RDI] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    X86_SIM_TAC BIGNUM_OF_WORD_EXEC (1--2) THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];
    ALL_TAC] THEN

  ASM_CASES_TAC `k = 1` THENL
   [X86_SIM_TAC BIGNUM_OF_WORD_EXEC (1--5) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[BIGNUM_FROM_MEMORY_SING; MULT_CLAUSES; MOD_LT];
    ALL_TAC] THEN

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

  ENSURES_WHILE_PADOWN_TAC `k:num` `1` `pc + 0x10` `pc + 0x17`
   `\i s. (read RSI s = z /\
           read RDX s = word 0 /\
           read RDI s = word(i - 1) /\
           read (memory :> bytes64 z) s = word n /\
           bignum_from_memory(word_add z (word(8 * i)),k - i) s = 0) /\
          (read ZF s <=> i = 1)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0) /\ ~(k = 1)`];
    MP_TAC(ISPECL [`word k:int64`; `word 1:int64`] VAL_WORD_SUB_EQ_0) THEN
    ASM_REWRITE_TAC[VAL_WORD_1] THEN DISCH_TAC THEN
    X86_SIM_TAC BIGNUM_OF_WORD_EXEC (1--6) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; WORD_SUB; LE_1];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    VAL_INT64_TAC `i:num` THEN REWRITE_TAC[ADD_SUB] THEN
    X86_SIM_TAC BIGNUM_OF_WORD_EXEC (1--2) THEN
    ASM_SIMP_TAC[WORD_SUB; LE_1; VAL_WORD_1] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
    ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_add z (word (8 * i))) (word 8) =
      word_add z (word (8 * (i + 1)))`] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; MULT_CLAUSES];
    REPEAT STRIP_TAC THEN X86_SIM_TAC BIGNUM_OF_WORD_EXEC [1];
    X86_SIM_TAC BIGNUM_OF_WORD_EXEC [1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES; MULT_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP 64` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC]);;

let BIGNUM_OF_WORD_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_of_word_tmc) (z,8 * val k) /\
        nonoverlapping (z,8 * val k) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_of_word_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; n] s)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  val n MOD (2 EXP (64 * val k)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_of_word_tmc BIGNUM_OF_WORD_CORRECT);;

let BIGNUM_OF_WORD_SUBROUTINE_CORRECT = prove
 (`!k z n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_of_word_mc) (z,8 * val k) /\
        nonoverlapping (z,8 * val k) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_of_word_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; n] s)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  val n MOD (2 EXP (64 * val k)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OF_WORD_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_of_word_windows_mc = define_from_elf
   "bignum_of_word_windows_mc" "x86/generic/bignum_of_word.obj";;

let bignum_of_word_windows_tmc = define_trimmed "bignum_of_word_windows_tmc" bignum_of_word_windows_mc;;

let BIGNUM_OF_WORD_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_of_word_windows_tmc)] /\
        nonoverlapping (word pc,LENGTH bignum_of_word_windows_tmc) (z,8 * val k) /\
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 16),24)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_of_word_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; n] s)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  val n MOD (2 EXP (64 * val k)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_of_word_windows_tmc bignum_of_word_tmc
    BIGNUM_OF_WORD_CORRECT);;

let BIGNUM_OF_WORD_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_of_word_windows_mc)] /\
        nonoverlapping (word pc,LENGTH bignum_of_word_windows_mc) (z,8 * val k) /\
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 16),24)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_of_word_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; n] s)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  val n MOD (2 EXP (64 * val k)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OF_WORD_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

