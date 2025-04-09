(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time digit selection from bignum.                                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_digit.o";;
 ****)

let bignum_digit_mc =
  define_assert_from_elf "bignum_digit_mc" "x86/generic/bignum_digit.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x16;              (* JE (Imm8 (word 22)) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x4c; 0x8b; 0x04; 0xce;  (* MOV (% r8) (Memop Quadword (%%% (rsi,3,rcx))) *)
  0x48; 0x39; 0xd1;        (* CMP (% rcx) (% rdx) *)
  0x49; 0x0f; 0x44; 0xc0;  (* CMOVE (% rax) (% r8) *)
  0x48; 0xff; 0xc1;        (* INC (% rcx) *)
  0x48; 0x39; 0xf9;        (* CMP (% rcx) (% rdi) *)
  0x72; 0xed;              (* JB (Imm8 (word 237)) *)
  0xc3                     (* RET *)
];;

let bignum_digit_tmc = define_trimmed "bignum_digit_tmc" bignum_digit_mc;;

let BIGNUM_DIGIT_EXEC = X86_MK_CORE_EXEC_RULE bignum_digit_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_DIGIT_CORRECT = prove
 (`!k x n a pc.
        ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST bignum_digit_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [k;x;n] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read RIP s = word(pc + 0x1e) /\
              C_RETURN s = word(bigdigit a (val n)))
         (MAYCHANGE [RIP; RAX; RCX; R8] ,,
          MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `x:int64` THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `a:num` THEN

  (*** The trivial case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_DIGIT_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[BIGDIGIT_0];
    ALL_TAC] THEN

  (*** Main loop setup ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0xb` `pc + 0x19`
   `\i s. read RDI s = word k /\
          read RSI s = x /\
          read RDX s = word n /\
          read RAX s = word(bigdigit (lowdigits a i) n) /\
          read RCX s = word i /\
          bignum_from_memory(word_add x (word(8 * i)),k - i) s =
          highdigits a i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; LOWDIGITS_0; BIGDIGIT_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_DIGIT_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[HIGHDIGITS_0];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_DIGIT_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_DIGIT_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** Main loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_DIGIT_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; VAL_EQ_0; WORD_SUB_EQ_0] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM COND_RAND] THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[GSYM VAL_EQ; BIGDIGIT_LOWDIGITS] THEN
  ASM_CASES_TAC `i:num = n` THEN ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n < i + 1 <=> n < i \/ n = i`]);;

let BIGNUM_DIGIT_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k x n a pc stackpointer returnaddress.
        ensures x86
         (\s. bytes_loaded s (word pc) bignum_digit_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [k;x;n] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s = word(bigdigit a (val n)))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_digit_tmc BIGNUM_DIGIT_CORRECT);;

let BIGNUM_DIGIT_SUBROUTINE_CORRECT = prove
 (`!k x n a pc stackpointer returnaddress.
        ensures x86
         (\s. bytes_loaded s (word pc) bignum_digit_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [k;x;n] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s = word(bigdigit a (val n)))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DIGIT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_digit_windows_mc = define_from_elf
   "bignum_digit_windows_mc" "x86/generic/bignum_digit.obj";;

let bignum_digit_windows_tmc = define_trimmed "bignum_digit_windows_tmc" bignum_digit_windows_mc;;

let BIGNUM_DIGIT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k x n a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_digit_windows_tmc); (x,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_digit_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;x;n] s /\
                  bignum_from_memory (x,val k) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  WINDOWS_C_RETURN s = word(bigdigit a (val n)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_digit_windows_tmc bignum_digit_tmc
    BIGNUM_DIGIT_CORRECT);;

let BIGNUM_DIGIT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k x n a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_digit_windows_mc); (x,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_digit_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;x;n] s /\
                  bignum_from_memory (x,val k) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  WINDOWS_C_RETURN s = word(bigdigit a (val n)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DIGIT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

