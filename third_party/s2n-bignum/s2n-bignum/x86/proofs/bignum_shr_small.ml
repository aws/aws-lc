(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shifting of a bignum right < 64 bits.                                     *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_shr_small.o";;
 ****)

let bignum_shr_small_mc =
  define_assert_from_elf "bignum_shr_small_mc" "x86/generic/bignum_shr_small.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x49; 0x89; 0xc9;        (* MOV (% r9) (% rcx) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x39; 0xfa;        (* CMP (% rdx) (% rdi) *)
  0x73; 0x0c;              (* JAE (Imm8 (word 12)) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x48; 0x89; 0x04; 0xfe;  (* MOV (Memop Quadword (%%% (rsi,3,rdi))) (% rax) *)
  0x48; 0x39; 0xfa;        (* CMP (% rdx) (% rdi) *)
  0x72; 0xf4;              (* JB (Imm8 (word 244)) *)
  0x74; 0x04;              (* JE (Imm8 (word 4)) *)
  0x49; 0x8b; 0x04; 0xf9;  (* MOV (% rax) (Memop Quadword (%%% (r9,3,rdi))) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x19;              (* JE (Imm8 (word 25)) *)
  0x4d; 0x8b; 0x54; 0xf9; 0xf8;
                           (* MOV (% r10) (Memop Quadword (%%%% (r9,3,rdi,-- &8))) *)
  0x4d; 0x89; 0xd0;        (* MOV (% r8) (% r10) *)
  0x49; 0x0f; 0xad; 0xc2;  (* SHRD (% r10) (% rax) (% cl) *)
  0x4c; 0x89; 0x54; 0xfe; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsi,3,rdi,-- &8))) (% r10) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xe7;              (* JNE (Imm8 (word 231)) *)
  0x41; 0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 1)) *)
  0x49; 0xd3; 0xe2;        (* SHL (% r10) (% cl) *)
  0x49; 0xff; 0xca;        (* DEC (% r10) *)
  0x4c; 0x21; 0xd0;        (* AND (% rax) (% r10) *)
  0xc3                     (* RET *)
];;

let bignum_shr_small_tmc = define_trimmed "bignum_shr_small_tmc" bignum_shr_small_mc;;

let BIGNUM_SHR_SMALL_EXEC = X86_MK_CORE_EXEC_RULE bignum_shr_small_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SHR_SMALL_CORRECT = prove
 (`!p z n x a c pc.
        nonoverlapping (word pc,0x4e) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_shr_small_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = word(pc + 0x4d) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (a DIV 2 EXP (val c MOD 64)) (val p) /\
                  C_RETURN s = word(a MOD 2 EXP (val c MOD 64)))
             (MAYCHANGE [RIP; RDI; RAX; RCX; R8; R9; R10] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `x:int64` THEN
  X_GEN_TAC `a:num` THEN W64_GEN_TAC `c:num` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Split the proof at the "nopad" label ***)

  ENSURES_SEQUENCE_TAC `pc + 0x1a`
   `\s. read RSI s = z /\
        read R9 s = x /\
        read RCX s = word c /\
        bignum_from_memory (x,n) s = a /\
        read RDI s = word(MIN n p) /\
        read RAX s = word 0 /\
        bignum_from_memory(word_add z (word(8 * n)),p - n) s = 0 /\
        (read ZF s <=> n <= p)` THEN

  CONJ_TAC THENL
   [ASM_CASES_TAC `p:num <= n` THENL
     [X86_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--5) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_EQ_0] THEN
      ASM_SIMP_TAC[WORD_SUB_EQ_0; ARITH_RULE `p <= n ==> p - n = 0`] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; GSYM VAL_EQ] THEN
      UNDISCH_TAC `p:num <= n` THEN
      ASM_SIMP_TAC[ARITH_RULE `p <= n ==> MIN n p = p`] THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN

    ENSURES_WHILE_ADOWN_TAC `p:num` `n:num` `pc + 0xe` `pc + 0x15`
     `\i s. read RSI s = z /\
            read RDX s = word n /\
            read R9 s = x /\
            read RCX s = word c /\
            bignum_from_memory (x,n) s = a /\
            read RAX s = word 0 /\
            read RDI s = word i /\
            bignum_from_memory(word_add z (word(8 * i)),p - i) s = 0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--5) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ASSUME_TAC(WORD_RULE
       `word_sub (word(i + 1)) (word 1):int64 = word i`) THEN
      X86_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--2) THEN
      ONCE_REWRITE_TAC[REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_EXPAND] THEN
      ASM_REWRITE_TAC[ARITH_RULE `p - i = 0 <=> ~(i < p)`] THEN
      REWRITE_TAC[WORD_RULE
       `word_add (word_add z (word (8 * i))) (word 8) =
        word_add z (word(8 * (i + 1)))`] THEN
      ASM_REWRITE_TAC[ARITH_RULE `p - i - 1 = p - (i + 1)`] THEN
      REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--2);

      X86_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--2) THEN
      ASM_SIMP_TAC[ARITH_RULE `n < p ==> MIN n p = n`] THEN
      ASM_REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0; LE_LT]];

    ALL_TAC] THEN

  (*** The possible initialization of the carry-in word ***)

  ENSURES_SEQUENCE_TAC `pc + 0x20`
   `\s. read RSI s = z /\
        read RDI s = word(MIN n p) /\
        read R9 s = x /\
        read RCX s = word c /\
        read RAX s = word(bigdigit a (MIN n p)) /\
        bignum_from_memory (x,MIN n p) s = lowdigits a (MIN n p) /\
        bignum_from_memory(word_add z (word(8 * MIN n p)),
                           p - MIN n p) s = 0` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n:num <= p` THENL
     [ASM_SIMP_TAC[ARITH_RULE `n <= p ==> MIN n p = n`] THEN
      X86_SIM_TAC BIGNUM_SHR_SMALL_EXEC [1] THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[BIGDIGIT_ZERO];
      ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
      ASM_SIMP_TAC[ARITH_RULE `p < n ==> MIN n p = p`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      MP_TAC(ISPECL [`n:num`; `x:int64`; `s0:x86state`; `p:num`]
        BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN STRIP_TAC THEN
      X86_STEPS_TAC BIGNUM_SHR_SMALL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "a" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
      ASM_SIMP_TAC[ARITH_RULE `p < n ==> MIN n p = p`]];
    ALL_TAC] THEN

  (*** Adopt q = min(n,p) as a new variable for brevity/convenience ***)

  MP_TAC(ARITH_RULE `MIN n p <= n /\ MIN n p <= p`) THEN
  ABBREV_TAC `q = MIN n p` THEN STRIP_TAC THEN

  (*** Deal with the part from "trivial" immediately to avoid duplication ***)

  ENSURES_SEQUENCE_TAC `pc + 0x3e`
   `\s. bignum_from_memory (z,p) s = lowdigits (a DIV 2 EXP (c MOD 64)) p /\
        read RCX s = word c /\
        read RAX s = word(bigdigit a 0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X86_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--4) THEN
    REWRITE_TAC[word_shl; VAL_WORD_1; MULT_CLAUSES] THEN
    REWRITE_TAC[VAL_WORD; ARITH_RULE `64 = 2 EXP 6 /\ 256 = 2 EXP 8`] THEN
    REWRITE_TAC[DIMINDEX_8; MOD_MOD_EXP_MIN] THEN
    CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
    REWRITE_TAC[MASK_WORD_SUB; WORD_AND_MASK_WORD; VAL_WORD] THEN
    REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `MIN 64 (c MOD 64) = c MOD 64`]] THEN

  (*** The degenerate case q = 0 ***)

  ASM_CASES_TAC `q = 0` THENL
   [ASM_REWRITE_TAC[SUB_0; MULT_CLAUSES; WORD_ADD_0] THEN
    X86_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--2) THEN
    UNDISCH_TAC `MIN n p = q` THEN
    ASM_REWRITE_TAC[ARITH_RULE `MIN n p = 0 <=> n = 0 \/ p = 0`] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[lowdigits; MULT_CLAUSES; MOD_1; EXP] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    REWRITE_TAC[DIV_0; MOD_0];
    ALL_TAC] THEN

  VAL_INT64_TAC `q:num` THEN

  ENSURES_WHILE_PDOWN_TAC `q:num` `pc + 0x25` `pc + 0x3c`
   `\i s. (read RSI s = z /\
           read RDI s = word i /\
           read R9 s = x /\
           read RCX s = word c /\
           read RAX s = word(bigdigit a i) /\
           bignum_from_memory(x,i) s = lowdigits a i /\
           bignum_from_memory (word_add z (word (8 * i)),p - i) s =
           highdigits (lowdigits (a DIV 2 EXP (c MOD 64)) p) i) /\
          (read ZF s <=> i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--2) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC HIGHDIGITS_ZERO THEN
    SUBST1_TAC(SYM(ASSUME `MIN n p = q`)) THEN REWRITE_TAC[MIN] THEN
    COND_CASES_TAC THEN REWRITE_TAC[LOWDIGITS_BOUND] THEN
    W(MP_TAC o PART_MATCH lhand LOWDIGITS_LE o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
    TRANS_TAC LET_TRANS `a:num` THEN ASM_REWRITE_TAC[DIV_LE];
    ALL_TAC; (*** The main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC BIGNUM_SHR_SMALL_EXEC [1];
    REWRITE_TAC[SUB_0; MULT_CLAUSES; WORD_ADD_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_SHR_SMALL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[HIGHDIGITS_0]] THEN

  (*** Now the core inner loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MAP_EVERY VAL_INT64_TAC [`i:num`; `i + 1`] THEN
  SUBGOAL_THEN `i:num < p` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `i:num` WORD_INDEX_WRAP) THEN DISCH_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
  X86_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--6) THEN
  REWRITE_TAC[VAL_WORD_1; EQ_ADD_RCANCEL_0] THEN
  ASM_REWRITE_TAC[WORD_RULE `word_sub (word (i + 1)) (word 1) = word i`] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
  ASM_REWRITE_TAC[ARITH_RULE `p - i = 0 <=> ~(i < p)`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `p - i - 1 = p - (i + 1)`] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add z (word (8 * i))) (word 8) =
    word_add z (word (8 * (i + 1)))`] THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; ARITH_RULE `64 = 2 EXP 6 /\ 256 = 2 EXP 8`] THEN
  REWRITE_TAC[DIMINDEX_8; MOD_MOD_EXP_MIN] THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 6 = 64`] THEN
  SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; LE_REFL] THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  GEN_REWRITE_TAC RAND_CONV [HIGHDIGITS_STEP] THEN
  REWRITE_TAC[ARITH_RULE `a + n:num = n + b <=> a = b`] THEN
  ASM_REWRITE_TAC[BIGDIGIT_LOWDIGITS] THEN
  GEN_REWRITE_TAC RAND_CONV [bigdigit] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_DIV] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ONCE_REWRITE_TAC[DIV_MOD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM highdigits] THEN
  REPLICATE_TAC 2
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP]) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; GSYM CONG] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `n divides a * b ==> (y + z:num == a * b * x + y + z) (mod n)`) THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
  ARITH_TAC);;

let BIGNUM_SHR_SMALL_NOIBT_SUBROUTINE_CORRECT = prove
 (`!p z n x a c pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_shr_small_tmc) (z,8 * val p) /\
        nonoverlapping (stackpointer,8) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_shr_small_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (a DIV 2 EXP (val c MOD 64)) (val p) /\
                  C_RETURN s = word(a MOD 2 EXP (val c MOD 64)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_shr_small_tmc BIGNUM_SHR_SMALL_CORRECT);;

let BIGNUM_SHR_SMALL_SUBROUTINE_CORRECT = prove
 (`!p z n x a c pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_shr_small_mc) (z,8 * val p) /\
        nonoverlapping (stackpointer,8) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_shr_small_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (a DIV 2 EXP (val c MOD 64)) (val p) /\
                  C_RETURN s = word(a MOD 2 EXP (val c MOD 64)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SHR_SMALL_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_shr_small_windows_mc = define_from_elf
   "bignum_shr_small_windows_mc" "x86/generic/bignum_shr_small.obj";;

let bignum_shr_small_windows_tmc = define_trimmed "bignum_shr_small_windows_tmc" bignum_shr_small_windows_mc;;

let BIGNUM_SHR_SMALL_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z n x a c pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_shr_small_windows_tmc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_shr_small_windows_tmc) (z,8 * val p) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_shr_small_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (a DIV 2 EXP (val c MOD 64)) (val p) /\
                  WINDOWS_C_RETURN s = word(a MOD 2 EXP (val c MOD 64)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_shr_small_windows_tmc bignum_shr_small_tmc
    BIGNUM_SHR_SMALL_CORRECT);;

let BIGNUM_SHR_SMALL_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z n x a c pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_shr_small_windows_mc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_shr_small_windows_mc) (z,8 * val p) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_shr_small_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (a DIV 2 EXP (val c MOD 64)) (val p) /\
                  WINDOWS_C_RETURN s = word(a MOD 2 EXP (val c MOD 64)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SHR_SMALL_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

