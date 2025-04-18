(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shifting of a bignum left < 64 bits.                                      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_shl_small.o";;
 ****)

let bignum_shl_small_mc =
  define_assert_from_elf "bignum_shl_small_mc" "x86/generic/bignum_shl_small.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x39; 0xd7;        (* CMP (% rdi) (% rdx) *)
  0x48; 0x0f; 0x42; 0xd7;  (* CMOVB (% rdx) (% rdi) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x74; 0x2a;              (* JE (Imm8 (word 42)) *)
  0x49; 0x89; 0xc9;        (* MOV (% r9) (% rcx) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x4f; 0x8b; 0x14; 0xd9;  (* MOV (% r10) (Memop Quadword (%%% (r9,3,r11))) *)
  0x4d; 0x89; 0xd0;        (* MOV (% r8) (% r10) *)
  0x49; 0x0f; 0xa5; 0xc2;  (* SHLD (% r10) (% rax) (% cl) *)
  0x4e; 0x89; 0x14; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,r11))) (% r10) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x49; 0xff; 0xc3;        (* INC (% r11) *)
  0x49; 0x39; 0xd3;        (* CMP (% r11) (% rdx) *)
  0x72; 0xe6;              (* JB (Imm8 (word 230)) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x49; 0x0f; 0xa5; 0xc2;  (* SHLD (% r10) (% rax) (% cl) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x49; 0x39; 0xfb;        (* CMP (% r11) (% rdi) *)
  0x73; 0x1b;              (* JAE (Imm8 (word 27)) *)
  0x4a; 0x89; 0x04; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,r11))) (% rax) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x49; 0xff; 0xc3;        (* INC (% r11) *)
  0x49; 0x39; 0xfb;        (* CMP (% r11) (% rdi) *)
  0x73; 0x0c;              (* JAE (Imm8 (word 12)) *)
  0x4a; 0x89; 0x04; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,r11))) (% rax) *)
  0x49; 0xff; 0xc3;        (* INC (% r11) *)
  0x49; 0x39; 0xfb;        (* CMP (% r11) (% rdi) *)
  0x72; 0xf4;              (* JB (Imm8 (word 244)) *)
  0xc3                     (* RET *)
];;

let bignum_shl_small_tmc = define_trimmed "bignum_shl_small_tmc" bignum_shl_small_mc;;

let BIGNUM_SHL_SMALL_EXEC = X86_MK_CORE_EXEC_RULE bignum_shl_small_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SHL_SMALL_CORRECT = prove
 (`!p z n x a c pc.
        nonoverlapping (word pc,0x5d) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_shl_small_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = word(pc + 0x5c) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (2 EXP (val c MOD 64) * a) (val p) /\
                  (p = n
                   ==> C_RETURN s =
                       word(highdigits (2 EXP (val c MOD 64) * a) (val p))))
             (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `x:int64` THEN
  X_GEN_TAC `a:num` THEN W64_GEN_TAC `c:num` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Remove some redundancy in conclusion ***)

  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN
  ENSURES_SEQUENCE_TAC `pc + 0x5c`
   `\s. 2 EXP (64 * p) * val(read RAX s) + bignum_from_memory(z,p) s =
        2 EXP (c MOD 64) * lowdigits a p` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN
     `2 EXP (64 * p) * val(read RAX s0) + bignum_from_memory(z,p) s0 =
      2 EXP (c MOD 64) * lowdigits a p`
     (fun th -> MP_TAC(AP_TERM `\x. x DIV 2 EXP (64 * p)` th) THEN
                MP_TAC(AP_TERM `\x. x MOD 2 EXP (64 * p)` th)) THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; ADD_CLAUSES;
                 DIV_LT; MOD_LT_EQ; MOD_LT; BIGNUM_FROM_MEMORY_BOUND;
                 lowdigits; highdigits] THEN
    CONV_TAC MOD_DOWN_CONV THEN SIMP_TAC[VAL_WORD_GALOIS] THEN
    REPLICATE_TAC 2 (DISCH_THEN(K ALL_TAC)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VAL_EQ] THEN ASM_SIMP_TAC[MOD_LT]] THEN

  (*** Reshuffle to handle clamping and just assume n <= p ***)

  ENSURES_SEQUENCE_TAC `pc + 0xd`
   `\s. read RDI s = word p /\
        read RSI s = z /\
        read RDX s = word(MIN n p) /\
        read RCX s = x /\
        read R8 s = word c /\
        read RAX s = word 0 /\
        read R11 s = word 0 /\
        bignum_from_memory(x,MIN n p) s = lowdigits a p` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_SHL_SMALL_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[lowdigits; REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
        (GSYM BIGNUM_FROM_MEMORY_MOD)] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM COND_RAND] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC)] THEN
  SUBGOAL_THEN
   `!w n. w = z \/
          nonoverlapping_modulo (2 EXP 64) (val w,8 * n) (val z,8 * p)
          ==> w:int64 = z \/
              nonoverlapping_modulo (2 EXP 64)
                 (val w,8 * MIN n p) (val z,8 * p)`
   (fun th -> DISCH_THEN(MP_TAC o MATCH_MP th))
  THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`c < 2 EXP 64`; `p < 2 EXP 64`;
    `val(word c:int64) = c`; `val(word p:int64) = p`] THEN
  SUBGOAL_THEN `MIN n p < 2 EXP 64` MP_TAC THENL
   [ASM_ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
  MP_TAC(ARITH_RULE `MIN n p <= p`) THEN
  MAP_EVERY SPEC_TAC
   [`lowdigits a p`,`a:num`; `MIN n p`,`n:num`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
  VAL_INT64_TAC `n:num` THEN BIGNUM_RANGE_TAC "n" "a" THEN
  SUBGOAL_THEN `a < 2 EXP (64 * p)` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_REWRITE_TAC[ARITH_EQ; LE_MULT_LCANCEL];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Break into two pieces at "tail", handle main loop "loop" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x3c`
   `\s. read RDI s = word p /\
        read RSI s = z /\
        read R11 s = word n /\
        2 EXP (64 * n) * val (read RAX s) + bignum_from_memory(z,n) s =
        2 EXP (c MOD 64) * a` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_SHL_SMALL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; ADD_CLAUSES];
      ALL_TAC] THEN

    ENSURES_WHILE_UP_TAC `n:num` `pc + 0x18` `pc + 0x2d`
     `\i s. read RDI s = word p /\
            read RSI s = z /\
            read RDX s = word n /\
            read R9 s = x /\
            read RCX s = word c /\
            read R11 s = word i /\
            bignum_from_memory(word_add x (word (8 * i)),n - i) s =
            highdigits a i /\
            2 EXP (64 * i) * val(read RAX s) DIV 2 EXP (64 - c MOD 64) +
            bignum_from_memory(z,i) s =
            2 EXP (c MOD 64) * lowdigits a i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--4) THEN
      SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[LOWDIGITS_0; DIV_0; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES;
                  WORD_ADD_0; HIGHDIGITS_0; SUB_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `i:num < p` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      GHOST_INTRO_TAC `b:int64` `read RAX` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - i = 0 <=> ~(i < n)`] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      X86_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--6) THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; DIMINDEX_64; GSYM WORD_ADD;
               ARITH_RULE `64 - n <= 64`] THEN
      SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_64_CLAUSES; LOWDIGITS_CLAUSES] THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUM_RING
       `ee * b + m:num = c * l
        ==> e * d + y = c * z + b
            ==> (ee * e) * d + m + ee * y = c * (ee * z + l)`)) THEN
      REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[ARITH_RULE `64 - (64 - x MOD 64) = x MOD 64`] THEN
      SUBGOAL_THEN `2 EXP 64 = 2 EXP (c MOD 64) * 2 EXP (64 - c MOD 64)`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; GSYM MULT_ASSOC]] THEN
      REWRITE_TAC[DIVISION_SIMP];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--2);

      GHOST_INTRO_TAC `b:int64` `read RAX` THEN
      X86_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--5) THEN

      ASM_SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; LE_REFL;
        MOD_64_CLAUSES; VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES;
        MESON[VAL_BOUND_64; DIV_LE; LET_TRANS; MOD_LT]
          `(val(b:int64) DIV n) MOD 2 EXP 64 = val b DIV n`] THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF]];

    ALL_TAC] THEN

  (*** The case p = n ***)

  ASM_CASES_TAC `p:num = n` THENL
   [UNDISCH_THEN `p:num = n` (SUBST_ALL_TAC o SYM) THEN
    X86_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--2);
    ALL_TAC] THEN

  (*** The case p = n + 1 ***)

  ASM_CASES_TAC `p = n + 1` THENL
   [UNDISCH_THEN `p = n + 1` SUBST_ALL_TAC THEN
    GHOST_INTRO_TAC `b:int64` `read RAX` THEN VAL_INT64_TAC `n + 1` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ARITH_RULE `~(n + 1 <= n)`) THEN DISCH_TAC THEN
    X86_STEPS_TAC BIGNUM_SHL_SMALL_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD; LE_REFL] THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** the tail loop "zloop" ***)

  ENSURES_WHILE_AUP_TAC `n + 1` `p:num` `pc + 0x50` `pc + 0x57`
   `\i s. read RDI s = word p /\
          read RSI s = z /\
          read R11 s = word i /\
          read RAX s = word 0 /\
          bignum_from_memory (z,i) s = 2 EXP (c MOD 64) * a` THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC;

    GHOST_INTRO_TAC `b:int64` `read RAX` THEN VAL_INT64_TAC `n + 1` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ARITH_RULE `n:num <= p ==> (p <= n <=> p = n)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X86_STEPS_TAC BIGNUM_SHL_SMALL_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    ASM_REWRITE_TAC[ARITH_RULE `p <= n + 1 <=> p <= n \/ p = n + 1`] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    X86_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--2) THEN
    REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--2);

    X86_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--2) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES]]);;

let BIGNUM_SHL_SMALL_NOIBT_SUBROUTINE_CORRECT = prove
 (`!p z n x a c pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_shl_small_tmc) (z,8 * val p) /\
        nonoverlapping (stackpointer,8) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_shl_small_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (2 EXP (val c MOD 64) * a) (val p) /\
                  (p = n
                   ==> C_RETURN s =
                       word(highdigits (2 EXP (val c MOD 64) * a) (val p))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_shl_small_tmc BIGNUM_SHL_SMALL_CORRECT);;

let BIGNUM_SHL_SMALL_SUBROUTINE_CORRECT = prove
 (`!p z n x a c pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_shl_small_mc) (z,8 * val p) /\
        nonoverlapping (stackpointer,8) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_shl_small_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (2 EXP (val c MOD 64) * a) (val p) /\
                  (p = n
                   ==> C_RETURN s =
                       word(highdigits (2 EXP (val c MOD 64) * a) (val p))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SHL_SMALL_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_shl_small_windows_mc = define_from_elf
   "bignum_shl_small_windows_mc" "x86/generic/bignum_shl_small.obj";;

let bignum_shl_small_windows_tmc = define_trimmed "bignum_shl_small_windows_tmc" bignum_shl_small_windows_mc;;

let BIGNUM_SHL_SMALL_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z n x a c pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_shl_small_windows_tmc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_shl_small_windows_tmc) (z,8 * val p) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_shl_small_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (2 EXP (val c MOD 64) * a) (val p) /\
                  (p = n
                   ==> WINDOWS_C_RETURN s =
                       word(highdigits (2 EXP (val c MOD 64) * a) (val p))))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_shl_small_windows_tmc bignum_shl_small_tmc
    BIGNUM_SHL_SMALL_CORRECT);;

let BIGNUM_SHL_SMALL_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z n x a c pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_shl_small_windows_mc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_shl_small_windows_mc) (z,8 * val p) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_shl_small_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (2 EXP (val c MOD 64) * a) (val p) /\
                  (p = n
                   ==> WINDOWS_C_RETURN s =
                       word(highdigits (2 EXP (val c MOD 64) * a) (val p))))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SHL_SMALL_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

