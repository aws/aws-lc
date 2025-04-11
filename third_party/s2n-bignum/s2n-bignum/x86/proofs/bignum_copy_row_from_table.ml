(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time table lookup.                                               *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

let bignum_copy_row_from_table_mc =
  define_assert_from_elf "bignum_copy_row_from_table_mc"
                         "x86/generic/bignum_copy_row_from_table.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x74; 0x56;              (* JE (Imm8 (word 86)) *)
  0x48; 0x85; 0xc9;        (* TEST (% rcx) (% rcx) *)
  0x74; 0x51;              (* JE (Imm8 (word 81)) *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x49; 0x89; 0xc9;        (* MOV (% r9) (% rcx) *)
  0x48; 0xc7; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rax,0))) (Imm32 (word 0)) *)
  0x48; 0x83; 0xc0; 0x08;  (* ADD (% rax) (Imm8 (word 8)) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x75; 0xf0;              (* JNE (Imm8 (word 240)) *)
  0x49; 0xc7; 0xc1; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Imm32 (word 0)) *)
  0x48; 0x89; 0xf0;        (* MOV (% rax) (% rsi) *)
  0x49; 0xc7; 0xc2; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Imm32 (word 0)) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x39; 0xc1;        (* CMP (% r9) (% r8) *)
  0x4e; 0x0f; 0x44; 0x1c; 0xd0;
                           (* CMOVE (% r11) (Memop Quadword (%%% (rax,3,r10))) *)
  0x4e; 0x09; 0x1c; 0xd7;  (* OR (Memop Quadword (%%% (rdi,3,r10))) (% r11) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0x39; 0xca;        (* CMP (% r10) (% rcx) *)
  0x75; 0xe9;              (* JNE (Imm8 (word 233)) *)
  0x4c; 0x8d; 0x14; 0xcd; 0x00; 0x00; 0x00; 0x00;
                           (* LEA (% r10) (Bsid NONE (SOME rcx) (word 3) (word 0)) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xd1;        (* CMP (% r9) (% rdx) *)
  0x75; 0xcf;              (* JNE (Imm8 (word 207)) *)
  0xc3                     (* RET *)
];;

let bignum_copy_row_from_table_tmc = define_trimmed "bignum_copy_row_from_table_tmc" bignum_copy_row_from_table_mc;;

let BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC = X86_MK_CORE_EXEC_RULE bignum_copy_row_from_table_tmc;;
let BIGNUM_COPY_ROW_FROM_TABLE_EXEC = X86_MK_EXEC_RULE bignum_copy_row_from_table_tmc;;

(* ARITH_RULE for proving `lp=rp` where lp and rp are pairs *)
let PAIR_EQ_ARITH_RULE (lp:term) (rp:term) =
  let lpl,lpr = dest_pair lp in
  let rpl,rpr = dest_pair rp in
  let lth = ARITH_RULE (mk_eq (lpl,rpl)) in
  let rth = ARITH_RULE (mk_eq (lpr,rpr)) in
  let th = REFL lp in
  let th = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [lth] th in
  GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [rth] th;;

let READ_MEMORY_BYTES_0 = prove(`read (memory :> bytes (z,0)) s = 0`,
    REWRITE_TAC[PAIR_EQ_ARITH_RULE `(x:int64,0)` `(x:int64, 8*0)`] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL]);;

let SPLIT_FIRST_CONJ_ASSUM_TAC =
    FIRST_X_ASSUM (fun thm -> let t1,t2 = CONJ_PAIR thm in
                              MAP_EVERY ASSUME_TAC [t1;t2]);;

let CASES_FIRST_DISJ_ASSUM_TAC =
    FIRST_X_ASSUM (fun thm ->
      if is_disj (concl thm) then DISJ_CASES_TAC thm else failwith "");;

let LT_WORD_64 = prove(`!x (y:int64). x < val y ==> x < 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LT_TRANS `val (y:int64)` THEN
  ONCE_REWRITE_TAC [GSYM DIMINDEX_64] THEN ASM_REWRITE_TAC[VAL_BOUND]);;

let READ_MEMORY_BYTES_ELEM = prove(`!z w s m k.
  w > k /\ read (memory :> bytes (z,8 * w)) s = m ==>
  val (read (memory :> bytes64 (word_add z (word (8 * k)))) s) = lowdigits (highdigits m k) 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "m" THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_SING] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_FIRSTELEM = prove(`!z w s m.
  w > 0 /\ read (memory :> bytes (z,8 * w)) s = m ==>
  val (read (memory :> bytes64 z) s) = lowdigits m 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `z:int64 = word_add z (word (8 * 0))` (fun thm -> ONCE_REWRITE_TAC[thm]) THENL
  [CONV_TAC WORD_RULE; ALL_TAC] THEN
  IMP_REWRITE_TAC[READ_MEMORY_BYTES_ELEM] THEN REWRITE_TAC[HIGHDIGITS_0]);;

let READ_MEMORY_BYTES_SLICE = prove(`!z w s m k w'.
  w >= k + w' /\ read (memory :> bytes (z,8 * w)) s = m ==>
  read (memory :> bytes (word_add z (word (8 * k)), 8 * w')) s = lowdigits (highdigits m k) w'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "m" THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_SLICE_HIGH = prove(`!z w s m k w'.
  w = k + w' /\ read (memory :> bytes (z,8 * w)) s = m ==>
  read (memory :> bytes (word_add z (word (8 * k)), 8 * w')) s = highdigits m k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "m" THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_MERGE = prove(`!z w w' w'' s m.
    read (memory :> bytes (z,8 * w)) s = lowdigits m w /\
    read (memory :> bytes (word_add z (word (8 * w)),8 * w')) s = highdigits m w /\
    w + w' = w'' ==>
    read (memory :> bytes (z, 8 * w'')) s = m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "w''" THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[HIGH_LOW_DIGITS]);;

let READ_MEMORY_BYTES_BYTES64 = prove(`!z s.
  read (memory :> bytes (z,8)) s = val (read (memory :> bytes64 z) s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PAIR_EQ_ARITH_RULE `(z:int64,8)` `(z:int64,8*1)`;
              GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_SING]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_COPY_ROW_FROM_TABLE_CORRECT = prove(
  `!z table height width idx n m pc.
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_tmc)
                   (z, 8 * val width) /\
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_tmc)
                   (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (table, 8 * val height * val width) /\
    8 * val width < 2 EXP 64 /\
    val idx < val height
    ==> ensures x86
      (\s. bytes_loaded s (word pc) (BUTLAST bignum_copy_row_from_table_tmc) /\
           read RIP s = word pc /\
           C_ARGUMENTS [z; table; height; width; idx] s /\
           bignum_from_memory (table, val height * val width) s = n /\
           bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s = m)
      (\s. read RIP s = word (pc + LENGTH (BUTLAST bignum_copy_row_from_table_tmc)) /\
           bignum_from_memory (z, val width) s = m)
      (MAYCHANGE [RIP] ,,
       MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
       MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
       MAYCHANGE [memory :> bytes(z,8 * val width)])`,

  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
    fst BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC;
    fst BIGNUM_COPY_ROW_FROM_TABLE_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ASM_CASES_TAC `val (height:(64)word) = 0` THENL [
    UNDISCH_TAC `val (idx:int64) < val (height:int64)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LT] THEN ENSURES_INIT_TAC "s0" THEN ITAUT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `width = (word 0):(64)word` THENL [
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_0; MULT_0; WORD_ADD_0] THEN
    X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC (1--4) THEN
    ASM_MESON_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val (width:64 word) = 0)` ASSUME_TAC THENL [
    UNDISCH_TAC `~(width = word 0:64 word)` THEN
    REWRITE_TAC[VAL_EQ_0];
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x10`
    `\s. // C arguments
          read RDI s = z /\ read RSI s = table /\
          read RDX s = height /\ read RCX s = width /\ read R8 s = idx /\
          // Temp vars
          read R9 s = width /\ read RAX s = z /\
          bignum_from_memory (table, val height * val width) s = n /\
          bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
            = m` THEN CONJ_TAC THENL [
  X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC (1--6);

  ALL_TAC] THEN

  (* This is necessary to avoid stores from overwriting the table *)
  SUBGOAL_THEN `val (idx:int64) * val (width:int64) + val width <= val (height:int64) * val width` ASSUME_TAC
    THENL [IMP_REWRITE_TAC[LE_MULT_ADD]; ALL_TAC] THEN

  (* bignum_copy_row_from_table_initzero *)
  ENSURES_WHILE_PDOWN_TAC `val (width:64 word):num` `pc + 0x10` `pc + 0x1e`
    `\i s. (read RDI s = z /\ read RSI s = table /\
            read RDX s = height /\ read RCX s = width /\ read R8 s = idx /\
            read R9 s = word i /\ read RAX s = word (val z + 8 * (val width - i)) /\
            bignum_from_memory (table, val height * val width) s = n /\
            bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
                = m /\
            bignum_from_memory (z, val width - i) s = 0) /\
            (read ZF s <=> i = 0)` THEN REPEAT CONJ_TAC THENL [
    (* 1. width > 0 *)
    ASM_MESON_TAC[];

    (* 2. loop starts *)
    X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC [] THEN
      REWRITE_TAC[SUB_REFL; WORD_VAL; MULT_0; ADD_0; GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL];

    (* 3. loop body *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE [RIP] ,,
                MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
                MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
                MAYCHANGE [memory :> bytes64 (word (val (z:int64) + 8 * (val (width:int64) - (i + 1))))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
      REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      (* SIMPLE_ARITH_TAC isn't good at dealing with assumptions containing 'val'. Let's abbreviate
        val width. *)
      REWRITE_TAC[WORD_ADD; WORD_VAL] THEN
      ABBREV_TAC `w' = val (width:int64)` THEN
      SUBSUMED_MAYCHANGE_TAC;

      ALL_TAC] THEN

    ENSURES_INIT_TAC "s0" THEN

    SUBGOAL_THEN `val (width:64 word) - (i + 1) < val (width:64 word)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `8 * (val (width:int64) - (i + 1)) + 8 <= 18446744073709551616` ASSUME_TAC
      THENL [ASM_ARITH_TAC; ALL_TAC] THEN

    X86_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [
      CONV_TAC WORD_RULE;

      REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN UNDISCH_TAC `i < val (width:64 word)`
      THEN ARITH_TAC;

      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_SIMP_TAC [ARITH_RULE `i < val (width:64 word) ==> val width - i = (val width - (i + 1)) + 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; WORD_RULE `word_add z (word c) = word (val z + c)`] THEN
      CONV_TAC WORD_RULE;

      REWRITE_TAC[WORD_SUB_ADD; VAL_WORD] THEN
      SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL [
        TRANS_TAC LT_TRANS `val (width:64 word)` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `8 * val (width:64 word) < 2 EXP 64` THEN
        ARITH_TAC;

        ALL_TAC] THEN
      ASM_SIMP_TAC[MOD_LT; DIMINDEX_64]];

    (* 4. loop backedge *)
    REPEAT STRIP_TAC THEN X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC (1--1);

    (* next *)
    ALL_TAC] THEN

  (* bignum_copy_row_from_table_outerloop *)
  ENSURES_WHILE_PUP_TAC `val (height:64 word):num` `pc + 0x2a` `pc + 0x59`
    `\i s.  (read RDI s = z /\ read RSI s = table /\
            read RDX s = height /\ read RCX s = width /\ read R8 s = idx /\
            read R9 s = word i /\ read RAX s = word_add table (word (8 * i * val width)) /\
            bignum_from_memory (table, val height * val width) s = n /\
            bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
                = m /\
            ((i <= val idx  /\ bignum_from_memory (z, val width) s = 0) \/
              (i > val idx /\ bignum_from_memory (z, val width) s = m))) /\
            (read ZF s <=> i = val height)` THEN REPEAT CONJ_TAC THENL [
    (* 1. height > 0 *)
    ASM_MESON_TAC[];

    (* 2. to loop start *)
    X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC (1--3) THEN
    REWRITE_TAC[ARITH_RULE `x * 0 = 0`; ARITH_RULE `0 * x = 0`; WORD_ADD_0] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ARITH_RULE `x - 0 = x`]) THEN
    ASM_REWRITE_TAC[LE_0];

    (* 3. loop body - pass *)
    ALL_TAC;

    (* 4. loop backedge *)
    REPEAT STRIP_TAC THEN
    X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC (1--1);

    (* next *)
    X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC [1] THEN
    CASES_FIRST_DISJ_ASSUM_TAC THEN SPLIT_FIRST_CONJ_ASSUM_TAC THENL [
      UNDISCH_TAC `val (idx:int64) < val (height:int64)` THEN
      UNDISCH_TAC `val (height:int64) <= val (idx:int64)` THEN
      ARITH_TAC;

      ASM_MESON_TAC[]
    ]
  ] THEN

  REPEAT STRIP_TAC THEN


  (* bignum_copy_row_from_table_innerloop *)
  ENSURES_WHILE_PUP_TAC `val (width:64 word):num` `pc + 0x31` `pc + 0x46`
    `\j s.  (read RDI s = z /\ read RSI s = table /\
            read RDX s = height /\ read RCX s = width /\ read R8 s = idx /\
            read R9 s = word i /\
            read R10 s = word j /\
            read RAX s = word_add table (word (8 * i * val width)) /\
            bignum_from_memory (table, val height * val width) s = n /\
            bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
                = m /\
            ((i < val idx /\
              bignum_from_memory (z, j) s = 0 /\
              bignum_from_memory (word_add z (word (8 * j)), val width - j) s = 0)
              \/
              (i = val idx /\
              bignum_from_memory (z, j) s = lowdigits m j /\
              bignum_from_memory (word_add z (word (8 * j)), val width - j) s = 0)
              \/
              (i > val idx /\
              bignum_from_memory (z, j) s = lowdigits m j /\
              bignum_from_memory (word_add z (word (8 * j)), val width - j) s = highdigits m j))) /\
            (read ZF s <=> j = val width)` THEN REPEAT CONJ_TAC THENL [
    (* width != 0 *)
    ASM_MESON_TAC[];

    (* loop entry *)
    X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC (1--1) THEN
    ASM_REWRITE_TAC[WORD_VAL; ADD_0; MULT_0; WORD_ADD_0; SUB_0;
        LOWDIGITS_0; HIGHDIGITS_0; READ_MEMORY_BYTES_0] THEN
    ASM_ARITH_TAC;

    (* loop body *)
    ALL_TAC;

    (* backedge *)
    REPEAT STRIP_TAC THEN
    X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC [1];

    (* inner loop exit -> outer loop branch; pc 0x48 -> 0x59 *)
    X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC (1--5) THEN
    REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THENL [
      SUBGOAL_THEN `m < 2 EXP (64 * val (width:int64))` ASSUME_TAC THENL
      [EXPAND_TAC "m" THEN SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC] THEN
      RULE_ASSUM_TAC (REWRITE_RULE[SUB_0;
        MATCH_MP LOWDIGITS_SELF (ASSUME `m < 2 EXP (64 * val (width:int64))`);
        MATCH_MP HIGHDIGITS_ZERO (ASSUME `m < 2 EXP (64 * val (width:int64))`);
        MULT_0; READ_MEMORY_BYTES_0]) THEN
      REPEAT CASES_FIRST_DISJ_ASSUM_TAC THEN REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN ASM_REWRITE_TAC[] THENL [
        UNDISCH_TAC `i < val (idx:int64)` THEN ARITH_TAC;
        UNDISCH_TAC `i = val (idx:int64)` THEN ARITH_TAC;
        UNDISCH_TAC `i > val (idx:int64)` THEN ARITH_TAC;
      ];

      SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [
        TRANS_TAC LET_TRANS `val (height:int64)` THEN
        CONJ_TAC THENL [
          UNDISCH_TAC `i < val (height:int64)` THEN ARITH_TAC;
          REWRITE_TAC[VAL_BOUND_64]];

        ALL_TAC
      ] THEN
      REWRITE_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;ARITH_RULE`1 MOD 2 EXP 64 = 1`; ADD_0] THEN

      ASM_SIMP_TAC[MOD_LT; MATCH_MP LT_WORD_64
        (ASSUME `i < val (height:int64)`)]
    ]
  ] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE [RIP] ,,
                MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
                MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
                MAYCHANGE [memory :> bytes64 (word (val (z:int64) + 8 * i'))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
      REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      (* SIMPLE_ARITH_TAC isn't good at dealing with assumptions containing 'val'. Let's abbreviate
        val width. *)
      REWRITE_TAC[WORD_ADD; WORD_VAL] THEN
      ABBREV_TAC `w' = val (width:int64)` THEN
      SUBSUMED_MAYCHANGE_TAC;

      ALL_TAC] THEN

  ASSERT_USING_ASM_ARITH_TAC `val (width:int64) < 2 EXP 64` THEN
  ASSERT_USING_ASM_ARITH_TAC `i' < 2 EXP 64` THEN
  SUBGOAL_THEN `val (word i':int64) = i'` ASSUME_TAC THENL
    [IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT]; ALL_TAC] THEN
  ASSERT_USING_ASM_ARITH_TAC `8 * i' + 8 <= 18446744073709551616` THEN
  ASSERT_USING_ASM_ARITH_TAC
    `(8 * i' + 8) + 8 * (val (width:int64) - i' - 1) <= 18446744073709551616` THEN
  ASSERT_USING_ASM_ARITH_TAC
    `val (idx:int64) * val (width:int64) + i' < val (height:int64) * val width` THEN
  SUBGOAL_THEN `val (word i:int64) = i` ASSUME_TAC THENL
    [IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN ASM_MESON_TAC[LT_TRANS;VAL_BOUND_64];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  CASES_FIRST_DISJ_ASSUM_TAC THENL [ (* 2 subgoals *)
    (* 1. i < val idx *)
    REPEAT_N 2 SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    (* high *)
    SUBGOAL_THEN `read
        (memory :> bytes
            (word_add (word_add (z:int64) (word (8 * i'))) (word (8 * 1)),
            8 * (val (width:int64) - i' - 1)))
        s0 = highdigits 0 1`
        (fun th -> ASSUME_TAC
          (REWRITE_RULE[WORD_ADD_ASSOC_CONSTS;ARITH_RULE`8*1=8`;HIGHDIGITS_TRIVIAL] th)) THENL [
      MATCH_MP_TAC READ_MEMORY_BYTES_SLICE_HIGH THEN
      EXISTS_TAC `val (width:int64) - i'` THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    (* the element *)
    SUBGOAL_THEN `val (read
        (memory :> bytes64 (word_add (z:int64) (word (8 * i')))) s0) = lowdigits 0 1`
        (fun th -> ASSUME_TAC
          (REWRITE_RULE[WORD_ADD_ASSOC_CONSTS;ARITH_RULE`8*1=8`;LOWDIGITS_TRIVIAL;VAL_EQ_0] th)) THENL [
      MATCH_MP_TAC READ_MEMORY_BYTES_FIRSTELEM THEN
      EXISTS_TAC `val (width:int64) - i'` THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(val (word_sub (word i:int64) idx) = 0)` ASSUME_TAC THENL [
      ASM_REWRITE_TAC[VAL_WORD_SUB;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN
      CONJ_TAC THENL [
        IMP_REWRITE_TAC[ADD_SUB_SWAP2] THEN CONJ_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN
        CONJ_TAC THENL [ REWRITE_TAC[GE] THEN MESON_TAC[LE_LT;VAL_BOUND_64]; ASM_ARITH_TAC ];

        SUBGOAL_THEN `~(2 EXP 64 - val (idx:int64) = 0)` MP_TAC THENL [
          SUBGOAL_THEN `val (idx:int64) < 2 EXP 64` MP_TAC THENL [
            MESON_TAC[VAL_BOUND_64]; ALL_TAC
          ]
          THEN ARITH_TAC;
          ALL_TAC
        ] THEN ARITH_TAC
      ];
      ALL_TAC
    ] THEN
    X86_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [ (* creates 3 subgoals *)
      CONV_TAC WORD_RULE;

      DISJ1_TAC THEN
      CONJ_TAC THENL [
        ASM_REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;BIGNUM_FROM_MEMORY_STEP] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC;

        ASM_REWRITE_TAC[ARITH_RULE`8*(a+1)=8*a+8`;ARITH_RULE`x-(y+z)=x-y-z`]
      ];

      REWRITE_TAC[VAL_WORD_ADD;VAL_WORD_SUB;DIMINDEX_64;VAL_WORD] THEN
      CONV_TAC MOD_DOWN_CONV THEN (* This is really useful! *)
      SUBGOAL_THEN `2 EXP 64 >= val (width:int64) /\ val (width:int64) >= (i' + 1)`
          (fun th -> REWRITE_TAC[MATCH_MP ADD_SUB_SWAP2 th]) THENL [
        MP_TAC (SPEC `width:int64` VAL_BOUND_64) THEN
        UNDISCH_TAC `i' < val (width:int64)` THEN
        ARITH_TAC;

        ALL_TAC
      ] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `2 EXP 64 <= (val (width:int64) - (i' + 1)) \/ (val (width:int64) - (i' + 1)) = 0` THEN
      CONJ_TAC THENL [
        MATCH_MP_TAC SUB_MOD_EQ_0 THEN
        ARITH_TAC;

        UNDISCH_TAC `i' < val (width:int64)` THEN
        UNDISCH_TAC `val (width:int64) < 2 EXP 64` THEN
        ARITH_TAC
      ]
    ];

    CASES_FIRST_DISJ_ASSUM_TAC THENL [ (* 2 subgoals *)
      (* 2. i = val idx *)
      REPEAT_N 2 SPLIT_FIRST_CONJ_ASSUM_TAC THEN
      (* high *)
      SUBGOAL_THEN `read
          (memory :> bytes
              (word_add (word_add (z:int64) (word (8 * i'))) (word (8 * 1)),
              8 * (val (width:int64) - i' - 1)))
          s0 = highdigits 0 1`
          (fun th -> ASSUME_TAC
            (REWRITE_RULE[WORD_ADD_ASSOC_CONSTS;ARITH_RULE`8*1=8`;HIGHDIGITS_TRIVIAL] th)) THENL [
        MATCH_MP_TAC READ_MEMORY_BYTES_SLICE_HIGH THEN
        EXISTS_TAC `val (width:int64) - i'` THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      (* the element *)
      SUBGOAL_THEN `val (read
          (memory :> bytes64 (word_add (z:int64) (word (8 * i')))) s0) = lowdigits 0 1`
          (fun th -> ASSUME_TAC
            (REWRITE_RULE[WORD_ADD_ASSOC_CONSTS;ARITH_RULE`8*1=8`;LOWDIGITS_TRIVIAL;VAL_EQ_0] th)) THENL [
        MATCH_MP_TAC READ_MEMORY_BYTES_FIRSTELEM THEN
        EXISTS_TAC `val (width:int64) - i'` THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      (* to fold branch cond at cmove *)
      SUBGOAL_THEN `val (word_sub (word (val (idx:int64))) idx) = 0` ASSUME_TAC THENL [
        REWRITE_TAC[WORD_VAL] THEN CONV_TAC WORD_ARITH;
        ALL_TAC
      ] THEN
      (* cmove's chosen value *)
      SUBGOAL_THEN
          `val (read (memory :> bytes64
            (word_add (word_add table (word (8 * val (idx:int64) * val (width:int64))):int64)
                      (word (8 * i')))) s0) =
          lowdigits (highdigits m i') 1` MP_TAC THENL [
        MATCH_MP_TAC READ_MEMORY_BYTES_ELEM THEN
        EXISTS_TAC `val (width:int64)` THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];

        ALL_TAC
      ] THEN
      DISCH_THEN (fun th ->
        ASSUME_TAC (REWRITE_RULE[WORD_VAL] (MATCH_MP
          (WORD_RULE `x = y ==> (word x:int64) = word y`)
          (REWRITE_RULE[WORD_ADD_ASSOC_CONSTS] th)))) THEN
      X86_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL [ (* creates 3 subgoals *)
        CONV_TAC WORD_RULE;

        DISJ1_TAC THEN
        CONJ_TAC THENL [
          ASM_REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;BIGNUM_FROM_MEMORY_STEP] THEN
          ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
          REWRITE_TAC[LOWDIGITS_1;BIGDIGIT_HIGHDIGITS;VAL_WORD_BIGDIGIT;ADD_0] THEN
          REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;

          ASM_REWRITE_TAC[ARITH_RULE`8*(a+1)=8*a+8`;ARITH_RULE`x-(y+z)=x-y-z`]
        ];

        REWRITE_TAC[VAL_WORD_ADD;VAL_WORD_SUB;DIMINDEX_64;VAL_WORD] THEN
        CONV_TAC MOD_DOWN_CONV THEN (* This is really useful! *)
        SUBGOAL_THEN `2 EXP 64 >= val (width:int64) /\ val (width:int64) >= (i' + 1)`
            (fun th -> REWRITE_TAC[MATCH_MP ADD_SUB_SWAP2 th]) THENL [
          MP_TAC (SPEC `width:int64` VAL_BOUND_64) THEN
          UNDISCH_TAC `i' < val (width:int64)` THEN
          ARITH_TAC;

          ALL_TAC
        ] THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `2 EXP 64 <= (val (width:int64) - (i' + 1)) \/ (val (width:int64) - (i' + 1)) = 0` THEN
        CONJ_TAC THENL [
          MATCH_MP_TAC SUB_MOD_EQ_0 THEN
          ARITH_TAC;

          UNDISCH_TAC `i' < val (width:int64)` THEN
          UNDISCH_TAC `val (width:int64) < 2 EXP 64` THEN
          ARITH_TAC
        ]
      ];

      (* 3. i > val idx *)
      REPEAT_N 2 SPLIT_FIRST_CONJ_ASSUM_TAC THEN
      (* high *)
      SUBGOAL_THEN `read
          (memory :> bytes
              (word_add (word_add (z:int64) (word (8 * i'))) (word (8 * 1)),
              8 * (val (width:int64) - i' - 1)))
          s0 = highdigits (highdigits m i') 1`
          (fun th -> ASSUME_TAC
            (REWRITE_RULE[WORD_ADD_ASSOC_CONSTS;ARITH_RULE`8*1=8`;HIGHDIGITS_HIGHDIGITS] th)) THENL [
        MATCH_MP_TAC READ_MEMORY_BYTES_SLICE_HIGH THEN
        EXISTS_TAC `val (width:int64) - i'` THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      (* the element *)
      SUBGOAL_THEN `val (read
          (memory :> bytes64 (word_add (z:int64) (word (8 * i')))) s0) =
          lowdigits (highdigits m i') 1`
          MP_TAC THENL [
        MATCH_MP_TAC READ_MEMORY_BYTES_FIRSTELEM THEN
        EXISTS_TAC `val (width:int64) - i'` THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN (fun th ->
        ASSUME_TAC (REWRITE_RULE[WORD_VAL;LOWDIGITS_1;BIGDIGIT_HIGHDIGITS;ADD_0]
          (MATCH_MP (WORD_RULE `x = y ==> (word x:int64) = word y`) th))) THEN
      (* cmov's cond *)
      SUBGOAL_THEN `~(val (word_sub (word i:int64) idx) = 0)` ASSUME_TAC THENL [
        ASM_REWRITE_TAC[VAL_WORD_SUB;DIMINDEX_64] THEN
        SUBGOAL_THEN `2 EXP 64 >= val (idx:int64) /\ i >= val (idx:int64)` MP_TAC THENL [
          CONJ_TAC THENL [
            REWRITE_TAC[GE;LE_LT] THEN DISJ1_TAC THEN REWRITE_TAC[VAL_BOUND_64];
            ASM_ARITH_TAC
          ];
          ALL_TAC
        ] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[MATCH_MP ADD_SUB_SWAP th]) THEN
        ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
        REWRITE_TAC[MOD_REFL;ADD;MOD_MOD_REFL] THEN
        SUBGOAL_THEN `i - val (idx:int64) < 2 EXP 64` MP_TAC THENL [
          MP_TAC (SPEC `height:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC;
          ALL_TAC
        ] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      X86_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL [ (* creates 3 subgoals *)
        CONV_TAC WORD_RULE;

        REPEAT_N 2 DISJ2_TAC THEN
        CONJ_TAC THENL [
          ASM_REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;BIGNUM_FROM_MEMORY_STEP] THEN
          ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
          REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
          REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;

          ASM_REWRITE_TAC[ARITH_RULE`8*(a+1)=8*a+8`;ARITH_RULE`x-(y+z)=x-y-z`]
        ];

        REWRITE_TAC[VAL_WORD_ADD;VAL_WORD_SUB;DIMINDEX_64;VAL_WORD] THEN
        CONV_TAC MOD_DOWN_CONV THEN (* This is really useful! *)
        SUBGOAL_THEN `2 EXP 64 >= val (width:int64) /\ val (width:int64) >= (i' + 1)`
            (fun th -> REWRITE_TAC[MATCH_MP ADD_SUB_SWAP2 th]) THENL [
          MP_TAC (SPEC `width:int64` VAL_BOUND_64) THEN
          UNDISCH_TAC `i' < val (width:int64)` THEN
          ARITH_TAC;

          ALL_TAC
        ] THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `2 EXP 64 <= (val (width:int64) - (i' + 1)) \/ (val (width:int64) - (i' + 1)) = 0` THEN
        CONJ_TAC THENL [
          MATCH_MP_TAC SUB_MOD_EQ_0 THEN
          ARITH_TAC;

          UNDISCH_TAC `i' < val (width:int64)` THEN
          UNDISCH_TAC `val (width:int64) < 2 EXP 64` THEN
          ARITH_TAC
        ]
      ]
    ]
  ]);;

let BIGNUM_COPY_ROW_FROM_TABLE_NOIBT_SUBROUTINE_CORRECT = prove(
  `!z table height width idx n m pc stackpointer returnaddress.
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_tmc)
                   (z, 8 * val width) /\
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_tmc)
                   (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (stackpointer, 8) /\
    8 * val width < 2 EXP 64 /\
    val idx < val height
    ==> ensures x86
      (\s. bytes_loaded s (word pc) bignum_copy_row_from_table_tmc /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [z; table; height; width; idx] s /\
           bignum_from_memory (table, val height * val width) s = n /\
           bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s = m)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           bignum_from_memory (z, val width) s = m)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(z,8 * val width)])`,
  REWRITE_TAC[fst BIGNUM_COPY_ROW_FROM_TABLE_EXEC] THEN
  (* A hack to introduce
     `val idx * val width + val width <= val height * val width`, which is
     necessary to help NONOVERLAPPING_TAC. *)
  SUBGOAL_THEN
    `!w i h. (8 * w < 2 EXP 64 /\ i < h) <=>
             (8 * w < 2 EXP 64 /\ i < h /\ i * w + w <= h * w)`
    (fun th -> REWRITE_TAC[th]) THENL [
    REPEAT GEN_TAC THEN EQ_TAC THENL [
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_MULT_ADD];
      STRIP_TAC THEN ASM_REWRITE_TAC[]
    ];
    ALL_TAC
  ] THEN
  let core = REWRITE_RULE
      [fst BIGNUM_COPY_ROW_FROM_TABLE_EXEC;
       fst BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC]
      BIGNUM_COPY_ROW_FROM_TABLE_CORRECT in
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_copy_row_from_table_tmc core);;

let BIGNUM_COPY_ROW_FROM_TABLE_SUBROUTINE_CORRECT = prove(
  `!z table height width idx n m pc stackpointer returnaddress.
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_mc)
                   (z, 8 * val width) /\
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_mc)
                   (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (stackpointer, 8) /\
    8 * val width < 2 EXP 64 /\
    val idx < val height
    ==> ensures x86
      (\s. bytes_loaded s (word pc) bignum_copy_row_from_table_mc /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [z; table; height; width; idx] s /\
           bignum_from_memory (table, val height * val width) s = n /\
           bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s = m)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           bignum_from_memory (z, val width) s = m)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(z,8 * val width)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_COPY_ROW_FROM_TABLE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_copy_row_from_table_windows_mc = define_from_elf
    "bignum_copy_row_from_table_windows_mc"
    "x86/generic/bignum_copy_row_from_table.obj";;

let bignum_copy_row_from_table_windows_tmc = define_trimmed "bignum_copy_row_from_table_windows_tmc" bignum_copy_row_from_table_windows_mc;;let WINDOWS_BIGNUM_COPY_ROW_FROM_TABLE_EXEC =

    X86_MK_EXEC_RULE bignum_copy_row_from_table_windows_tmc;;


let BIGNUM_COPY_ROW_FROM_TABLE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove(
  `!z table height width idx n m pc stackpointer returnaddress.
    ALL (nonoverlapping (word_sub stackpointer (word 16), 16))
        [(word pc, LENGTH bignum_copy_row_from_table_windows_tmc);
         (table, 8 * val height * val width)] /\
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_windows_tmc)
                   (z, 8 * val width) /\
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_windows_tmc)
                   (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (word_sub stackpointer (word 16), 24) /\
    8 * val width < 2 EXP 64 /\
    val idx < val height
    ==> ensures x86
      (\s. bytes_loaded s (word pc) bignum_copy_row_from_table_windows_tmc /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           WINDOWS_C_ARGUMENTS [z; table; height; width; idx] s /\
           bignum_from_memory (table, val height * val width) s = n /\
           bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s = m)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           bignum_from_memory (z, val width) s = m)
      (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(z,8 * val width);
                  memory :> bytes(word_sub stackpointer (word 16), 16)])`,
  REWRITE_TAC[fst WINDOWS_BIGNUM_COPY_ROW_FROM_TABLE_EXEC] THEN
  (* A hack to introduce
     `val idx * val width + val width <= val height * val width`, which is
     necessary to help NONOVERLAPPING_TAC. *)
  SUBGOAL_THEN
    `!w i h. (8 * w < 2 EXP 64 /\ i < h) <=>
             (8 * w < 2 EXP 64 /\ i < h /\ i * w + w <= h * w)`
    (fun th -> REWRITE_TAC[th]) THENL [
    REPEAT GEN_TAC THEN EQ_TAC THENL [
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_MULT_ADD];
      STRIP_TAC THEN ASM_REWRITE_TAC[]
    ];
    ALL_TAC
  ] THEN
  let core = REWRITE_RULE
      [fst BIGNUM_COPY_ROW_FROM_TABLE_EXEC;
       fst BIGNUM_COPY_ROW_FROM_TABLE_CORE_EXEC]
      BIGNUM_COPY_ROW_FROM_TABLE_CORRECT in
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_copy_row_from_table_windows_tmc
    bignum_copy_row_from_table_tmc core);;

let BIGNUM_COPY_ROW_FROM_TABLE_WINDOWS_SUBROUTINE_CORRECT = prove(
  `!z table height width idx n m pc stackpointer returnaddress.
    ALL (nonoverlapping (word_sub stackpointer (word 16), 16))
        [(word pc, LENGTH bignum_copy_row_from_table_windows_mc);
         (table, 8 * val height * val width)] /\
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_windows_mc)
                   (z, 8 * val width) /\
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_windows_mc)
                   (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (word_sub stackpointer (word 16), 24) /\
    8 * val width < 2 EXP 64 /\
    val idx < val height
    ==> ensures x86
      (\s. bytes_loaded s (word pc) bignum_copy_row_from_table_windows_mc /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           WINDOWS_C_ARGUMENTS [z; table; height; width; idx] s /\
           bignum_from_memory (table, val height * val width) s = n /\
           bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s = m)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           bignum_from_memory (z, val width) s = m)
      (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(z,8 * val width);
                  memory :> bytes(word_sub stackpointer (word 16), 16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_COPY_ROW_FROM_TABLE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

