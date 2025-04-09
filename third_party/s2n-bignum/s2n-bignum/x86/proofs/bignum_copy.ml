(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Copying (with truncation or extension) bignums                            *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_copy.o";;
 ****)

let bignum_copy_mc =
  define_assert_from_elf "bignum_copy_mc" "x86/generic/bignum_copy.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x39; 0xd7;        (* CMP (% rdi) (% rdx) *)
  0x48; 0x0f; 0x42; 0xd7;  (* CMOVB (% rdx) (% rdi) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x74; 0x10;              (* JE (Imm8 (word 16)) *)
  0x4a; 0x8b; 0x04; 0xc1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r8))) *)
  0x4a; 0x89; 0x04; 0xc6;  (* MOV (Memop Quadword (%%% (rsi,3,r8))) (% rax) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x49; 0x39; 0xd0;        (* CMP (% r8) (% rdx) *)
  0x72; 0xf0;              (* JB (Imm8 (word 240)) *)
  0x49; 0x39; 0xf8;        (* CMP (% r8) (% rdi) *)
  0x73; 0x0f;              (* JAE (Imm8 (word 15)) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x4a; 0x89; 0x04; 0xc6;  (* MOV (Memop Quadword (%%% (rsi,3,r8))) (% rax) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x49; 0x39; 0xf8;        (* CMP (% r8) (% rdi) *)
  0x72; 0xf4;              (* JB (Imm8 (word 244)) *)
  0xc3                     (* RET *)
];;

let bignum_copy_tmc = define_trimmed "bignum_copy_tmc" bignum_copy_mc;;

let BIGNUM_COPY_EXEC = X86_MK_CORE_EXEC_RULE bignum_copy_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_COPY_CORRECT = prove
 (`!k z n x a pc.
     nonoverlapping (word pc,0x34) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_copy_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a)
           (\s. read RIP s = word (pc + 0x33) /\
                bignum_from_memory (z,val k) s = lowdigits a (val k))
          (MAYCHANGE [RIP; RAX; RDX; R8] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_COPY_EXEC] THEN
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `x:int64` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Simulate the initial computation of min(n,k) and then
   *** recast the problem with n' = min(n,k) so we can assume
   *** hereafter that n <= k. This makes life a bit easier since
   *** otherwise n can actually be any number < 2^64 without
   *** violating the preconditions.
   ***)

  ENSURES_SEQUENCE_TAC `pc + 0xa`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read RDX s = word(MIN n k) /\
        read RCX s = x /\
        read R8 s = word 0 /\
        bignum_from_memory (x,MIN n k) s = lowdigits a k` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    X86_SIM_TAC BIGNUM_COPY_EXEC (1--3) THEN
    REWRITE_TAC[ARITH_RULE `MIN n k = if k < n then k else n`] THEN
    MESON_TAC[];
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (vfree_in `k:num` o concl))) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN MP_TAC(ARITH_RULE `MIN n k <= k`) THEN
    SPEC_TAC(`lowdigits a k`,`a:num`) THEN SPEC_TAC(`MIN n k`,`n:num`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    VAL_INT64_TAC `n:num` THEN BIGNUM_RANGE_TAC "n" "a"] THEN

  (*** Break at the start of the padding stage ***)

  ENSURES_SEQUENCE_TAC `pc + 0x1f`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R8 s = word n /\
        bignum_from_memory(z,n) s = a` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[MESON[] `0 = a <=> a = 0`] THEN
      X86_SIM_TAC BIGNUM_COPY_EXEC (1--2);
      ALL_TAC] THEN

    FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      NONOVERLAPPING_IMP_SMALL_2)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

    (*** The main copying loop, in the case when n is nonzero ***)

    ENSURES_WHILE_UP_TAC `n:num` `pc + 0xf` `pc + 0x1a`
     `\i s. read RDI s = word k /\
            read RSI s = z /\
            read RDX s = word n /\
            read RCX s = x /\
            read R8 s = word i /\
            bignum_from_memory(z,i) s = lowdigits a i /\
            bignum_from_memory(word_add x (word(8 * i)),n - i) s =
            highdigits a i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_COPY_EXEC (1--2) THEN
      REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      X86_SIM_TAC BIGNUM_COPY_EXEC (1--3) THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_BIGDIGIT] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_COPY_EXEC (1--2);
      X86_SIM_TAC BIGNUM_COPY_EXEC (1--2) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF]];
    ALL_TAC] THEN

  (*** Degenerate case of no padding (initial k <= n) ***)

  FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o
    MATCH_MP (ARITH_RULE `n:num <= k ==> n = k \/ n < k`))
  THENL [X86_SIM_TAC BIGNUM_COPY_EXEC (1--2); ALL_TAC] THEN

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      NONOVERLAPPING_IMP_SMALL_2)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

  (*** Main padding loop ***)

  ENSURES_WHILE_AUP_TAC `n:num` `k:num` `pc + 0x27` `pc + 0x2e`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read R8 s = word i /\
          read RAX s = word 0 /\
          bignum_from_memory(z,i) s = a` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_COPY_EXEC (1--3);
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    X86_SIM_TAC BIGNUM_COPY_EXEC (1--2) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_COPY_EXEC (1--2);
    X86_SIM_TAC BIGNUM_COPY_EXEC (1--2)]);;

let BIGNUM_COPY_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z n x a pc stackpointer returnaddress.
     nonoverlapping (word pc,LENGTH bignum_copy_tmc) (z,8 * val k) /\
     nonoverlapping(z,8 * val k) (stackpointer,8) /\
     (x = z \/ nonoverlapping(x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_copy_tmc  /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s =  lowdigits a (val k))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_copy_tmc BIGNUM_COPY_CORRECT);;

let BIGNUM_COPY_SUBROUTINE_CORRECT = prove
 (`!k z n x a pc stackpointer returnaddress.
     nonoverlapping (word pc,LENGTH bignum_copy_mc) (z,8 * val k) /\
     nonoverlapping(z,8 * val k) (stackpointer,8) /\
     (x = z \/ nonoverlapping(x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_copy_mc  /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s =  lowdigits a (val k))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_COPY_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_copy_windows_mc = define_from_elf
   "bignum_copy_windows_mc" "x86/generic/bignum_copy.obj";;

let bignum_copy_windows_tmc = define_trimmed "bignum_copy_windows_tmc" bignum_copy_windows_mc;;

let BIGNUM_COPY_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z n x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_copy_windows_tmc); (x,8 * val n)] /\
     nonoverlapping (word pc,LENGTH bignum_copy_windows_tmc) (z,8 * val k) /\
     nonoverlapping(z,8 * val k) (word_sub stackpointer (word 16),24) /\
     (x = z \/ nonoverlapping(x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_copy_windows_tmc  /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s =  lowdigits a (val k))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_copy_windows_tmc bignum_copy_tmc
    BIGNUM_COPY_CORRECT);;

let BIGNUM_COPY_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z n x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_copy_windows_mc); (x,8 * val n)] /\
     nonoverlapping (word pc,LENGTH bignum_copy_windows_mc) (z,8 * val k) /\
     nonoverlapping(z,8 * val k) (word_sub stackpointer (word 16),24) /\
     (x = z \/ nonoverlapping(x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_copy_windows_mc  /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s =  lowdigits a (val k))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_COPY_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

