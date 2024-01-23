(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Little-endian transformation (just copying as x86 is little-endian).      *)
(* There are three different correctness variants corresponding to the three *)
(* aliases with different types (littleendian, fromlebytes and tolebytes).   *)
(* ========================================================================= *)

(**** print_literal_from_elf "x86/p256/bignum_littleendian_4.o";;
 ****)

let bignum_littleendian_4_mc =
  define_assert_from_elf "bignum_littleendian_4_mc" "x86/p256/bignum_littleendian_4.o"
[
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x89; 0x47; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rax) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rax) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x89; 0x47; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rax) *)
  0xc3                     (* RET *)
];;

let BIGNUM_LITTLEENDIAN_4_EXEC = X86_MK_CORE_EXEC_RULE bignum_littleendian_4_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof as a "fromlebytes" function.                                          *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_FROMLEBYTES_4_CORRECT = time prove
 (`!z x l pc.
      nonoverlapping (word pc,0x1f) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_littleendian_4_mc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,32)) s = l)
           (\s. read RIP s = word (pc + 0x1e) /\
                bignum_from_memory(z,4) s = num_of_bytelist l)
          (MAYCHANGE [RIP; RAX] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `l:byte list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BYTELIST_DIGITIZE_TAC "b_" `read (memory :> bytelist (x,32)) s0` THEN
  BIGNUM_DIGITIZE_TAC "d_" `bignum_from_memory(x,4) s0` THEN
  EVERY_ASSUM(fun th ->
   try MP_TAC(GEN_REWRITE_RULE LAND_CONV
        [CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT] th)
   with Failure _ -> ALL_TAC) THEN
  REWRITE_TAC[IMP_IMP] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
        [READ_MEMORY_BYTESIZED_SPLIT] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  X86_STEPS_TAC BIGNUM_LITTLEENDIAN_4_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "l" THEN REWRITE_TAC[num_of_bytelist; val_def] THEN
  REWRITE_TAC[DIMINDEX_8; ARITH_RULE `i < 8 <=> 0 <= i /\ i <= 7`] THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BIT_WORD_OF_BITS; IN; BIT_WORD_JOIN] THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let BIGNUM_FROMLEBYTES_4_SUBROUTINE_CORRECT = time prove
 (`!z x l pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,8 * 4) /\
      nonoverlapping (word pc,0x1f) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_littleendian_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,32)) s = l)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = num_of_bytelist l)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_littleendian_4_mc
    BIGNUM_FROMLEBYTES_4_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* As a "tolebytes" function.                                                *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_TOLEBYTES_4_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x1f) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_littleendian_4_mc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = word (pc + 0x1e) /\
                read (memory :> bytelist(z,32)) s = bytelist_of_num 32 n)
          (MAYCHANGE [RIP; RAX] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ONCE_REWRITE_TAC[READ_BYTES_EQ_BYTELIST; READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[ LENGTH_BYTELIST_OF_NUM] THEN
  MP_TAC(ISPECL [`z:int64`; `x:int64`; `bytelist_of_num 32 n`; `pc:num`]
        BIGNUM_FROMLEBYTES_4_CORRECT) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
  SIMP_TAC[]);;

let BIGNUM_TOLEBYTES_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,8 * 4) /\
      nonoverlapping (word pc,0x1f) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_littleendian_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytelist(z,32)) s = bytelist_of_num 32 n)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_littleendian_4_mc
    BIGNUM_TOLEBYTES_4_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* As a bignum-to-bignum operation.                                          *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_LITTLEENDIAN_4_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x1f) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_littleendian_4_mc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = word (pc + 0x1e) /\
                bignum_from_memory(z,4) s = n)
          (MAYCHANGE [RIP; RAX] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
        [BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[READ_BYTES_EQ_BYTELIST] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  MP_TAC(ISPECL [`z:int64`; `x:int64`; `bytelist_of_num 32 n`; `pc:num`]
        BIGNUM_FROMLEBYTES_4_CORRECT) THEN
  ASM_SIMP_TAC[NUM_OF_BYTELIST_OF_NUM; MOD_LT;
               ARITH_RULE `256 EXP 32 = 2 EXP (64 * 4)`]);;

let BIGNUM_LITTLEENDIAN_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,8 * 4) /\
      nonoverlapping (word pc,0x1f) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_littleendian_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory(z,4) s = n)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_littleendian_4_mc
    BIGNUM_LITTLEENDIAN_4_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let windows_bignum_littleendian_4_mc = define_from_elf
   "windows_bignum_littleendian_4_mc" "x86/p256/bignum_littleendian_4.obj";;

let WINDOWS_BIGNUM_FROMLEBYTES_4_SUBROUTINE_CORRECT = time prove
 (`!z x l pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,0x29); (x,8 * 4)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
      nonoverlapping (word pc,0x29) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) windows_bignum_littleendian_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,32)) s = l)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = num_of_bytelist l)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC windows_bignum_littleendian_4_mc
    bignum_littleendian_4_mc BIGNUM_FROMLEBYTES_4_CORRECT);;

let WINDOWS_BIGNUM_TOLEBYTES_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,0x29); (x,8 * 4)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
      nonoverlapping (word pc,0x29) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) windows_bignum_littleendian_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytelist(z,32)) s = bytelist_of_num 32 n)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC windows_bignum_littleendian_4_mc
    bignum_littleendian_4_mc BIGNUM_TOLEBYTES_4_CORRECT);;

let WINDOWS_BIGNUM_LITTLEENDIAN_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,0x29); (x,8 * 4)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
      nonoverlapping (word pc,0x29) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) windows_bignum_littleendian_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory(z,4) s = n)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC windows_bignum_littleendian_4_mc
    bignum_littleendian_4_mc BIGNUM_LITTLEENDIAN_4_CORRECT);;
