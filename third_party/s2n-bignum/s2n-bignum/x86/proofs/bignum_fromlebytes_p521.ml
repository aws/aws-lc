(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Translation from little-endian byte sequence, 66 bytes -> 9 digits.       *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_fromlebytes_p521.o";;
 ****)

let bignum_fromlebytes_p521_mc =
  define_assert_from_elf "bignum_fromlebytes_p521_mc" "x86/p521/bignum_fromlebytes_p521.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x89; 0x47; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rax) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rax) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x89; 0x47; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rax) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rax) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x89; 0x47; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rax) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x89; 0x47; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rax) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x89; 0x47; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rax) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x66; 0x8b; 0x46; 0x40;  (* MOV (% ax) (Memop Word (%% (rsi,64))) *)
  0x48; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rax) *)
  0xc3                     (* RET *)
];;

let bignum_fromlebytes_p521_tmc = define_trimmed "bignum_fromlebytes_p521_tmc" bignum_fromlebytes_p521_mc;;

let BIGNUM_FROMLEBYTES_P521_EXEC = X86_MK_CORE_EXEC_RULE bignum_fromlebytes_p521_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_FROMLEBYTES_P521_CORRECT = prove
 (`!z x l pc.
      nonoverlapping (word pc,0x49) (z,8 * 9) /\
      (x = z \/ nonoverlapping (x,66) (z,8 * 9))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_fromlebytes_p521_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,66)) s = l)
           (\s. read RIP s = word (pc + 0x48) /\
                bignum_from_memory(z,9) s = num_of_bytelist l)
          (MAYCHANGE [RIP; RAX] ,,
           MAYCHANGE [memory :> bignum(z,9)] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `l:byte list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BYTELIST_DIGITIZE_TAC "b_" `read (memory :> bytelist (x,66)) s0` THEN
  BIGNUM_DIGITIZE_TAC "d_" `bignum_from_memory(x,8) s0` THEN
  EVERY_ASSUM(fun th ->
   try MP_TAC(GEN_REWRITE_RULE LAND_CONV
        [CONJUNCT2(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT)] th)
   with Failure _ -> ALL_TAC) THEN
  REWRITE_TAC[IMP_IMP] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
        [READ_MEMORY_BYTESIZED_SPLIT] THEN
  MP_TAC(ISPECL [`memory`; `word_add x (word 64):int64`; `s0:x86state`]
        (last(CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT))) THEN
  GEN_REWRITE_TAC I [IMP_IMP] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  X86_STEPS_TAC BIGNUM_FROMLEBYTES_P521_EXEC (1--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "l" THEN REWRITE_TAC[num_of_bytelist] THEN
  CONV_TAC WORD_BLAST);;

let BIGNUM_FROMLEBYTES_P521_NOIBT_SUBROUTINE_CORRECT = prove
 (`!z x l pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,8 * 9) /\
      nonoverlapping (word pc,LENGTH bignum_fromlebytes_p521_tmc) (z,8 * 9) /\
      (x = z \/ nonoverlapping (x,66) (z,8 * 9))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_fromlebytes_p521_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,66)) s = l)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = num_of_bytelist l)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_fromlebytes_p521_tmc
    BIGNUM_FROMLEBYTES_P521_CORRECT);;

let BIGNUM_FROMLEBYTES_P521_SUBROUTINE_CORRECT = prove
 (`!z x l pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,8 * 9) /\
      nonoverlapping (word pc,LENGTH bignum_fromlebytes_p521_mc) (z,8 * 9) /\
      (x = z \/ nonoverlapping (x,66) (z,8 * 9))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_fromlebytes_p521_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,66)) s = l)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = num_of_bytelist l)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_FROMLEBYTES_P521_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_fromlebytes_p521_windows_mc = define_from_elf
   "bignum_fromlebytes_p521_windows_mc" "x86/p521/bignum_fromlebytes_p521.obj";;

let bignum_fromlebytes_p521_windows_tmc = define_trimmed "bignum_fromlebytes_p521_windows_tmc" bignum_fromlebytes_p521_windows_mc;;

let BIGNUM_FROMLEBYTES_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x l pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_fromlebytes_p521_windows_tmc); (x,8 * 9)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 9) /\
      nonoverlapping (word pc,LENGTH bignum_fromlebytes_p521_windows_tmc) (z,8 * 9) /\
      (x = z \/ nonoverlapping (x,66) (z,8 * 9))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_fromlebytes_p521_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,66)) s = l)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = num_of_bytelist l)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_fromlebytes_p521_windows_tmc
   bignum_fromlebytes_p521_tmc BIGNUM_FROMLEBYTES_P521_CORRECT);;

let BIGNUM_FROMLEBYTES_P521_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x l pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_fromlebytes_p521_windows_mc); (x,8 * 9)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 9) /\
      nonoverlapping (word pc,LENGTH bignum_fromlebytes_p521_windows_mc) (z,8 * 9) /\
      (x = z \/ nonoverlapping (x,66) (z,8 * 9))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_fromlebytes_p521_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,66)) s = l)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = num_of_bytelist l)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_FROMLEBYTES_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

