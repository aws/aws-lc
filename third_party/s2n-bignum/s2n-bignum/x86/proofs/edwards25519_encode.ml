(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Encoding of point on edwards25519 in its compressed form.                 *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/ecencoding.ml";;

(**** print_literal_from_elf "x86/curve25519/edwards25519_encode.o";;
 ****)

let edwards25519_encode_mc =
  define_assert_from_elf "edwards25519_encode_mc" "x86/curve25519/edwards25519_encode.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x4c; 0x8b; 0x0e;        (* MOV (% r9) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x8b; 0x4e; 0x28;  (* MOV (% rcx) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x8b; 0x56; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x8b; 0x46; 0x38;  (* MOV (% r8) (Memop Quadword (%% (rsi,56))) *)
  0x49; 0x0f; 0xba; 0xf0; 0x3f;
                           (* BTR (% r8) (Imm8 (word 63)) *)
  0x49; 0xc1; 0xe1; 0x3f;  (* SHL (% r9) (Imm8 (word 63)) *)
  0x4d; 0x09; 0xc8;        (* OR (% r8) (% r9) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x48; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rdx) *)
  0x4c; 0x89; 0x47; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r8) *)
  0xc3                     (* RET *)
];;

let edwards25519_encode_tmc = define_trimmed "edwards25519_encode_tmc" edwards25519_encode_mc;;

let EDWARDS25519_ENCODE_EXEC = X86_MK_CORE_EXEC_RULE edwards25519_encode_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = define `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let ed25519_encode = new_definition
  `ed25519_encode (X,Y) =
        let x = num_of_int(X rem &p_25519)
        and y = num_of_int(Y rem &p_25519) in
        2 EXP 255 * x MOD 2 + y`;;

let EDWARDS25519_ENCODE_CORRECT = prove
 (`!z p x y pc.
      nonoverlapping (word pc,0x2f) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST edwards25519_encode_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; p] s /\
                bignum_pair_from_memory(p,4) s = (x,y))
           (\s. read RIP s = word (pc + 0x2e) /\
                (x < p_25519 /\ y < p_25519
                ==> read (memory :> bytelist(z,32)) s =
                    bytelist_of_num 32 (ed25519_encode (&x,&y))))
           (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R9] ,,
            MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [memory :> bytes(z,32)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `p:int64`; `x:num`; `y:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              PAIR_EQ; bignum_pair_from_memory] THEN
  STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `read (memory :> bytes (p,8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y_"
   `read (memory :> bytes (word_add p (word 32),8 * 4)) s0` THEN
  X86_STEPS_TAC EDWARDS25519_ENCODE_EXEC (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  REWRITE_TAC[ARITH_RULE `32 = 8 * 4 /\ 256 EXP (8 * 4) = 2 EXP (8 * 32)`] THEN
  MATCH_MP_TAC(MESON[MOD_LT] `x < e /\ x = y ==> x = y MOD e`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[]] THEN
  DISCARD_STATE_TAC "s12" THEN
  ASM_SIMP_TAC[ed25519_encode; INT_OF_NUM_REM; MOD_LT; NUM_OF_INT_OF_NUM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `y = y MOD 2 EXP 255` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `y < p_25519` THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
  REWRITE_TAC[ARITH_RULE
   `z = x + y MOD 2 EXP 255 <=>
    2 EXP 255 * y DIV 2 EXP 255 + z = x + y`] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(1,3)] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 * x = 2 * 2 EXP 63 * x`; MOD_MULT_ADD] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
  REWRITE_TAC[bignum_of_wordlist] THEN
  CONV_TAC WORD_BLAST);;

let EDWARDS25519_ENCODE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!z p x y pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,32) /\
      nonoverlapping (word pc,LENGTH edwards25519_encode_tmc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) edwards25519_encode_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; p] s /\
                bignum_pair_from_memory(p,4) s = (x,y))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (x < p_25519 /\ y < p_25519
                ==> read (memory :> bytelist(z,32)) s =
                    bytelist_of_num 32 (ed25519_encode (&x,&y))))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,32)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC edwards25519_encode_tmc
    EDWARDS25519_ENCODE_CORRECT);;

let EDWARDS25519_ENCODE_SUBROUTINE_CORRECT = prove
 (`!z p x y pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,32) /\
      nonoverlapping (word pc,LENGTH edwards25519_encode_mc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) edwards25519_encode_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; p] s /\
                bignum_pair_from_memory(p,4) s = (x,y))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (x < p_25519 /\ y < p_25519
                ==> read (memory :> bytelist(z,32)) s =
                    bytelist_of_num 32 (ed25519_encode (&x,&y))))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE EDWARDS25519_ENCODE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let edwards25519_encode_windows_mc = define_from_elf
   "edwards25519_encode_windows_mc" "x86/curve25519/edwards25519_encode.obj";;

let edwards25519_encode_windows_tmc = define_trimmed "edwards25519_encode_windows_tmc" edwards25519_encode_windows_mc;;

let EDWARDS25519_ENCODE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z p x y pc stackpointer returnaddress.
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,LENGTH edwards25519_encode_windows_tmc); (p,8 * 8)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,32) /\
      nonoverlapping (word pc,LENGTH edwards25519_encode_windows_tmc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) edwards25519_encode_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; p] s /\
                bignum_pair_from_memory(p,4) s = (x,y))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (x < p_25519 /\ y < p_25519
                ==> read (memory :> bytelist(z,32)) s =
                    bytelist_of_num 32 (ed25519_encode (&x,&y))))
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,32);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    edwards25519_encode_windows_tmc edwards25519_encode_tmc
    EDWARDS25519_ENCODE_CORRECT);;

let EDWARDS25519_ENCODE_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z p x y pc stackpointer returnaddress.
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,LENGTH edwards25519_encode_windows_mc); (p,8 * 8)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,32) /\
      nonoverlapping (word pc,LENGTH edwards25519_encode_windows_mc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) edwards25519_encode_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; p] s /\
                bignum_pair_from_memory(p,4) s = (x,y))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (x < p_25519 /\ y < p_25519
                ==> read (memory :> bytelist(z,32)) s =
                    bytelist_of_num 32 (ed25519_encode (&x,&y))))
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,32);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE EDWARDS25519_ENCODE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

