(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* MULX-based 6x6->12 squaring.                                              *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/fastmul/bignum_sqr_6_12.o";;
 ****)

let bignum_sqr_6_12_mc =
  define_assert_from_elf "bignum_sqr_6_12_mc" "x86/fastmul/bignum_sqr_6_12.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4e; 0x08;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0xc4; 0x62; 0xab; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% r11,% r10) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0xc4; 0x62; 0x9b; 0xf6; 0x6e; 0x28;
                           (* MULX4 (% r13,% r12) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0x62; 0x8b; 0xf6; 0x7e; 0x20;
                           (* MULX4 (% r15,% r14) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x0e;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x08;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x18;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x28;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADCX (% r14) (% rbp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADOX (% r15) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADCX (% r15) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x56; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rsi,32))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x0e;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x18;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x28;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADOX (% rbx) (% rbp) *)
  0x48; 0x8b; 0x56; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rsi,32))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x6e; 0x28;
                           (* MULX4 (% rbp,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% rbx) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADOX (% rbp) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% rbp) (% rax) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% r8) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% r8) (% rdx) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x89; 0x47; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADOX (% r9) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% r10) (% r10) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADOX (% r10) (% rdx) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x89; 0x4f; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% r11) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADOX (% r11) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe4;
                           (* ADCX (% r12) (% r12) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe2;
                           (* ADOX (% r12) (% rdx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x89; 0x57; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r10) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% r13) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADOX (% r13) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf2;
                           (* ADOX (% r14) (% rdx) *)
  0x48; 0x8b; 0x56; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x89; 0x5f; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xff;
                           (* ADCX (% r15) (% r15) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADOX (% r15) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% rbx) (% rbx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xda;
                           (* ADOX (% rbx) (% rdx) *)
  0x48; 0x8b; 0x56; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x89; 0x67; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x4c; 0x89; 0x6f; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r13) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% rbp) (% rbp) *)
  0x4c; 0x89; 0x77; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r14) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADOX (% rbp) (% rax) *)
  0x4c; 0x89; 0x7f; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r15) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x89; 0x5f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% rbx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% rdx) (% rax) *)
  0x48; 0x89; 0x6f; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% rbp) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% rdx) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0xc3                     (* RET *)
];;

let bignum_sqr_6_12_tmc = define_trimmed "bignum_sqr_6_12_tmc" bignum_sqr_6_12_mc;;

let BIGNUM_SQR_6_12_EXEC = X86_MK_CORE_EXEC_RULE bignum_sqr_6_12_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SQR_6_12_CORRECT = time prove
 (`!z x a pc.
     nonoverlapping (word pc,0x220) (z,8 * 12) /\
     (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 12))
     ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST bignum_sqr_6_12_tmc) /\
               read RIP s = word(pc + 0x0a) /\
               C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,6) s = a)
          (\s. read RIP s = word (pc + 0x215) /\
               bignum_from_memory (z,12) s = a EXP 2)
          (MAYCHANGE [RIP; RAX; RBP; RBX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(z,8 * 12)] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  X86_ACCSTEPS_TAC BIGNUM_SQR_6_12_EXEC (1--100) (1--100) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let BIGNUM_SQR_6_12_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 48),56) (z,8 * 12) /\
     ALL (nonoverlapping (word_sub stackpointer (word 48),48))
         [(word pc,LENGTH bignum_sqr_6_12_tmc); (x,8 * 6)] /\
     nonoverlapping (word pc,LENGTH bignum_sqr_6_12_tmc) (z,8 * 12) /\
     (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 12))
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_sqr_6_12_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,6) s = a)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,12) s = a EXP 2)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 12);
                      memory :> bytes(word_sub stackpointer (word 48),48)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_sqr_6_12_tmc BIGNUM_SQR_6_12_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_SQR_6_12_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 48),56) (z,8 * 12) /\
     ALL (nonoverlapping (word_sub stackpointer (word 48),48))
         [(word pc,LENGTH bignum_sqr_6_12_mc); (x,8 * 6)] /\
     nonoverlapping (word pc,LENGTH bignum_sqr_6_12_mc) (z,8 * 12) /\
     (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 12))
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_sqr_6_12_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,6) s = a)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,12) s = a EXP 2)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 12);
                      memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SQR_6_12_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_sqr_6_12_windows_mc = define_from_elf
   "bignum_sqr_6_12_windows_mc" "x86/fastmul/bignum_sqr_6_12.obj";;

let bignum_sqr_6_12_windows_tmc = define_trimmed "bignum_sqr_6_12_windows_tmc" bignum_sqr_6_12_windows_mc;;

let BIGNUM_SQR_6_12_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 64),72) (z,8 * 12) /\
     ALL (nonoverlapping (word_sub stackpointer (word 64),64))
         [(word pc,LENGTH bignum_sqr_6_12_windows_tmc); (x,8 * 6)] /\
     nonoverlapping (word pc,LENGTH bignum_sqr_6_12_windows_tmc) (z,8 * 12) /\
     (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 12))
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_sqr_6_12_windows_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,6) s = a)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,12) s = a EXP 2)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 12);
                      memory :> bytes(word_sub stackpointer (word 64),64)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_sqr_6_12_windows_tmc bignum_sqr_6_12_tmc
    BIGNUM_SQR_6_12_CORRECT `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_SQR_6_12_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 64),72) (z,8 * 12) /\
     ALL (nonoverlapping (word_sub stackpointer (word 64),64))
         [(word pc,LENGTH bignum_sqr_6_12_windows_mc); (x,8 * 6)] /\
     nonoverlapping (word pc,LENGTH bignum_sqr_6_12_windows_mc) (z,8 * 12) /\
     (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 12))
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_sqr_6_12_windows_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,6) s = a)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,12) s = a EXP 2)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 12);
                      memory :> bytes(word_sub stackpointer (word 64),64)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SQR_6_12_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

