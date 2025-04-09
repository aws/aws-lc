(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 59 divstep iterations.                                                    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "Divstep/idivstep.ml";;

(* ------------------------------------------------------------------------- *)
(* The code.                                                                 *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "x86/generic/word_divstep59.o";;
 ****)

let word_divstep59_mc = define_assert_from_elf "word_divstep59_mc" "x86/generic/word_divstep59.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x48; 0x89; 0xd3;        (* MOV (% rbx) (% rdx) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0x81; 0xe3; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rbx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0xfe; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446741874686296064)) *)
  0x48; 0x09; 0xc3;        (* OR (% rbx) (% rax) *)
  0x49; 0x89; 0xcd;        (* MOV (% r13) (% rcx) *)
  0x48; 0x81; 0xe1; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rcx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xc0;
                           (* MOV (% rax) (Imm64 (word 13835058055282163712)) *)
  0x48; 0x09; 0xc1;        (* OR (% rcx) (% rax) *)
  0x48; 0xc7; 0xc0; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294967294)) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xba; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 2)) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0xf7; 0xc1; 0x01; 0x00; 0x00; 0x00;
                           (* TEST (% rcx) (Imm32 (word 1)) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0xb8; 0x00; 0x00; 0x10; 0x00;
                           (* MOV (% eax) (Imm32 (word 1048576)) *)
  0x4c; 0x8d; 0x04; 0x03;  (* LEA (% r8) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x14; 0x01;  (* LEA (% r10) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xe0; 0x16;  (* SHL (% r8) (Imm8 (word 22)) *)
  0x49; 0xc1; 0xe2; 0x16;  (* SHL (% r10) (Imm8 (word 22)) *)
  0x49; 0xc1; 0xf8; 0x2b;  (* SAR (% r8) (Imm8 (word 43)) *)
  0x49; 0xc1; 0xfa; 0x2b;  (* SAR (% r10) (Imm8 (word 43)) *)
  0x48; 0xb8; 0x00; 0x00; 0x10; 0x00; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 2199024304128)) *)
  0x4c; 0x8d; 0x0c; 0x03;  (* LEA (% r9) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x1c; 0x01;  (* LEA (% r11) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xf9; 0x2a;  (* SAR (% r9) (Imm8 (word 42)) *)
  0x49; 0xc1; 0xfb; 0x2a;  (* SAR (% r11) (Imm8 (word 42)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x4d; 0x0f; 0xaf; 0xd4;  (* IMUL (% r10) (% r12) *)
  0x4d; 0x0f; 0xaf; 0xe0;  (* IMUL (% r12) (% r8) *)
  0x4d; 0x0f; 0xaf; 0xcd;  (* IMUL (% r9) (% r13) *)
  0x4d; 0x0f; 0xaf; 0xeb;  (* IMUL (% r13) (% r11) *)
  0x4d; 0x01; 0xcc;        (* ADD (% r12) (% r9) *)
  0x4d; 0x01; 0xd5;        (* ADD (% r13) (% r10) *)
  0x49; 0xc1; 0xfc; 0x14;  (* SAR (% r12) (Imm8 (word 20)) *)
  0x49; 0xc1; 0xfd; 0x14;  (* SAR (% r13) (Imm8 (word 20)) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0x81; 0xe3; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rbx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0xfe; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446741874686296064)) *)
  0x48; 0x09; 0xc3;        (* OR (% rbx) (% rax) *)
  0x4c; 0x89; 0xe9;        (* MOV (% rcx) (% r13) *)
  0x48; 0x81; 0xe1; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rcx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xc0;
                           (* MOV (% rax) (Imm64 (word 13835058055282163712)) *)
  0x48; 0x09; 0xc1;        (* OR (% rcx) (% rax) *)
  0x48; 0xc7; 0xc0; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294967294)) *)
  0xba; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 2)) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0xf7; 0xc1; 0x01; 0x00; 0x00; 0x00;
                           (* TEST (% rcx) (Imm32 (word 1)) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0xb8; 0x00; 0x00; 0x10; 0x00;
                           (* MOV (% eax) (Imm32 (word 1048576)) *)
  0x4c; 0x8d; 0x04; 0x03;  (* LEA (% r8) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x14; 0x01;  (* LEA (% r10) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xe0; 0x16;  (* SHL (% r8) (Imm8 (word 22)) *)
  0x49; 0xc1; 0xe2; 0x16;  (* SHL (% r10) (Imm8 (word 22)) *)
  0x49; 0xc1; 0xf8; 0x2b;  (* SAR (% r8) (Imm8 (word 43)) *)
  0x49; 0xc1; 0xfa; 0x2b;  (* SAR (% r10) (Imm8 (word 43)) *)
  0x48; 0xb8; 0x00; 0x00; 0x10; 0x00; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 2199024304128)) *)
  0x4c; 0x8d; 0x0c; 0x03;  (* LEA (% r9) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x1c; 0x01;  (* LEA (% r11) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xf9; 0x2a;  (* SAR (% r9) (Imm8 (word 42)) *)
  0x49; 0xc1; 0xfb; 0x2a;  (* SAR (% r11) (Imm8 (word 42)) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x4c; 0x89; 0xe1;        (* MOV (% rcx) (% r12) *)
  0x4d; 0x0f; 0xaf; 0xe0;  (* IMUL (% r12) (% r8) *)
  0x49; 0x0f; 0xaf; 0xd9;  (* IMUL (% rbx) (% r9) *)
  0x49; 0x01; 0xdc;        (* ADD (% r12) (% rbx) *)
  0x4d; 0x0f; 0xaf; 0xeb;  (* IMUL (% r13) (% r11) *)
  0x49; 0x0f; 0xaf; 0xca;  (* IMUL (% rcx) (% r10) *)
  0x49; 0x01; 0xcd;        (* ADD (% r13) (% rcx) *)
  0x49; 0xc1; 0xfc; 0x14;  (* SAR (% r12) (Imm8 (word 20)) *)
  0x49; 0xc1; 0xfd; 0x14;  (* SAR (% r13) (Imm8 (word 20)) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0x81; 0xe3; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rbx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0xfe; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446741874686296064)) *)
  0x48; 0x09; 0xc3;        (* OR (% rbx) (% rax) *)
  0x4c; 0x89; 0xe9;        (* MOV (% rcx) (% r13) *)
  0x48; 0x81; 0xe1; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rcx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xc0;
                           (* MOV (% rax) (Imm64 (word 13835058055282163712)) *)
  0x48; 0x09; 0xc1;        (* OR (% rcx) (% rax) *)
  0x48; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x49; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% r8) *)
  0x48; 0x8b; 0x57; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x49; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% r9) *)
  0x4c; 0x0f; 0xaf; 0x47; 0x08;
                           (* IMUL (% r8) (Memop Quadword (%% (rdi,8))) *)
  0x4c; 0x0f; 0xaf; 0x4f; 0x18;
                           (* IMUL (% r9) (Memop Quadword (%% (rdi,24))) *)
  0x4d; 0x01; 0xc1;        (* ADD (% r9) (% r8) *)
  0x4c; 0x8d; 0x04; 0x10;  (* LEA (% r8) (%%% (rax,0,rdx)) *)
  0x48; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x49; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% r10) *)
  0x48; 0x8b; 0x57; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x49; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% r11) *)
  0x4c; 0x0f; 0xaf; 0x57; 0x08;
                           (* IMUL (% r10) (Memop Quadword (%% (rdi,8))) *)
  0x4c; 0x0f; 0xaf; 0x5f; 0x18;
                           (* IMUL (% r11) (Memop Quadword (%% (rdi,24))) *)
  0x4d; 0x01; 0xd3;        (* ADD (% r11) (% r10) *)
  0x4c; 0x8d; 0x14; 0x10;  (* LEA (% r10) (%%% (rax,0,rdx)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0xc7; 0xc0; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294967294)) *)
  0xba; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 2)) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0xf7; 0xc1; 0x01; 0x00; 0x00; 0x00;
                           (* TEST (% rcx) (Imm32 (word 1)) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x4c; 0x0f; 0x44; 0xcd;  (* CMOVE (% r9) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd6;        (* ADD (% rsi) (% rdx) *)
  0x4a; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,r9)) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0xb8; 0x00; 0x00; 0x10; 0x00;
                           (* MOV (% eax) (Imm32 (word 1048576)) *)
  0x4c; 0x8d; 0x04; 0x03;  (* LEA (% r8) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x14; 0x01;  (* LEA (% r10) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xe0; 0x15;  (* SHL (% r8) (Imm8 (word 21)) *)
  0x49; 0xc1; 0xe2; 0x15;  (* SHL (% r10) (Imm8 (word 21)) *)
  0x49; 0xc1; 0xf8; 0x2b;  (* SAR (% r8) (Imm8 (word 43)) *)
  0x49; 0xc1; 0xfa; 0x2b;  (* SAR (% r10) (Imm8 (word 43)) *)
  0x48; 0xb8; 0x00; 0x00; 0x10; 0x00; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 2199024304128)) *)
  0x4c; 0x8d; 0x0c; 0x03;  (* LEA (% r9) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x1c; 0x01;  (* LEA (% r11) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xf9; 0x2b;  (* SAR (% r9) (Imm8 (word 43)) *)
  0x49; 0xc1; 0xfb; 0x2b;  (* SAR (% r11) (Imm8 (word 43)) *)
  0x48; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x49; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% r8) *)
  0x48; 0x8b; 0x57; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x49; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% r9) *)
  0x4c; 0x0f; 0xaf; 0x47; 0x08;
                           (* IMUL (% r8) (Memop Quadword (%% (rdi,8))) *)
  0x4c; 0x0f; 0xaf; 0x4f; 0x18;
                           (* IMUL (% r9) (Memop Quadword (%% (rdi,24))) *)
  0x4d; 0x01; 0xc1;        (* ADD (% r9) (% r8) *)
  0x4c; 0x8d; 0x04; 0x10;  (* LEA (% r8) (%%% (rax,0,rdx)) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x49; 0xf7; 0xd8;        (* NEG (% r8) *)
  0x48; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x49; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% r10) *)
  0x48; 0x8b; 0x57; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x49; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% r11) *)
  0x4c; 0x0f; 0xaf; 0x57; 0x08;
                           (* IMUL (% r10) (Memop Quadword (%% (rdi,8))) *)
  0x4c; 0x0f; 0xaf; 0x5f; 0x18;
                           (* IMUL (% r11) (Memop Quadword (%% (rdi,24))) *)
  0x4d; 0x01; 0xd3;        (* ADD (% r11) (% r10) *)
  0x4c; 0x8d; 0x14; 0x10;  (* LEA (% r10) (%%% (rax,0,rdx)) *)
  0x49; 0xf7; 0xdb;        (* NEG (% r11) *)
  0x49; 0xf7; 0xda;        (* NEG (% r10) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x89; 0xf0;        (* MOV (% rax) (% rsi) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let word_divstep59_tmc = define_trimmed "word_divstep59_tmc" word_divstep59_mc;;

let WORD_DIVSTEP59_EXEC = X86_MK_CORE_EXEC_RULE word_divstep59_tmc;;

(* ------------------------------------------------------------------------- *)
(* Some not-very-general lemmas.                                             *)
(* ------------------------------------------------------------------------- *)

let BIT_1_WORD_ISHR = prove
 (`!x:int64. bit 1 x = bit 0 (word_ishr x 1)`,
  CONV_TAC WORD_BLAST);;

let VAL_WORD_AND_2_ISHR = prove
 (`!x:int64. val(word_and x (word 2)) = 0 <=> ~bit 0 (word_ishr x 1)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `2 = 2 EXP 1`] THEN
  REWRITE_TAC[VAL_WORD_AND_POW2; GSYM BIT_1_WORD_ISHR] THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let lemma1,lemma2 = (CONJ_PAIR o prove)
 (`(--(&2 pow 20) <= h /\ h < &2 pow 20 /\ &0 <= l /\ l < &2 pow 43
    ==> word_ishr (iword(&2 pow 43 * h + l):int64) 43 = iword h) /\
   (--(&2 pow 20) <= h /\ h < &2 pow 20 /\ &0 <= l /\ l < &2 pow 42
    ==> word_ishr (iword(&2 pow 42 * h + l):int64) 42 = iword h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ishr] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
  EXISTS_TAC `l:int` THEN ASM_REWRITE_TAC[INT_ABS_POW; INT_ABS_NUM] THEN
  REWRITE_TAC[INT_MUL_SYM] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Definitions and lemmas about packed representations, and common tactics.  *)
(* ------------------------------------------------------------------------- *)

let divstep_fvec = define
 `divstep_fvec n (d,f,g) =
    divstep_f n (d,f rem &2 pow 20,g rem &2 pow 20) -
    &2 pow (41 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$1$1 -
    &2 pow (62 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$1$2`;;

let divstep_gvec = define
 `divstep_gvec n (d,f,g) =
    divstep_g n (d,f rem &2 pow 20,g rem &2 pow 20) -
    &2 pow (41 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$2$1 -
    &2 pow (62 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$2$2`;;

let divstep_dvec = define
 `divstep_dvec n (d,f,g) =
  divstep_d n (d,f rem &2 pow 20,g rem &2 pow 20)`;;

let DIVSTEP_DVEC_BOUND = prove
 (`!n d f g. abs(divstep_dvec n (d,f,g)) <= abs(d) + &2 * &n`,
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  REWRITE_TAC[divstep_dvec] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[DIVSTEP_D; GSYM INT_OF_NUM_SUC] THEN
  ASM_INT_ARITH_TAC);;

let DIVSTEP_DVEC_PARITY = prove
 (`!n d f g. divstep_dvec n (d,f,g) rem &2 = d rem &2`,
  REWRITE_TAC[divstep_dvec; DIVSTEP_D_PARITY]);;

let DIVSTEP_FVEC_PARITY = prove
 (`!n d f g.
        n <= 20
        ==> divstep_fvec n (d,f,g) rem &2 =
            divstep_f n (d,f rem &2 pow 20,g rem &2 pow 20) rem &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[divstep_fvec; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `n pow 1 divides p /\ n pow 1 divides q
    ==> (x - p * a - q * b:int == x) (mod n)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ASM_ARITH_TAC);;

let DIVSTEP_FVEC_ODD = prove
 (`!n d f g.
        n <= 20 /\ f rem &2 = &1
        ==> divstep_fvec n (d,f,g) rem &2 = &1`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DIVSTEP_FVEC_PARITY] THEN
  MATCH_MP_TAC DIVSTEP_F_ODD THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [INT_ARITH `&2:int = &2 pow 1`] THEN
  REWRITE_TAC[INT_REM_REM_POW_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[INT_POW_1]);;

let DIVSTEP_GVEC_PARITY = prove
 (`!n d f g.
        n <= 20
        ==> divstep_gvec n (d,f,g) rem &2 =
            divstep_g n (d,f rem &2 pow 20,g rem &2 pow 20) rem &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[divstep_gvec; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `n pow 1 divides p /\ n pow 1 divides q
    ==> (x - p * a - q * b:int == x) (mod n)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ASM_ARITH_TAC);;

let DIVSTEP_DVEC = prove
 (`(!d f g. divstep_dvec 0 (d,f,g) = d) /\
   (!n t. n <= 20
          ==> divstep_dvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then &2 - divstep_dvec n t else &2 + divstep_dvec n t)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_dvec; DIVSTEP_D] THEN
  SIMP_TAC[DIVSTEP_GVEC_PARITY]);;

let DIVSTEP_FVEC = prove
 (`(!d f g. divstep_fvec 0 (d,f,g) = f rem &2 pow 20 - &2 pow 41) /\
   (!n t. n <= 20
          ==> divstep_fvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then divstep_gvec n t else divstep_fvec n t)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_fvec; DIVSTEP_F; divstep_mat] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  CONJ_TAC THENL [CONV_TAC INT_ARITH; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `d:int`; `f:int`; `g:int`] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[DIVSTEP_GVEC_PARITY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[divstep_dvec; divstep_gvec] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 41 - n = (41 - SUC n) + 1`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 62 - n = (62 - SUC n) + 1`] THEN
  REWRITE_TAC[INT_POW_ADD; INT_POW_1; GSYM INT_MUL_ASSOC] THEN
  SIMP_TAC[imat_mul; VECTOR_2; ISUM_2; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  INT_ARITH_TAC);;

let DIVSTEP_GVEC = prove
 (`(!d f g. divstep_gvec 0 (d,f,g) = g rem &2 pow 20 - &2 pow 62) /\
   (!n t. n <= 20
          ==> divstep_gvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then (divstep_gvec n t - divstep_fvec n t) div &2
              else (divstep_gvec n t +
                    divstep_gvec n t rem &2 * divstep_fvec n t) div &2)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_gvec; DIVSTEP_G; divstep_mat] THEN
  REWRITE_TAC[GSYM divstep_gvec] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  CONJ_TAC THENL [CONV_TAC INT_ARITH; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `d:int`; `f:int`; `g:int`] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[DIVSTEP_GVEC_PARITY] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[divstep_dvec; divstep_fvec; divstep_gvec] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 41 - n = 1 + (41 - SUC n)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 62 - n = 1 + (62 - SUC n)`] THEN
  REWRITE_TAC[INT_POW_ADD; INT_POW_1; GSYM INT_MUL_ASSOC] THEN
  REWRITE_TAC[INT_ARITH
   `(x - &2 * y - &2 * z) - (x' - &2 * y' - &2 * z'):int =
    (x - x') + &2 * ((y' + z') - (y + z))`] THEN
  REWRITE_TAC[INT_ARITH
   `(x - &2 * y - &2 * z) + b * (x' - &2 * y' - &2 * z'):int =
    (x + b * x') + &2 * --(b * (y' + z') + (y + z))`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_OF_NUM_EQ; ARITH_EQ] THEN
  SIMP_TAC[imat_mul; VECTOR_2; ISUM_2; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  INT_ARITH_TAC);;

let DIVSTEP_FGVEC_PACK = prove
 (`!d f g. word_or (word_and (iword f) (word 1048575))
                   (word 18446741874686296064):int64 =
           iword(divstep_fvec 0 (d,f,g)) /\
           word_or (word_and (iword g) (word 1048575))
                   (word 13835058055282163712):int64 =
           iword(divstep_gvec 0 (d,f,g))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC;
              DIVSTEP_F; DIVSTEP_G; divstep_mat] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  W(MP_TAC o PART_MATCH (rand o rand) WORD_ADD_OR o lhand o snd) THEN
  (ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  REWRITE_TAC[INT_SUB] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[IWORD_INT_ADD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_AND_MASK_WORD; GSYM(NUM_REDUCE_CONV `2 EXP 20 - 1`)] THEN
  REWRITE_TAC[WORD_IWORD; IWORD_EQ; GSYM INT_OF_NUM_CLAUSES; DIMINDEX_64] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC INT_EQ_IMP_CONG THEN REWRITE_TAC[INT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN REWRITE_TAC[VAL_IWORD_CONG] THEN
  REWRITE_TAC[DIMINDEX_64; GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REDUCE_CONV);;

let IVAL_IWORD_DVEC = prove
 (`!n d f g.
        abs(d) < &2 pow 63 - &2 * &n
        ==> ival(iword(divstep_dvec n (d,f,g)):int64) =
            divstep_dvec n (d,f,g)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`n:num`; `d:int`; `f:int`; `g:int`] DIVSTEP_DVEC_BOUND) THEN
  ASM_INT_ARITH_TAC);;

let DIVSTEP_FVEC_BOUNDS,DIVSTEP_GVEC_BOUNDS = (CONJ_PAIR o prove)
 (`(!n d f g.
        n <= 20
        ==> --(&2 pow 62) <= divstep_fvec n (d,f,g) /\
            divstep_fvec n (d,f,g) < &2 pow 62) /\
   (!n d f g.
        n <= 20
        ==> --(&2 pow 62) <= divstep_gvec n (d,f,g) /\
            divstep_gvec n (d,f,g) < &2 pow 62)`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  REWRITE_TAC[divstep_dvec] THEN INDUCT_TAC THENL
   [REWRITE_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC; ARITH] THEN
    MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_DIVISION) THEN
    MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_DIVISION) THEN
    INT_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o MATCH_MP
     (ARITH_RULE `SUC n <= 20 ==> n <= 20`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_SIMP_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC] THEN STRIP_TAC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_LE_DIV_EQ; INT_DIV_LT_EQ;  INT_ARITH `(&0:int) < &2`] THEN
  DISJ_CASES_THEN SUBST1_TAC
   (SPEC `divstep_gvec n (d,f,g)` INT_REM_2_CASES) THEN
  ASM_INT_ARITH_TAC);;

let PACKED_DIVSTEP_TAC n shf s =
  let s' = if mem n shf then s+7 else s+12 in
  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (s--s') THEN
  SUBGOAL_THEN
   (subst [mk_small_numeral(n-1),`n:num`;
           mk_var("s"^string_of_int s',`:x86state`),`s:x86state`]
     `read RSI s = iword(divstep_dvec (SUC n) (d,f,g)) /\
      read RBX s = iword(divstep_fvec (SUC n) (d,f,g)) /\
      read RCX s = iword(divstep_gvec (SUC n) (d,f,g))`)
  MP_TAC THENL
   [ASM_REWRITE_TAC[WORD_AND_1_BITVAL] THEN
    REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_EQ_0] THEN
    SIMP_TAC(ARITH::map CONJUNCT2
     [DIVSTEP_DVEC; DIVSTEP_FVEC; DIVSTEP_GVEC]) THEN
    REWRITE_TAC[COND_SWAP; INT_ARITH `~(x:int < &0) <=> x >= &0`] THEN
    REWRITE_TAC[BIT_LSB_IWORD] THEN
    MP_TAC(ISPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
      IVAL_IWORD_DVEC) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
       `abs(d:int) < a ==> a <= b ==> abs(d) < b`)) THEN
      CONV_TAC INT_ARITH;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MESON[]
     `(if p /\ q then x else y) =
      (if p then if q then x else y else y)`] THEN
    REWRITE_TAC[COND_SWAP; INT_ARITH `x:int < &0 <=> ~(x >= &0)`] THEN
    DISJ_CASES_THEN SUBST1_TAC
       (SPEC(subst [mk_small_numeral(n - 1),`n:num`] `divstep_gvec n (d,f,g)`)
          INT_REM_2_CASES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_MUL_LID; INT_ADD_RID] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[WORD_XOR_0; WORD_ADD_0; WORD_BLAST
     `word_xor (x:int64) (word 18446744073709551614) =
      word_sub (word_neg x) (word_shl (word(bitval(~bit 0 x))) 1)`] THEN
    REWRITE_TAC[BIT_LSB_IWORD] THEN
    ASM_SIMP_TAC[DIVSTEP_FVEC_ODD; DIVSTEP_DVEC_PARITY; ARITH_LT; ARITH_LE;
                 BITVAL_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    REWRITE_TAC[word_ishr; WORD_SUB_0] THEN AP_TERM_TAC THEN
    REWRITE_TAC[WORD_ADD_0; INT_POW_1; MULT_CLAUSES; WORD_VAL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[WORD_RULE `word_add x (word_neg y) = word_sub x y`] THEN
    REWRITE_TAC[GSYM IWORD_INT_ADD; GSYM IWORD_INT_SUB] THEN
    MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    MP_TAC(SPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
     DIVSTEP_FVEC_BOUNDS) THEN
    MP_TAC(SPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
     DIVSTEP_GVEC_BOUNDS) THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read RCX s = x`) o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read RBX s = x`) o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read RSI s = x`) o concl)) THEN
    RULE_ASSUM_TAC(PURE_REWRITE_RULE [VAL_WORD_AND_2_ISHR]) THEN
    REPLICATE_TAC 3 (DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_SUC_CONV)) THEN
    DISCH_THEN(fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN STRIP_ASSUME_TAC th)];;

let RENAME_DFG_TAC d0 f0 g0 =
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`f:int`,f0) THEN
  SPEC_TAC(`g:int`,g0) THEN
  SPEC_TAC(`d:int`,d0) THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read RSI s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read R12 s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read R13 s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th));;

let DIVSTEP_MAT_UNPACK_20 = prove
 (`word_ishr
    (word_shl (word_add (iword (divstep_fvec 20 (d,f,g))) (word 1048576)) 22)
    43:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$1$1)) /\
   word_ishr (word_add (iword (divstep_fvec 20 (d,f,g))) (word 2199024304128))
             42:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$1$2)) /\
   word_ishr
    (word_shl (word_add (iword (divstep_gvec 20 (d,f,g))) (word 1048576)) 22)
    43:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$2$1)) /\
   word_ishr (word_add (iword (divstep_gvec 20 (d,f,g))) (word 2199024304128))
             42:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$2$2))`,
  REWRITE_TAC[WORD_RULE `word_add (iword x) (word y) = iword(x + &y)`] THEN
  REWRITE_TAC[WORD_SHL_IWORD] THEN
  REWRITE_TAC[divstep_fvec; divstep_gvec] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_ARITH
   `&2 pow 22 * (l - &2 pow 21 * m - &2 pow 42 * h + z):int =
    &2 pow 64 * --h + &2 pow 43 * --m + &2 pow 22 * (l + z)`] THEN
  REWRITE_TAC[INT_ARITH
   `l - &2 pow 21 * m - &2 pow 42 * h + z:int =
    &2 pow 42 * --h + &2 pow 21 * --m + (l + z)`] THEN
  ONCE_REWRITE_TAC[GSYM IWORD_REM_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64; INT_REM_MUL_ADD] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; IWORD_REM_SIZE] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC lemma1 ORELSE MATCH_MP_TAC lemma2) THEN
  MP_TAC(SPECL [`20`; `(d:int,f rem &2 pow 20,g rem &2 pow 20)`]
        DIVSTEP_MAT_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `20`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_F_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `20`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_G_BOUNDS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let DIVSTEP_MAT_UNPACK_19 = prove
 (`word_ishr
    (word_shl (word_add (iword (divstep_fvec 19 (d,f,g))) (word 1048576)) 21)
    43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$1$1)) /\
   word_ishr (word_add (iword(divstep_fvec 19 (d,f,g)):int64)
                       (word 2199024304128)) 43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$1$2)) /\
   word_ishr
    (word_shl (word_add (iword (divstep_gvec 19 (d,f,g))) (word 1048576)) 21)
    43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$2$1)) /\
   word_ishr (word_add (iword(divstep_gvec 19 (d,f,g)):int64)
                       (word 2199024304128)) 43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$2$2))`,
  REWRITE_TAC[WORD_RULE `word_add (iword x) (word y) = iword(x + &y)`] THEN
  REWRITE_TAC[WORD_SHL_IWORD] THEN
  REWRITE_TAC[divstep_fvec; divstep_gvec] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_ARITH
   `&2 pow 21 * (l - &2 pow 22 * m - &2 pow 43 * h + z):int =
    &2 pow 64 * --h + &2 pow 43 * --m + &2 pow 21 * (l + z)`] THEN
  REWRITE_TAC[INT_ARITH
   `l - &2 pow 22 * m - &2 pow 43 * h + z:int =
    &2 pow 43 * --h + &2 pow 22 * --m + (l + z)`] THEN
  ONCE_REWRITE_TAC[GSYM IWORD_REM_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64; INT_REM_MUL_ADD] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; IWORD_REM_SIZE] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC lemma1 THEN
  MP_TAC(SPECL [`19`; `(d:int,f rem &2 pow 20,g rem &2 pow 20)`]
        DIVSTEP_MAT_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `19`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_F_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `19`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_G_BOUNDS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The overall correctness proof.                                            *)
(* ------------------------------------------------------------------------- *)

let WORD_DIVSTEP59_CORRECT = prove
 (`!m d f g pc.
   nonoverlapping (word pc,0xd1b) (m,32)
   ==> ensures x86
        (\s. bytes_loaded s (word pc) (BUTLAST word_divstep59_tmc) /\
             read RIP s = word(pc + 0x6) /\
             C_ARGUMENTS [m; d; f; g] s)
        (\s. read RIP s = word(pc + 0xd14) /\
             (ival d rem &2 = &1 /\
              ival f rem &2 = &1 /\
              abs(ival d) < &2 pow 62
          ==> C_RETURN s = iword(divstep_d 59 (ival d,ival f,ival g)) /\
              let M = divstep_mat 59 (ival d,ival f,ival g) in
              read (memory :> bytes64(m)) s = iword(M$1$1) /\
              read (memory :> bytes64(word_add m (word 8))) s = iword(M$1$2) /\
              read (memory :> bytes64(word_add m (word 16))) s = iword(M$2$1) /\
              read (memory :> bytes64(word_add m (word 24))) s = iword(M$2$2)))
          (MAYCHANGE [RIP; RDI; RSI; RAX; RBX; RCX; RDX; RBP;
                      R8; R9; R10; R11; R12; R13] ,,
           MAYCHANGE [memory :> bytes(m,32)] ,,
           MAYCHANGE SOME_FLAGS)`,
  X_GEN_TAC `m:int64` THEN
  MAP_EVERY
    (fun t -> GEN_REWRITE_TAC I [FORALL_IVAL_GEN] THEN
              X_GEN_TAC t THEN STRIP_TAC)
    [`d:int`; `f:int`; `g:int`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`]) THEN
  X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  STRIP_TAC THEN

  (*** Globalize the odd(d), odd(f) and |d| < 2^62 assumption ***)

  ASM_CASES_TAC `d rem &2 = &1 /\ f rem &2 = &1 /\ abs(d:int) < &2 pow 62` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    X86_QUICKSIM_TAC WORD_DIVSTEP59_EXEC [`read RDI s = x`] (1--908)] THEN

  (*** The first packing ***)

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read RSI s = a ==> !x. a = x ==> read RSI s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The first block of 20 divsteps ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (10--19) THEN
  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [20] (13*n+7)) (1--20) THEN

  (*** The unpacking of the first block ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (275--290) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_20]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** Application of first update matrix to f and g ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (291--298) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_ishr]) THEN

  (*** Renaming new values and checking d bound ***)

  SUBGOAL_THEN
    `abs(divstep_d 20 (d,f,g)) < &2 pow 62 + &40`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`20`; `d:int`; `f:int`; `g:int`] DIVSTEP_D_BOUND) THEN
    UNDISCH_TAC `abs(d:int) < &2 pow 62` THEN CONV_TAC INT_ARITH;
    ALL_TAC] THEN
  RENAME_DFG_TAC `d0:int` `f0:int` `g0:int` THEN

  (*** Get congruences on the new f and g, and prove oddness ***)

  SUBGOAL_THEN `d rem &2 = &1` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[DIVSTEP_D_PARITY] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(divstep_f 20 (d0,f0,g0) == --f) (mod (&2 pow 40)) /\
    (divstep_g 20 (d0,f0,g0) == --g) (mod (&2 pow 40))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`d0:int`; `f0:int`; `g0:int`; `20`] DIVSTEP_MAT) THEN
    ASM_SIMP_TAC[CART_EQ; FORALL_2; VECTOR_2; imat_vmul;
                 DIMINDEX_2; LAMBDA_BETA; ISUM_2] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
    SIMP_TAC[GSYM IWORD_INT_NEG; GSYM IWORD_INT_ADD; GSYM IWORD_INT_MUL] THEN
    SIMP_TAC[INT_ARITH `f * --m + --n * g:int = --(m * f + n * g)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [INT_ADD_SYM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(a:int == --b) (mod p) <=> (b == --a) (mod p)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_CONG_DIV THEN
    (CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[INT_MUL_RNEG] THEN MATCH_MP_TAC(INTEGER_RULE
     `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN
    REWRITE_TAC[IVAL_IWORD_CONG; GSYM INT_POW_ADD] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `f rem &2 = &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INT_REM_2_NEG] THEN
    TRANS_TAC EQ_TRANS `divstep_f 20 (d0,f0,g0) rem &2` THEN
    REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[DIVSTEP_F_ODD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(d:int == f) (mod p) ==> q pow 1 divides p ==> (f == d) (mod q)`)) THEN
    MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The second packing ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (299--306) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read RSI s = a ==> !x. a = x ==> read RSI s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The second block of 20 divsteps ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (307--315) THEN
  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [20] (13*n+303)) (1--20) THEN

  (*** The unpacking of the second block ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (571--582) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_20]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** Application of second update matrix to f and g ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (583--592) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_ishr]) THEN

  (*** Renaming new values and checking d bound ***)

  SUBGOAL_THEN
    `abs(divstep_d 20 (d,f,g)) < &2 pow 62 + &80`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`20`; `d:int`; `f:int`; `g:int`] DIVSTEP_D_BOUND) THEN
    UNDISCH_TAC `abs(d:int) < &2 pow 62 + &40` THEN CONV_TAC INT_ARITH;
    ALL_TAC] THEN
  RENAME_DFG_TAC `d1:int` `f1:int` `g1:int` THEN

  (*** Get congruences on the new f and g, and prove oddness ***)

  SUBGOAL_THEN `d rem &2 = &1` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[DIVSTEP_D_PARITY] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(divstep_f 20 (d1,f1,g1) == --f) (mod (&2 pow 40)) /\
    (divstep_g 20 (d1,f1,g1) == --g) (mod (&2 pow 40))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`d1:int`; `f1:int`; `g1:int`; `20`] DIVSTEP_MAT) THEN
    ASM_SIMP_TAC[CART_EQ; FORALL_2; VECTOR_2; imat_vmul;
                 DIMINDEX_2; LAMBDA_BETA; ISUM_2] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
    SIMP_TAC[GSYM IWORD_INT_NEG; GSYM IWORD_INT_ADD; GSYM IWORD_INT_MUL] THEN
    SIMP_TAC[INT_ARITH `f * --m + g * --n:int = --(m * f + n * g)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [INT_ADD_SYM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(a:int == --b) (mod p) <=> (b == --a) (mod p)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_CONG_DIV THEN
    (CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[INT_MUL_RNEG] THEN MATCH_MP_TAC(INTEGER_RULE
     `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN
    REWRITE_TAC[IVAL_IWORD_CONG; GSYM INT_POW_ADD] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `f rem &2 = &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INT_REM_2_NEG] THEN
    TRANS_TAC EQ_TRANS `divstep_f 20 (d1,f1,g1) rem &2` THEN
    REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[DIVSTEP_F_ODD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(d:int == f) (mod p) ==> q pow 1 divides p ==> (f == d) (mod q)`)) THEN
    MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The third and final packing ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (593--600) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read RSI s = a ==> !x. a = x ==> read RSI s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The multiplication of the first two matrices ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (601--620) THEN

  (*** The last 19 divsteps ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (621--629) THEN
  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [19] (13*n+617)) (1--19) THEN

  (*** The final unpacking is a little different as it's 19 not 20 ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (872--883) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_19]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** The final matrix multiplication and writeback ***)

  X86_STEPS_TAC WORD_DIVSTEP59_EXEC (884--908) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s908" THEN

  (*** The ending mathematics ***)

  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[IWORD_IVAL; IWORD_INT_SUB; IWORD_INT_NEG; IWORD_INT_ADD;
           IWORD_INT_MUL; WORD_ADD; WORD_MUL; ADD_CLAUSES; WORD_VAL] THEN
  REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_MUL; GSYM IWORD_INT_ADD;
              GSYM IWORD_INT_SUB; GSYM IWORD_INT_NEG] THEN
  SUBGOAL_THEN
   `divstep_d 59 (d0,f0,g0) = divstep_d 19 (d,f,g) /\
    divstep_mat 59 (d0,f0,g0) =
    imat_mul (divstep_mat 19 (d,f,g))
             (imat_mul (divstep_mat 20 (d1,f1,g1))
                       (divstep_mat 20 (d0,f0,g0)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[ARITH_RULE `59 = 19 + 40`; DIVSTEP_MAT_ADD; DIVSTEP_DFG_ADD];
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[imat_mul; LAMBDA_BETA; DIMINDEX_2; ARITH; ISUM_2] THEN
    INT_ARITH_TAC] THEN
  SUBGOAL_THEN
   `divstep_d 40 (d0,f0,g0) = d /\
    (divstep_f 40 (d0,f0,g0) == f) (mod (&2 pow 19)) /\
    (divstep_g 40 (d0,f0,g0) == g) (mod (&2 pow 19)) /\
    divstep_mat 40 (d0,f0,g0) =
    imat_mul (divstep_mat 20 (d1,f1,g1))
             (divstep_mat 20 (d0,f0,g0))`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[ARITH_RULE `59 = 19 + 40`;
                    DIVSTEP_MAT_ADD; DIVSTEP_DFG_ADD] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIVSTEP_D_CONGRUENCE;
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC DIVSTEP_MAT_CONGRUENCE] THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL
   [`40`; `d1:int`; `divstep_f 20 (d0,f0,g0)`; `divstep_g 20 (d0,f0,g0)`;
    `f1:int`; `g1:int`; `20`]
   DIVSTEP_CONGRUENCE_NEG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[DIVSTEP_F_ODD]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `40 = 20 + 20`;
                  DIVSTEP_DFG_ADD; DIVSTEP_MAT_ADD] THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
   `(x:int == y) (mod p) ==> (y == z) (mod p) /\ q divides p
    ==> (x == z) (mod q)`)) THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(--x:int == y) (mod p) <=> (x == --y) (mod p)`] THEN
  SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
   `(x:int == y) (mod p) ==> q divides p ==> (x == y) (mod q)`)) THEN
  SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT]);;

let WORD_DIVSTEP59_NOIBT_SUBROUTINE_CORRECT = prove
 (`!m d f g pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 32),40) (m,32) /\
     ALL (nonoverlapping (word pc,LENGTH word_divstep59_tmc))
         [(word_sub stackpointer (word 32),32); (m,32)]
   ==> ensures x86
        (\s. bytes_loaded s (word pc) word_divstep59_tmc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             C_ARGUMENTS [m; d; f; g] s)
        (\s. read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             (ival d rem &2 = &1 /\
              ival f rem &2 = &1 /\
              abs(ival d) < &2 pow 62 ==>
              C_RETURN s = iword(divstep_d 59 (ival d,ival f,ival g)) /\
              let M = divstep_mat 59 (ival d,ival f,ival g) in
              read (memory :> bytes64(m)) s = iword(M$1$1) /\
              read (memory :> bytes64(word_add m (word 8))) s = iword(M$1$2) /\
              read (memory :> bytes64(word_add m (word 16))) s = iword(M$2$1) /\
              read (memory :> bytes64(word_add m (word 24))) s = iword(M$2$2)))
        (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes(m,32);
                   memory :> bytes(word_sub stackpointer (word 32),32)])`,
   X86_PROMOTE_RETURN_STACK_TAC word_divstep59_tmc WORD_DIVSTEP59_CORRECT
    `[RBX; RBP; R12; R13]` 32);;

let WORD_DIVSTEP59_SUBROUTINE_CORRECT = prove
 (`!m d f g pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 32),40) (m,32) /\
     ALL (nonoverlapping (word pc,LENGTH word_divstep59_mc))
         [(word_sub stackpointer (word 32),32); (m,32)]
   ==> ensures x86
        (\s. bytes_loaded s (word pc) word_divstep59_mc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             C_ARGUMENTS [m; d; f; g] s)
        (\s. read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             (ival d rem &2 = &1 /\
              ival f rem &2 = &1 /\
              abs(ival d) < &2 pow 62 ==>
              C_RETURN s = iword(divstep_d 59 (ival d,ival f,ival g)) /\
              let M = divstep_mat 59 (ival d,ival f,ival g) in
              read (memory :> bytes64(m)) s = iword(M$1$1) /\
              read (memory :> bytes64(word_add m (word 8))) s = iword(M$1$2) /\
              read (memory :> bytes64(word_add m (word 16))) s = iword(M$2$1) /\
              read (memory :> bytes64(word_add m (word 24))) s = iword(M$2$2)))
        (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes(m,32);
                   memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_DIVSTEP59_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let word_divstep59_windows_mc = define_from_elf "word_divstep59_windows_mc"
      "x86/generic/word_divstep59.obj";;

let word_divstep59_windows_tmc = define_trimmed "word_divstep59_windows_tmc" word_divstep59_windows_mc;;

let WORD_DIVSTEP59_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!m d f g pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 48),56) (m,32) /\
     ALL (nonoverlapping (word pc,LENGTH word_divstep59_windows_tmc))
         [(word_sub stackpointer (word 48),48); (m,32)]
   ==> ensures x86
        (\s. bytes_loaded s (word pc) word_divstep59_windows_tmc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             WINDOWS_C_ARGUMENTS [m; d; f; g] s)
        (\s. read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             (ival d rem &2 = &1 /\
              ival f rem &2 = &1 /\
              abs(ival d) < &2 pow 62 ==>
              C_RETURN s = iword(divstep_d 59 (ival d,ival f,ival g)) /\
              let M = divstep_mat 59 (ival d,ival f,ival g) in
              read (memory :> bytes64(m)) s = iword(M$1$1) /\
              read (memory :> bytes64(word_add m (word 8))) s = iword(M$1$2) /\
              read (memory :> bytes64(word_add m (word 16))) s = iword(M$2$1) /\
              read (memory :> bytes64(word_add m (word 24))) s = iword(M$2$2)))
        (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes(m,32);
                   memory :> bytes(word_sub stackpointer (word 48),48)])`,
   WINDOWS_X86_WRAP_STACK_TAC
    word_divstep59_windows_tmc word_divstep59_tmc
    WORD_DIVSTEP59_CORRECT
    `[RBX; RBP; R12; R13]` 32);;

let WORD_DIVSTEP59_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!m d f g pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 48),56) (m,32) /\
     ALL (nonoverlapping (word pc,LENGTH word_divstep59_windows_mc))
         [(word_sub stackpointer (word 48),48); (m,32)]
   ==> ensures x86
        (\s. bytes_loaded s (word pc) word_divstep59_windows_mc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             WINDOWS_C_ARGUMENTS [m; d; f; g] s)
        (\s. read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             (ival d rem &2 = &1 /\
              ival f rem &2 = &1 /\
              abs(ival d) < &2 pow 62 ==>
              C_RETURN s = iword(divstep_d 59 (ival d,ival f,ival g)) /\
              let M = divstep_mat 59 (ival d,ival f,ival g) in
              read (memory :> bytes64(m)) s = iword(M$1$1) /\
              read (memory :> bytes64(word_add m (word 8))) s = iword(M$1$2) /\
              read (memory :> bytes64(word_add m (word 16))) s = iword(M$2$1) /\
              read (memory :> bytes64(word_add m (word 24))) s = iword(M$2$2)))
        (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes(m,32);
                   memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_DIVSTEP59_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

