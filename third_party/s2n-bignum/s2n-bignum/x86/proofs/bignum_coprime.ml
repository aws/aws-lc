(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Coprimality test for two arbitrary bignums.                               *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_coprime.o";;
 ****)

let bignum_coprime_mc =
  define_assert_from_elf "bignum_coprime_mc" "x86/generic/bignum_coprime.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x83; 0xec; 0x30;  (* SUB (% rsp) (Imm8 (word 48)) *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0x39; 0xd0;        (* CMP (% rax) (% rdx) *)
  0x48; 0x0f; 0x42; 0xc2;  (* CMOVB (% rax) (% rdx) *)
  0x49; 0x89; 0xc6;        (* MOV (% r14) (% rax) *)
  0x48; 0x85; 0xc0;        (* TEST (% rax) (% rax) *)
  0x0f; 0x84; 0x0b; 0x03; 0x00; 0x00;
                           (* JE (Imm32 (word 779)) *)
  0x4f; 0x8d; 0x3c; 0xf0;  (* LEA (% r15) (%%% (r8,3,r14)) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x15;              (* JE (Imm8 (word 21)) *)
  0x4a; 0x8b; 0x04; 0xce;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,r9))) *)
  0x4b; 0x89; 0x04; 0xc8;  (* MOV (Memop Quadword (%%% (r8,3,r9))) (% rax) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xf9;        (* CMP (% r9) (% rdi) *)
  0x72; 0xf0;              (* JB (Imm8 (word 240)) *)
  0x4d; 0x39; 0xf1;        (* CMP (% r9) (% r14) *)
  0x73; 0x10;              (* JAE (Imm8 (word 16)) *)
  0x4b; 0xc7; 0x04; 0xc8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%%% (r8,3,r9))) (Imm32 (word 0)) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x4d; 0x39; 0xf1;        (* CMP (% r9) (% r14) *)
  0x72; 0xf0;              (* JB (Imm8 (word 240)) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x74; 0x15;              (* JE (Imm8 (word 21)) *)
  0x4a; 0x8b; 0x04; 0xc9;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r9))) *)
  0x4b; 0x89; 0x04; 0xcf;  (* MOV (Memop Quadword (%%% (r15,3,r9))) (% rax) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xd1;        (* CMP (% r9) (% rdx) *)
  0x72; 0xf0;              (* JB (Imm8 (word 240)) *)
  0x4d; 0x39; 0xf1;        (* CMP (% r9) (% r14) *)
  0x73; 0x10;              (* JAE (Imm8 (word 16)) *)
  0x4b; 0xc7; 0x04; 0xcf; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%%% (r15,3,r9))) (Imm32 (word 0)) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x4d; 0x39; 0xf1;        (* CMP (% r9) (% r14) *)
  0x72; 0xf0;              (* JB (Imm8 (word 240)) *)
  0x48; 0x8d; 0x04; 0x17;  (* LEA (% rax) (%%% (rdi,0,rdx)) *)
  0x48; 0xc1; 0xe0; 0x06;  (* SHL (% rax) (Imm8 (word 6)) *)
  0x48; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rax) *)
  0x49; 0x8b; 0x00;        (* MOV (% rax) (Memop Quadword (%% (r8,0))) *)
  0x49; 0x8b; 0x1f;        (* MOV (% rbx) (Memop Quadword (%% (r15,0))) *)
  0x48; 0x09; 0xd8;        (* OR (% rax) (% rbx) *)
  0x48; 0x89; 0x44; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rax) *)
  0x48; 0x83; 0xe3; 0x01;  (* AND (% rbx) (Imm8 (word 1)) *)
  0x48; 0x83; 0xeb; 0x01;  (* SUB (% rbx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4b; 0x8b; 0x04; 0xc8;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,r9))) *)
  0x4b; 0x8b; 0x0c; 0xcf;  (* MOV (% rcx) (Memop Quadword (%%% (r15,3,r9))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x31; 0xca;        (* XOR (% rdx) (% rcx) *)
  0x48; 0x21; 0xda;        (* AND (% rdx) (% rbx) *)
  0x48; 0x31; 0xd0;        (* XOR (% rax) (% rdx) *)
  0x48; 0x31; 0xd1;        (* XOR (% rcx) (% rdx) *)
  0x4b; 0x89; 0x04; 0xc8;  (* MOV (Memop Quadword (%%% (r8,3,r9))) (% rax) *)
  0x4b; 0x89; 0x0c; 0xcf;  (* MOV (Memop Quadword (%%% (r15,3,r9))) (% rcx) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x4d; 0x39; 0xf1;        (* CMP (% r9) (% r14) *)
  0x75; 0xd9;              (* JNE (Imm8 (word 217)) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x20;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x83; 0xc5; 0x3f;  (* ADD (% r13) (Imm8 (word 63)) *)
  0x49; 0xc1; 0xed; 0x06;  (* SHR (% r13) (Imm8 (word 6)) *)
  0x4d; 0x39; 0xf5;        (* CMP (% r13) (% r14) *)
  0x4d; 0x0f; 0x43; 0xee;  (* CMOVAE (% r13) (% r14) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x31; 0xff;        (* XOR (% rdi) (% rdi) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x48; 0x31; 0xf6;        (* XOR (% rsi) (% rsi) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4b; 0x8b; 0x1c; 0xc8;  (* MOV (% rbx) (Memop Quadword (%%% (r8,3,r9))) *)
  0x4b; 0x8b; 0x0c; 0xcf;  (* MOV (% rcx) (Memop Quadword (%%% (r15,3,r9))) *)
  0x4d; 0x89; 0xda;        (* MOV (% r10) (% r11) *)
  0x4d; 0x21; 0xe2;        (* AND (% r10) (% r12) *)
  0x49; 0x21; 0xeb;        (* AND (% r11) (% rbp) *)
  0x48; 0x89; 0xd8;        (* MOV (% rax) (% rbx) *)
  0x48; 0x09; 0xc8;        (* OR (% rax) (% rcx) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x49; 0x0f; 0x42; 0xfa;  (* CMOVB (% rdi) (% r10) *)
  0x49; 0x0f; 0x42; 0xf3;  (* CMOVB (% rsi) (% r11) *)
  0x4c; 0x0f; 0x42; 0xe3;  (* CMOVB (% r12) (% rbx) *)
  0x48; 0x0f; 0x42; 0xe9;  (* CMOVB (% rbp) (% rcx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x4d; 0x39; 0xe9;        (* CMP (% r9) (% r13) *)
  0x72; 0xcb;              (* JB (Imm8 (word 203)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0x09; 0xe8;        (* OR (% rax) (% rbp) *)
  0x48; 0x0f; 0xbd; 0xc8;  (* BSR (% rcx) (% rax) *)
  0x48; 0x83; 0xf1; 0x3f;  (* XOR (% rcx) (Imm8 (word 63)) *)
  0x49; 0x0f; 0xa5; 0xfc;  (* SHLD (% r12) (% rdi) (% cl) *)
  0x48; 0x0f; 0xa5; 0xf5;  (* SHLD (% rbp) (% rsi) (% cl) *)
  0x49; 0x8b; 0x00;        (* MOV (% rax) (Memop Quadword (%% (r8,0))) *)
  0x48; 0x89; 0xc7;        (* MOV (% rdi) (% rax) *)
  0x49; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (r15,0))) *)
  0x48; 0x89; 0xc6;        (* MOV (% rsi) (% rax) *)
  0x41; 0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 1)) *)
  0x41; 0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r11d) (Imm32 (word 0)) *)
  0xb9; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 0)) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x41; 0xb9; 0x3a; 0x00; 0x00; 0x00;
                           (* MOV (% r9d) (Imm32 (word 58)) *)
  0x4c; 0x89; 0x74; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r14) *)
  0x4c; 0x89; 0x6c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r13) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x7c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r15) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x0f; 0xba; 0xe7; 0x00;
                           (* BT (% rdi) (Imm8 (word 0)) *)
  0x48; 0x0f; 0x42; 0xc5;  (* CMOVB (% rax) (% rbp) *)
  0x48; 0x0f; 0x42; 0xde;  (* CMOVB (% rbx) (% rsi) *)
  0x4c; 0x0f; 0x42; 0xc1;  (* CMOVB (% r8) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xfa;  (* CMOVB (% r15) (% rdx) *)
  0x49; 0x89; 0xfd;        (* MOV (% r13) (% rdi) *)
  0x48; 0x29; 0xdf;        (* SUB (% rdi) (% rbx) *)
  0x4c; 0x29; 0xeb;        (* SUB (% rbx) (% r13) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x49; 0x29; 0xc6;        (* SUB (% r14) (% rax) *)
  0x49; 0x0f; 0x42; 0xec;  (* CMOVB (% rbp) (% r12) *)
  0x4d; 0x8d; 0x66; 0xff;  (* LEA (% r12) (%% (r14,18446744073709551615)) *)
  0x48; 0x0f; 0x42; 0xfb;  (* CMOVB (% rdi) (% rbx) *)
  0x49; 0x0f; 0x42; 0xf5;  (* CMOVB (% rsi) (% r13) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x49; 0x0f; 0x42; 0xca;  (* CMOVB (% rcx) (% r10) *)
  0x49; 0x0f; 0x42; 0xd3;  (* CMOVB (% rdx) (% r11) *)
  0x4d; 0x0f; 0x43; 0xe6;  (* CMOVAE (% r12) (% r14) *)
  0x48; 0xd1; 0xef;        (* SHR (% rdi) (Imm8 (word 1)) *)
  0x4d; 0x01; 0xc2;        (* ADD (% r10) (% r8) *)
  0x4d; 0x01; 0xfb;        (* ADD (% r11) (% r15) *)
  0x49; 0xd1; 0xec;        (* SHR (% r12) (Imm8 (word 1)) *)
  0x48; 0x01; 0xc9;        (* ADD (% rcx) (% rcx) *)
  0x48; 0x01; 0xd2;        (* ADD (% rdx) (% rdx) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x75; 0x9c;              (* JNE (Imm8 (word 156)) *)
  0x4c; 0x8b; 0x74; 0x24; 0x08;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x10;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x04; 0x24;  (* MOV (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x8b; 0x7c; 0x24; 0x18;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x89; 0x14; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r11) *)
  0x48; 0x89; 0x4c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rcx) *)
  0x48; 0x89; 0x54; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rdx) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x31; 0xff;        (* XOR (% rdi) (% rdi) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x48; 0x31; 0xf6;        (* XOR (% rsi) (% rsi) *)
  0x4b; 0x8b; 0x0c; 0xc8;  (* MOV (% rcx) (Memop Quadword (%%% (r8,3,r9))) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x4b; 0x8b; 0x0c; 0xcf;  (* MOV (% rcx) (Memop Quadword (%%% (r15,3,r9))) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x48; 0x29; 0xc7;        (* SUB (% rdi) (% rax) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x4b; 0x89; 0x3c; 0xc8;  (* MOV (Memop Quadword (%%% (r8,3,r9))) (% rdi) *)
  0x4c; 0x89; 0xd7;        (* MOV (% rdi) (% r10) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x4b; 0x89; 0x34; 0xcf;  (* MOV (Memop Quadword (%%% (r15,3,r9))) (% rsi) *)
  0x4c; 0x89; 0xde;        (* MOV (% rsi) (% r11) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x4d; 0x39; 0xe9;        (* CMP (% r9) (% r13) *)
  0x72; 0x97;              (* JB (Imm8 (word 151)) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4d; 0x89; 0xe2;        (* MOV (% r10) (% r12) *)
  0x49; 0x89; 0xeb;        (* MOV (% r11) (% rbp) *)
  0x4c; 0x31; 0xe7;        (* XOR (% rdi) (% r12) *)
  0x48; 0x31; 0xee;        (* XOR (% rsi) (% rbp) *)
  0x4b; 0x8b; 0x04; 0xc8;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,r9))) *)
  0x4c; 0x31; 0xe0;        (* XOR (% rax) (% r12) *)
  0x49; 0xf7; 0xda;        (* NEG (% r10) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x4b; 0x89; 0x04; 0xc8;  (* MOV (Memop Quadword (%%% (r8,3,r9))) (% rax) *)
  0x4b; 0x8b; 0x04; 0xcf;  (* MOV (% rax) (Memop Quadword (%%% (r15,3,r9))) *)
  0x48; 0x31; 0xe8;        (* XOR (% rax) (% rbp) *)
  0x49; 0xf7; 0xdb;        (* NEG (% r11) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x4b; 0x89; 0x04; 0xcf;  (* MOV (Memop Quadword (%%% (r15,3,r9))) (% rax) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x4d; 0x39; 0xe9;        (* CMP (% r9) (% r13) *)
  0x72; 0xce;              (* JB (Imm8 (word 206)) *)
  0x4c; 0x29; 0xd7;        (* SUB (% rdi) (% r10) *)
  0x4c; 0x29; 0xde;        (* SUB (% rsi) (% r11) *)
  0x4d; 0x89; 0xe9;        (* MOV (% r9) (% r13) *)
  0x4b; 0x8b; 0x44; 0xc8; 0xf8;
                           (* MOV (% rax) (Memop Quadword (%%%% (r8,3,r9,-- &8))) *)
  0x49; 0x89; 0xc4;        (* MOV (% r12) (% rax) *)
  0x48; 0x0f; 0xac; 0xf8; 0x3a;
                           (* SHRD (% rax) (% rdi) (Imm8 (word 58)) *)
  0x4b; 0x89; 0x44; 0xc8; 0xf8;
                           (* MOV (Memop Quadword (%%%% (r8,3,r9,-- &8))) (% rax) *)
  0x4c; 0x89; 0xe7;        (* MOV (% rdi) (% r12) *)
  0x4b; 0x8b; 0x44; 0xcf; 0xf8;
                           (* MOV (% rax) (Memop Quadword (%%%% (r15,3,r9,-- &8))) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x0f; 0xac; 0xf0; 0x3a;
                           (* SHRD (% rax) (% rsi) (Imm8 (word 58)) *)
  0x4b; 0x89; 0x44; 0xcf; 0xf8;
                           (* MOV (Memop Quadword (%%%% (r15,3,r9,-- &8))) (% rax) *)
  0x48; 0x89; 0xee;        (* MOV (% rsi) (% rbp) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x75; 0xd1;              (* JNE (Imm8 (word 209)) *)
  0x48; 0x83; 0x6c; 0x24; 0x20; 0x3a;
                           (* SUB (Memop Quadword (%% (rsp,32))) (Imm8 (word 58)) *)
  0x0f; 0x87; 0xcd; 0xfd; 0xff; 0xff;
                           (* JA (Imm32 (word 4294966733)) *)
  0x49; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (r15,0))) *)
  0x48; 0x83; 0xf0; 0x01;  (* XOR (% rax) (Imm8 (word 1)) *)
  0x49; 0x83; 0xfe; 0x01;  (* CMP (% r14) (Imm8 (word 1)) *)
  0x74; 0x12;              (* JE (Imm8 (word 18)) *)
  0x41; 0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r9d) (Imm32 (word 1)) *)
  0x4b; 0x0b; 0x04; 0xcf;  (* OR (% rax) (Memop Quadword (%%% (r15,3,r9))) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x4d; 0x39; 0xf1;        (* CMP (% r9) (% r14) *)
  0x72; 0xf4;              (* JB (Imm8 (word 244)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xff; 0xc0;        (* INC (% rax) *)
  0x48; 0x23; 0x44; 0x24; 0x28;
                           (* AND (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x83; 0xc4; 0x30;  (* ADD (% rsp) (Imm8 (word 48)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0xc3                     (* RET *)
];;

let bignum_coprime_tmc = define_trimmed "bignum_coprime_tmc" bignum_coprime_mc;;

let BIGNUM_COPRIME_EXEC = X86_MK_CORE_EXEC_RULE bignum_coprime_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let lemma58 = prove
 (`!n i. lowdigits (n DIV 2 EXP 58) (i + 1) =
         2 EXP (64 * i) *
         ((2 EXP 64 * bigdigit n (i + 1) + bigdigit n i) DIV 2 EXP 58) MOD
         2 EXP 64 +
         lowdigits (n DIV 2 EXP 58) i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [bigdigit] THEN REWRITE_TAC[DIV_DIV] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (GSYM DIV_DIV)] THEN
  ONCE_REWRITE_TAC[DIV_MOD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM highdigits; GSYM EXP_ADD] THEN
  REPLICATE_TAC 2 (ONCE_REWRITE_TAC[HIGHDIGITS_STEP]) THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `m divides e EXP 2 ==> (e * (e * x + y) + z == e * y + z) (mod m)`) THEN
  REWRITE_TAC[EXP_EXP] THEN MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ARITH_TAC);;

let BIGNUM_COPRIME_CORRECT = prove
 (`!m x a n y b w pc stackpointer.
        nonoverlapping (word pc,0x33e) (stackpointer,48) /\
        ALL (nonoverlapping (w,8 * 2 * MAX (val m) (val n)))
            [(word pc,0x33e); (stackpointer,48);
             (x,8 * val m); (y,8 * val n)] /\
        val m < 2 EXP 57 /\ val n < 2 EXP 57
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_coprime_tmc) /\
                  read RIP s = word(pc + 0xe) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [m;x;n;y;w] s /\
                  bignum_from_memory(x,val m) s = a /\
                  bignum_from_memory(y,val n) s = b)
             (\s. read RIP s = word(pc + 0x32f) /\
                  C_RETURN s = if coprime(a,b) then word 1 else word 0)
             (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RBP; RDI; RSI;
                         R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(w,2 * MAX (val m) (val n));
                         memory :> bytes(stackpointer,48)])`,
  W64_GEN_TAC `m:num` THEN MAP_EVERY X_GEN_TAC [`x:int64`; `a:num`] THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`y:int64`; `b:num`] THEN
  MAP_EVERY X_GEN_TAC [`mm:int64`; `pc:num`] THEN
  X_GEN_TAC `stackpointer:int64` THEN ABBREV_TAC `k = MAX m n` THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  BIGNUM_TERMRANGE_TAC `m:num` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `n:num` `b:num` THEN

  (*** Actual computation of k = max(m,n) ***)

  ENSURES_SEQUENCE_TAC `pc + 0x1b`
   `\s. read RSP s = stackpointer /\
        read RDI s = word m /\
        read RSI s = x /\
        read RDX s = word n /\
        read RCX s = y /\
        read R8 s = mm /\
        bignum_from_memory(x,m) s = a /\
        bignum_from_memory(y,n) s = b /\
        read RAX s = word k /\
        read R14 s = word k` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "k" THEN
    REWRITE_TAC[ARITH_RULE `MAX m n = if m < n then n else m`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The degenerate case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN FIRST_X_ASSUM
     (CONJUNCTS_THEN SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `MAX m n = 0 ==> m = 0 /\ n = 0`)) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[COPRIME_0; ARITH_EQ] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  VAL_INT64_TAC `k:num` THEN

  (*** The setup of the two separate buffers for m and n, for clarity ***)

  ABBREV_TAC `nn:int64 = word_add mm (word(8 * k))` THEN

  SUBGOAL_THEN
   `!z p. nonoverlapping_modulo (2 EXP 64) (val(mm:int64),8 * 2 * k) (z,p)
          ==> nonoverlapping_modulo (2 EXP 64) (val mm,8 * k) (z,p) /\
              nonoverlapping_modulo (2 EXP 64) (val(nn:int64),8 * k) (z,p)`
  MP_TAC THENL
   [EXPAND_TAC "nn" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT STRIP_TAC THEN NONOVERLAPPING_TAC;
    DISCH_THEN(fun th -> REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP th))) THEN
    REPEAT STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RBP; RDI; RSI;
               R9; R10; R11; R12; R13; R14; R15] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
    MAYCHANGE [memory :> bignum(mm,k); memory :> bignum(nn,k);
               memory :> bytes (stackpointer,48)]` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    EXPAND_TAC "nn" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64)
      (val(mm:int64),8 * k) (val(nn:int64),8 * k)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "nn" THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x28`
   `\s. read RSP s = stackpointer /\
        read RDI s = word m /\
        read RSI s = x /\
        read RDX s = word n /\
        read RCX s = y /\
        read R8 s = mm /\
        read R15 s = nn /\
        bignum_from_memory(x,m) s = a /\
        bignum_from_memory(y,n) s = b /\
        read R14 s = word k` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_THEN `word_add mm (word(8 * k)):int64 = nn` (K ALL_TAC)] THEN

  (*** Copying in of x = a argument into m ***)

  ENSURES_SEQUENCE_TAC `pc + 0x55`
   `\s. read RSP s = stackpointer /\
        read RDI s = word m /\
        read RDX s = word n /\
        read RCX s = y /\
        read R8 s = mm /\
        read R15 s = nn /\
        bignum_from_memory(mm,k) s = a /\
        bignum_from_memory(y,n) s = b /\
        read R14 s = word k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `m = 0` THENL
     [UNDISCH_THEN `m = 0` SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
        `MAX 0 n = k ==> n = k`)) THEN
      ENSURES_WHILE_UP_TAC `k:num` `pc + 0x45` `pc + 0x50`
       `\i s. read RSP s = stackpointer /\
              read RDI s = word 0 /\
              read RSI s = x /\
              read RDX s = word k /\
              read RCX s = y /\
              read R8 s = mm /\
              read R15 s = nn /\
              bignum_from_memory(mm,i) s = 0 /\
              bignum_from_memory(y,k) s = b /\
              read R14 s = word k /\
              read R9 s = word i` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--3) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
        X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2) THEN
        REWRITE_TAC[WORD_ADD; MULT_CLAUSES; ADD_CLAUSES];
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2);
        X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2)];
      ALL_TAC] THEN

    ENSURES_WHILE_UP_TAC `m:num` `pc + 0x30` `pc + 0x3b`
     `\i s. read RSP s = stackpointer /\
            read RDI s = word m /\
            read RSI s = x /\
            read RDX s = word n /\
            read RCX s = y /\
            read R8 s = mm /\
            read R15 s = nn /\
            bignum_from_memory(mm,i) s = lowdigits a i /\
            bignum_from_memory(word_add x (word (8 * i)),m - i) s =
            highdigits a i /\
            bignum_from_memory(y,n) s = b /\
            read R14 s = word k /\
            read R9 s = word i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--3) THEN
      REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; HIGHDIGITS_0; LOWDIGITS_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--3) THEN
      REWRITE_TAC[WORD_ADD; LOWDIGITS_CLAUSES] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2);
      ALL_TAC] THEN

    ASM_CASES_TAC `k:num = m` THENL
     [UNDISCH_THEN `k:num = m` SUBST_ALL_TAC THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--4) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF];
      ALL_TAC] THEN

    SUBGOAL_THEN `m:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN

    ENSURES_WHILE_AUP_TAC `m:num` `k:num` `pc + 0x45` `pc + 0x50`
     `\i s. read RSP s = stackpointer /\
            read RDI s = word m /\
            read RSI s = x /\
            read RDX s = word n /\
            read RCX s = y /\
            read R8 s = mm /\
            read R15 s = nn /\
            bignum_from_memory(mm,i) s = a /\
            bignum_from_memory(y,n) s = b /\
            read R14 s = word k /\
            read R9 s = word i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--4) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF; GSYM NOT_LT];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2) THEN
      REWRITE_TAC[WORD_ADD; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_0];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2);
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2)];
    ALL_TAC] THEN

  (*** Copying in of y = b argument into n ***)

  ENSURES_SEQUENCE_TAC `pc + 0x82`
   `\s. read RSP s = stackpointer /\
        read RDI s = word m /\
        read RDX s = word n /\
        read R8 s = mm /\
        read R15 s = nn /\
        bignum_from_memory(mm,k) s = a /\
        bignum_from_memory(nn,k) s = b /\
        read R14 s = word k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
        `MAX m 0 = k ==> m = k`)) THEN
      ENSURES_WHILE_UP_TAC `k:num` `pc + 0x72` `pc + 0x7d`
       `\i s. read RSP s = stackpointer /\
              read RDI s = word k /\
              read RDX s = word 0 /\
              read RCX s = y /\
              read R8 s = mm /\
              read R15 s = nn /\
              bignum_from_memory(mm,k) s = a /\
              bignum_from_memory(nn,i) s = 0 /\
              read R14 s = word k /\
              read R9 s = word i` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--3) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
        X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2) THEN
        REWRITE_TAC[WORD_ADD; MULT_CLAUSES; ADD_CLAUSES];
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2);
        X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2)];
      ALL_TAC] THEN

    ENSURES_WHILE_UP_TAC `n:num` `pc + 0x5d` `pc + 0x68`
     `\i s. read RSP s = stackpointer /\
            read RDI s = word m /\
            read RDX s = word n /\
            read RCX s = y /\
            read R8 s = mm /\
            read R15 s = nn /\
            bignum_from_memory(mm,k) s = a /\
            bignum_from_memory(nn,i) s = lowdigits b i /\
            bignum_from_memory(word_add y (word (8 * i)),n - i) s =
            highdigits b i /\
            read R14 s = word k /\
            read R9 s = word i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--3) THEN
      REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; HIGHDIGITS_0; LOWDIGITS_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--3) THEN
      REWRITE_TAC[WORD_ADD; LOWDIGITS_CLAUSES] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2);
      ALL_TAC] THEN

    ASM_CASES_TAC `k:num = n` THENL
     [UNDISCH_THEN `k:num = n` SUBST_ALL_TAC THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--4) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF];
      ALL_TAC] THEN

    SUBGOAL_THEN `n:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN

    ENSURES_WHILE_AUP_TAC `n:num` `k:num` `pc + 0x72` `pc + 0x7d`
     `\i s. read RSP s = stackpointer /\
            read RDI s = word m /\
            read RDX s = word n /\
            read RCX s = y /\
            read R8 s = mm /\
            read R15 s = nn /\
            bignum_from_memory(mm,k) s = a /\
            bignum_from_memory(nn,i) s = b /\
            read R14 s = word k /\
            read R9 s = word i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--4) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF; GSYM NOT_LT];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2) THEN
      REWRITE_TAC[WORD_ADD; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_0];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2);
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2)];
    ALL_TAC] THEN

  (*** Set up more parameters for the main part of the code, in particular ***)
  (*** the total number of bits which uses m and n for the last time.      ***)

  ENSURES_SEQUENCE_TAC `pc + 0xa5`
   `\s. read RSP s = stackpointer /\
        read (memory :> bytes64(word_add stackpointer (word 40))) s =
        word_or (word(bigdigit a 0)) (word(bigdigit b 0)) /\
        read R8 s = mm /\
        read R15 s = nn /\
        read R14 s = word k /\
        read (memory :> bytes64(word_add stackpointer (word 32))) s =
        word(64 * (m + n)) /\
        read RBX s = word_neg(word(bitval(EVEN b))) /\
        bignum_from_memory(mm,k) s = a /\
        bignum_from_memory(nn,k) s = b` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(mm,k) s0 = highdigits a 0 /\
      bignum_from_memory(nn,k) s0 = highdigits b 0`
    MP_TAC THENL
     [ASM_SIMP_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REWRITE_TAC[WORD_AND_1; BIT_WORD; DIMINDEX_64; ARITH; DIV_1] THEN
    REWRITE_TAC[GSYM NOT_ODD; ODD_MOD_POW2; bigdigit] THEN
    REWRITE_TAC[MULT_CLAUSES; DIV_1; ARITH_EQ; EXP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Now just introduce a variable for the overall size and then    ***)
  (*** forget all about x, y, m and n which play no more role. Indeed ***)
  (*** we re-use the variable names m and n later on.                 ***)

  SUBGOAL_THEN `a * b < 2 EXP (64 * (m + n))` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_ADD; LEFT_ADD_DISTRIB] THEN MATCH_MP_TAC LT_MULT2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t = 64 * (m + n)` THEN
  SUBGOAL_THEN `64 <= t /\ t <= 128 * k` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k < 2 EXP 57` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `x:int64` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `y:int64` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN STRIP_TAC THEN

  (*** The optional swapping done initially if n is even ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0xa8` `pc + 0xca`
     `\i s. read RSP s = stackpointer /\
            read (memory :> bytes64(word_add stackpointer (word 40))) s =
            word_or (word(bigdigit a 0)) (word(bigdigit b 0)) /\
            read R8 s = mm /\
            read R15 s = nn /\
            read R14 s = word k /\
            read (memory :> bytes64(word_add stackpointer (word 32))) s =
            word t /\
            read RBX s = word_neg(word(bitval(EVEN b))) /\
            bignum_from_memory(mm,i) s =
            lowdigits (if EVEN b then b else a) i /\
            bignum_from_memory(word_add mm (word (8 * i)),k - i) s =
            highdigits a i /\
            bignum_from_memory(nn,i) s =
            lowdigits (if EVEN b then a else b) i /\
            bignum_from_memory(word_add nn (word (8 * i)),k - i) s =
            highdigits b i /\
            read R9 s = word i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_COPRIME_EXEC [1] THEN
    REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; HIGHDIGITS_0; LOWDIGITS_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--10) THEN
    REWRITE_TAC[WORD_ADD; LOWDIGITS_CLAUSES; WORD_AND_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_XOR_0] THEN
    REWRITE_TAC[WORD_BITWISE_RULE `word_xor a (word_xor a b) = b`] THEN
    REWRITE_TAC[WORD_BITWISE_RULE `word_xor b (word_xor a b) = a`] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN ARITH_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
    ALL_TAC] THEN

  (*** The setup of the main outer loop, with the final comparison to 1 ***)

  ENSURES_WHILE_PUP_TAC `(t + 57) DIV 58` `pc + 0xcf` `pc + 0x2fc`
    `\i s. (read RSP s = stackpointer /\
            read (memory :> bytes64(word_add stackpointer (word 40))) s =
            word_or (word(bigdigit a 0)) (word(bigdigit b 0)) /\
            read R8 s = mm /\
            read R15 s = nn /\
            read R14 s = word k /\
            read (memory :> bytes64(word_add stackpointer (word 32))) s =
            word_sub (word t) (word(58 * i)) /\
            (ODD a \/ ODD b
             ==> ODD(bignum_from_memory(nn,k) s) /\
                 bignum_from_memory(mm,k) s * bignum_from_memory(nn,k) s
                 < 2 EXP (t - 58 * i) /\
                 gcd(bignum_from_memory(mm,k) s,bignum_from_memory(nn,k) s) =
                 gcd(a,b))) /\
           (read CF s <=> t < 58 * i) /\
           (read ZF s <=> 58 * i = t)` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `64 <= t` THEN ARITH_TAC;

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_SUB_0; GSYM NOT_ODD] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN CONV_TAC NUMBER_RULE;

    ALL_TAC; (*** This is the big one, the main loop invariant ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_COPRIME_EXEC [1] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `i < (t + 57) DIV 58 ==> ~(t < 58 * i) /\ ~(58 * i = t)`];

    (**** This is the end loop doing a comparison  ***)

    REWRITE_TAC[ARITH_RULE `t - 58 * (t + 57) DIV 58 = 0`] THEN
    GHOST_INTRO_TAC `m:num` `bignum_from_memory(mm,k)` THEN
    GHOST_INTRO_TAC `n:num` `bignum_from_memory(nn,k)` THEN
    MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`m:num`; `n:num`] THEN
    REWRITE_TAC[EXP] THEN
    GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN

    ENSURES_SEQUENCE_TAC `pc + 0x321`
     `\s. read RSP s = stackpointer /\
          read (memory :> bytes64(word_add stackpointer (word 40))) s =
          word_or (word (bigdigit a 0)) (word (bigdigit b 0)) /\
          (read RAX s = word 0 <=> n = 1)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      GHOST_INTRO_TAC `zorro:int64` `read RAX` THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[WORD_MASK_ALT; WORD_SUB_0; VAL_EQ_0; COND_SWAP] THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC[WORD_RULE `word_add (word_neg x) x = word 0`;
                      WORD_AND_1; WORD_AND_0; WORD_ADD_0]
      THENL
       [REWRITE_TAC[BIT_WORD_OR; BIT_WORD; DIMINDEX_64; ARITH; DIV_1] THEN
        REWRITE_TAC[ODD_MOD_POW2; bigdigit] THEN
        REWRITE_TAC[MULT_CLAUSES; DIV_1; ARITH_EQ; EXP] THEN
        FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[GCD_1] THEN
        SIMP_TAC[NUMBER_RULE `1 = gcd(a,b) <=> coprime(a,b)`] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_ODD] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `2` o GEN_REWRITE_RULE I [COPRIME]) THEN
        SIMP_TAC[DIVIDES_2; ARITH_EQ];
        REWRITE_TAC[COPRIME_GCD] THEN
        FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(TAUT `~(~p /\ ~s) /\ ~q ==> (p \/ s ==> q) ==> r`) THEN
        CONJ_TAC THENL
         [REWRITE_TAC[NOT_ODD] THEN STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `2` o MATCH_MP (NUMBER_RULE
           `gcd(a,b) = 1 ==> !d. d divides a /\ d divides b ==> d = 1`)) THEN
          ASM_REWRITE_TAC[DIVIDES_2; ARITH_EQ];
          REWRITE_TAC[ARITH_RULE `m < 1 <=> m = 0`; MULT_EQ_0] THEN
          ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ODD] THEN
          ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[GCD_0]]]] THEN

    ENSURES_SEQUENCE_TAC `pc + 0x309`
     `\s. read RSP s = stackpointer /\
          read (memory :> bytes64(word_add stackpointer (word 40))) s =
          word_or (word (bigdigit a 0)) (word (bigdigit b 0)) /\
          read R15 s = nn /\
          read R14 s = word k /\
          bignum_from_memory(word_add nn (word (8 * 1)),k - 1) s =
          highdigits n 1 /\
          (read RAX s = word 0 <=> bigdigit n 0 = 1)` THEN
    CONJ_TAC THENL
     [MP_TAC(ARITH_RULE
       `t < 58 * (t + 57) DIV 58 \/ 58 * (t + 57) DIV 58 = t`) THEN
      DISCH_TAC THEN ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `bignum_from_memory(nn,k) s0 = highdigits n 0`
      MP_TAC THENL
       [ASM_SIMP_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0];
        GEN_REWRITE_TAC LAND_CONV
         [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
        ASM_REWRITE_TAC[ADD_CLAUSES; BIGNUM_FROM_MEMORY_BYTES] THEN
        STRIP_TAC] THEN
      X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[WORD_XOR_EQ_0; MULT_CLAUSES] THEN
      MATCH_MP_TAC WORD_EQ_IMP THEN
      REWRITE_TAC[DIMINDEX_64; BIGDIGIT_BOUND] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN

    ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      GHOST_INTRO_TAC `zorro:int64` `read RAX` THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[bigdigit; EXP; DIV_1; MULT_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_SIMP_TAC[MOD_LT];
      ALL_TAC] THEN

    ENSURES_WHILE_AUP_TAC `1` `k:num` `pc + 0x315` `pc + 0x31c`
     `\i s. read RSP s = stackpointer /\
            read (memory :> bytes64(word_add stackpointer (word 40))) s =
            word_or (word (bigdigit a 0)) (word (bigdigit b 0)) /\
            read R15 s = nn /\
            read R14 s = word k /\
            bignum_from_memory (word_add nn (word (8 * i)),k - i) s =
            highdigits n i /\
            (read RAX s = word 0 <=> lowdigits n i = 1) /\
            read R9 s = word i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;

      SUBGOAL_THEN `val(word_sub (word k) (word 1):int64) = 0 <=> k = 1`
      ASSUME_TAC THENL
       [REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
        MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
        SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      GHOST_INTRO_TAC `zorro:int64` `read RAX` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[LOWDIGITS_1];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `zorro:int64` `read RAX` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2) THEN
      ASM_REWRITE_TAC[WORD_ADD; WORD_OR_EQ_0; LOWDIGITS_CLAUSES] THEN
      SIMP_TAC[WORD_EQ_0; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      ASM_CASES_TAC `bigdigit n i = 0` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      MATCH_MP_TAC(ARITH_RULE `2 EXP 1 * 1 <= e * d ==> ~(e * d + l = 1)`) THEN
      MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_EXP] THEN
      ASM_SIMP_TAC[LE_1] THEN SIMPLE_ARITH_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2);

      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF]]] THEN

  (*** Tidying up the main outer loop invariant. We use the slightly more  ***)
  (*** verbose names "m0" and "n0" since most interesting computations are ***)
  (*** actually on the l-digit versions which are usually the same.        ***)

  X_GEN_TAC `icount:num` THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP
   (ARITH_RULE `i < (t + 57) DIV 58 ==> 0 < t - 58 * i`) o CONJUNCT1) THEN
  REWRITE_TAC[ARITH_RULE `t - 58 * (i + 1) = t - 58 * i - 58`] THEN
  REWRITE_TAC[WORD_RULE
   `word_sub t (word(58 * (i + 1))):int64 =
    word_sub (word_sub t (word(58 * i))) (word 58)`] THEN
  SUBGOAL_THEN
   `word_sub (word t) (word (58 * icount)):int64 = word(t - 58 * icount)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `0 < m - n ==> n <= m`];
    UNDISCH_TAC `0 < t - 58 * icount`] THEN

  SIMP_TAC[ARITH_RULE
   `0 < t - 58 * i ==> (t < 58 * (i + 1) <=> t - 58 * i < 58)`] THEN
  SIMP_TAC[ARITH_RULE
   `0 < t - 58 * i ==> (58 * (i + 1) = t <=> t - 58 * i = 58)`] THEN
  SUBGOAL_THEN `t - 58 * icount <= 128 * k` MP_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`t - 58 * icount`,`t':num`) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `t:num` o concl))) THEN
  X_GEN_TAC `t:num` THEN REPEAT DISCH_TAC THEN
  GHOST_INTRO_TAC `m0:num` `bignum_from_memory(mm,k)` THEN
  GHOST_INTRO_TAC `n0:num` `bignum_from_memory(nn,k)` THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`m0:num`; `n0:num`] THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN

  SPEC_TAC(`word_or (word (bigdigit a 0)) (word (bigdigit b 0)):int64`,
           `evenor:int64`) THEN
  X_GEN_TAC `evenor:int64` THEN

  (*** Computation of the sharper bound and its property ***)

  ABBREV_TAC `l = MIN k ((t + 63) DIV 64)` THEN
  ABBREV_TAC `m = lowdigits m0 l` THEN
  ABBREV_TAC `n = lowdigits n0 l` THEN

  ENSURES_SEQUENCE_TAC `pc + 0xe3`
   `\s. read RSP s = stackpointer /\
        read (memory :> bytes64(word_add stackpointer (word 40))) s = evenor /\
        read R8 s = mm /\
        read R15 s = nn /\
        read R14 s = word k /\
        read (memory :> bytes64(word_add stackpointer (word 32))) s = word t /\
        read R13 s = word l /\
        bignum_from_memory (mm,l) s = m /\
        bignum_from_memory (nn,l) s = n /\
        bignum_from_memory (mm,k) s = m0 /\
        bignum_from_memory (nn,k) s = n0` THEN
  CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[MESON[]
     `m = lowdigits m0 l /\ n = lowdigits n0 l /\ x = m0 /\ y = n0 <=>
      m = lowdigits x l /\ n = lowdigits y l /\ x = m0 /\ y = n0`] THEN
    REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN EXPAND_TAC "l" THEN
    REWRITE_TAC[ARITH_RULE `MIN k (MIN k l) = MIN k l`] THEN
    ASM_REWRITE_TAC[] THEN X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--5) THEN
    VAL_INT64_TAC `t + 63` THEN REWRITE_TAC[GSYM VAL_EQ; GSYM WORD_ADD] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR] THEN EXPAND_TAC "l" THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MIN] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `~(l = 0)` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  SUBGOAL_THEN
   `(~(n0 = 0) /\ (ODD a \/ ODD b) ==> m0 < 2 EXP (64 * l)) /\
    (~(m0 = 0) /\ (ODD a \/ ODD b) ==> n0 < 2 EXP (64 * l))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[TAUT
     `(p /\ q ==> r) /\ (p' /\ q ==> r') <=>
      q ==> (p ==> r) /\ (p' ==> r')`] THEN
     DISCH_THEN(fun th ->
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
    EXPAND_TAC "l" THEN REWRITE_TAC[MIN] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN TRANS_TAC LET_TRANS `m0 * n0:num` THEN
    REWRITE_TAC[ARITH_RULE `m0 <= m0 * n0 <=> m0 * 1 <= m0 * n0`] THEN
    REWRITE_TAC[ARITH_RULE `n0 <= m0 * n0 <=> n0 * 1 <= n0 * m0`] THEN
    ASM_SIMP_TAC[LE_MULT_LCANCEL; LE_1] THEN
    TRANS_TAC LTE_TRANS `2 EXP t` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LE_EXP] THEN ARITH_TAC;
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `MIN k ttt = l ==> l <= k`)) THEN
    VAL_INT64_TAC `l:num`] THEN

  (*** The initial toploop picking out high 2 words for the inputs ***)

  ENSURES_WHILE_UP_TAC `l:num` `pc + 0xf5` `pc + 0x125`
   `\i s. read RSP s = stackpointer /\
          read (memory :> bytes64(word_add stackpointer (word 40))) s =
          evenor /\
          read R8 s = mm /\
          read R15 s = nn /\
          read R14 s = word k /\
          read (memory :> bytes64(word_add stackpointer (word 32))) s =
          word t /\
          read R13 s = word l /\
          bignum_from_memory (mm,l) s = m /\
          bignum_from_memory (nn,l) s = n /\
          bignum_from_memory (mm,k) s = m0 /\
          bignum_from_memory (nn,k) s = n0 /\
          bignum_from_memory (word_add mm (word (8 * i)),k - i) s =
          highdigits m0 i /\
          bignum_from_memory (word_add nn (word (8 * i)),k - i) s =
          highdigits n0 i /\
          read R9 s = word i /\
          read R11 s = word_neg(word(bitval
           (~(i = 0) /\ ~(bigdigit m0 (i-1) = 0 /\ bigdigit n0 (i-1) = 0)))) /\
          (read R12 s = word 0 /\ read RBP s = word 0 <=>
           lowdigits m0 i = 0 /\ lowdigits n0 i = 0) /\
          ?j. j <= i /\
              (2 EXP 128 * lowdigits m0 i) DIV 2 EXP (64 * j) =
              2 EXP 64 * val(read R12 s) + val(read RDI s) /\
              (2 EXP 128 * lowdigits n0 i) DIV 2 EXP (64 * j) =
              2 EXP 64 * val(read RBP s) + val(read RSI s)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; HIGHDIGITS_0] THEN
    X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--6) THEN
    REWRITE_TAC[CONJUNCT1 LE; UNWIND_THM2; LOWDIGITS_0; VAL_WORD_0] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; DIV_0; BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[NOT_LT; ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[GSYM VAL_EQ_0] THEN
    GHOST_INTRO_TAC `h1:num` `\s. val(read R12 s)` THEN
    GHOST_INTRO_TAC `h2:num` `\s. val(read RBP s)` THEN
    GHOST_INTRO_TAC `l1:num` `\s. val(read RDI s)` THEN
    GHOST_INTRO_TAC `l2:num` `\s. val(read RSI s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_SUB; WORD_SUB_0; VAL_EQ_0; ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[WORD_OR_EQ_0; WORD_ADD] THEN
    SIMP_TAC[WORD_EQ_0; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE `0 < n0 <=> ~(n0 = 0)`] THEN
    REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    ASM_CASES_TAC `bigdigit m0 i = 0 /\ bigdigit n0 i = 0` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    ASM_SIMP_TAC[WORD_EQ_0; DIMINDEX_64; BIGDIGIT_BOUND] THENL
     [EXISTS_TAC `j:num` THEN
      ASM_SIMP_TAC[ARITH_RULE `j <= i ==> j <= i + 1`] THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [TAUT `(p /\ p') /\ (q /\ q') <=> (p /\ q) /\ (p' /\ q')`] THEN
    SIMP_TAC[WORD_EQ_0; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `i + 1` THEN REWRITE_TAC[LE_REFL] THEN
    REWRITE_TAC[ARITH_RULE `128 = 64 + 64`] THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 + 64 * i`] THEN
    SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT2; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `2 EXP 64 * (e * a + b) = e * (2 EXP 64 * a) + 2 EXP 64 * b`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[WORD_AND_MASK] THEN ASM_CASES_TAC `i = 0` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; VAL_WORD_0; DIV_0; LOWDIGITS_0] THEN
    REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [SIMP_TAC[VAL_WORD_0; DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
      SUBGOAL_THEN `i = (i - 1) + 1` SUBST1_TAC THENL
       [UNDISCH_TAC `~(i = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[LOWDIGITS_CLAUSES; EXP_ADD; LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[LOWDIGITS_BOUND; ARITH_RULE
       `a * b * 0 + 2 EXP 64 * x < y * 2 EXP (64 * 1) <=> x < y`];
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]] THEN
    UNDISCH_TAC `j:num <= i` THEN REWRITE_TAC[LE_LT] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `a = 2 EXP 64 * h + l
        ==> h < 2 EXP 64 /\ l < 2 EXP 64 ==> a < 2 EXP 128`))) THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
      MATCH_MP_TAC(ARITH_RULE
       `e <= a \/ e <= b
        ==> 2 EXP 128 * a < e * 2 EXP 128
            ==> 2 EXP 128 * b < e * 2 EXP 128
                ==> p`) THEN
      SUBGOAL_THEN `i = (i - 1) + 1` SUBST1_TAC THENL
       [UNDISCH_TAC `~(i = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      UNDISCH_TAC `~(bigdigit m0 (i - 1) = 0 /\ bigdigit n0 (i - 1) = 0)` THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN MATCH_MP_TAC MONO_OR THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(ARITH_RULE
       `a * 1 <= b * d ==> a <= b * d + c`) THEN
      MATCH_MP_TAC LE_MULT2 THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_RULE `1 <= n0 <=> ~(n0 = 0)`] THEN
      UNDISCH_TAC `j:num < i` THEN ARITH_TAC;
      ONCE_REWRITE_TAC[ARITH_RULE
       `2 EXP 64 * a = (2 EXP 128 * a) DIV 2 EXP 64`] THEN
      REWRITE_TAC[DIV_DIV] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (GSYM DIV_DIV)] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; EXP_EQ_0] THEN
      ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES]];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2) THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];

    ALL_TAC] THEN

  (*** Pick the base position for the upper proxies, which can be negative ***)

  ABBREV_TAC `base:int = &(MAX (bitsize m) (bitsize n)) - &64` THEN

  (*** Set up a bidirectional local bound for more refined error estimates ***)

  SUBGOAL_THEN
   `?lowerr upperr.
        lowerr 0 = &1 /\ upperr 0 = &0 /\
        (!i. lowerr(SUC i) = (lowerr(i) + upperr(i) + &1) / &2) /\
        (!i. upperr(SUC i) = (lowerr(i) + upperr(i)) / &2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXISTS_UNPAIR_FUN_THM] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> (p /\ q) /\ (r /\ s)`] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN ONCE_REWRITE_TAC[GSYM PAIR_EQ] THEN
    REWRITE_TAC[o_THM] THEN
    W(ACCEPT_TAC o prove_recursive_functions_exist num_RECURSION o
      snd o dest_exists o snd);
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!i. i <= 58
        ==> &0 <= lowerr i /\ (lowerr:num->real) i < &16 /\
            &0 <= upperr i /\ (upperr:num->real) i < &16 /\
            --((lowerr i + upperr i + &1) / &2) <= --lowerr i /\
            upperr i <= (lowerr i + upperr i) / &2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun n ->
      MP_TAC(REFL(mk_comb(`lowerr:num->real`,mk_small_numeral n))) THEN
      CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV num_CONV))) THEN
      MP_TAC(REFL(mk_comb(`upperr:num->real`,mk_small_numeral n))) THEN
      CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV num_CONV))) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      DISCH_TAC THEN DISCH_TAC)
      (1--58) THEN
    REWRITE_TAC[ARITH_RULE `i <= 58 <=> i < 59`] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Allow the inner loop to save and restore R8 ***)

  ENSURES_EXISTING_PRESERVED_TAC `R8` THEN

  (*** Now set up the somewhat intricate inner loop invariant ***)

  ENSURES_WHILE_PUP_TAC `58` `pc + 0x17b` `pc + 0x1dd`
   `\i s. (read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s =
           mm /\
           read (memory :> bytes64(word_add stackpointer (word 8))) s =
           word k /\
           read (memory :> bytes64(word_add stackpointer (word 16))) s =
           word l /\
           read (memory :> bytes64(word_add stackpointer (word 24))) s =
           nn /\
           read (memory :> bytes64(word_add stackpointer (word 40))) s =
           evenor /\
           read (memory :> bytes64(word_add stackpointer (word 32))) s =
           word t /\
           bignum_from_memory (mm,l) s = m /\
           bignum_from_memory (nn,l) s = n /\
           bignum_from_memory (mm,k) s = m0 /\
           bignum_from_memory (nn,k) s = n0 /\
           read R9 s = word(58 - i) /\
           val(read R10 s) + val(read R11 s) <= 2 EXP i /\
           val(read RCX s) + val(read RDX s) <= 2 EXP i /\
           (ODD a \/ ODD b
           ==> ODD(val(read RSI s)) /\
               gcd(&(val(read R10 s)) * &m - &(val(read R11 s)) * &n:int,
                   &(val(read RCX s)) * &m - &(val(read RDX s)) * &n) =
               &2 pow i * gcd(&m,&n) /\
               ?q. (--(&1) pow q *
                    (&(val(read R10 s)) * &m - &(val(read R11 s)) * &n):int ==
                    &2 pow i * &(val(read RDI s))) (mod (&2 pow 64)) /\
                   (--(--(&1) pow q) *
                    (&(val(read RCX s)) * &m - &(val(read RDX s)) * &n):int ==
                    &2 pow i * &(val(read RSI s))) (mod (&2 pow 64)) /\
                   let m' = --(&1) pow q *
                            (&(val(read R10 s)) * &m - &(val(read R11 s)) * &n)
                   and n' = --(--(&1) pow q) *
                            (&(val(read RCX s)) * &m - &(val(read RDX s)) * &n)
                   and m_hi = val(read R12 s)
                   and n_hi = val(read RBP s)
                   and m_lo = val(read RDI s)
                   and n_lo = val(read RSI s) in
                   --(lowerr i) <= &m_hi - m' / &2 zpow (base + &i) /\
                   &m_hi - m' / &2 zpow (base + &i) <= upperr i /\
                   --(lowerr i) <= &n_hi - n' / &2 zpow (base + &i) /\
                   &n_hi - n' / &2 zpow (base + &i) <= upperr i /\
                   (min (&m) (&n) < &2 zpow base * &2 pow 5
                    ==> abs(m') * abs(n') <= &2 pow i * &m * &n /\
                        (i <= 57
                         ==> &0 <= m' /\ &0 <= n' /\
                             (m_hi < n_hi /\
                              m_hi < 2 EXP 5 /\
                              2 EXP 63 <= 2 EXP i * (n_hi + 31) /\
                              &m_hi <= m' / &2 zpow (base + &i) /\
                              m' / &2 zpow (base + &i) <= &m_hi + &1 \/
                              n_hi < m_hi /\
                              n_hi < 2 EXP 5 /\
                              2 EXP 63 <= 2 EXP i * (m_hi + 31) /\
                              n' / &2 zpow (base + &i) <= &n_hi + &1))) /\
                   (&0 <= m' /\ &0 <= n' /\
                    min m' n' <= &2 pow i * min (&m) (&n) /\
                    m' * n' <= &2 pow i * &m * &n \/
                    m' < &0 /\ &0 <= n' /\ m_hi < 16 /\
                    &n_hi < min (&m) (&n) / &2 zpow base + &16 \/
                    n' < &0 /\ &0 <= m' /\ n_hi < 16 /\
                    &m_hi < min (&m) (&n) / &2 zpow base + &16))) /\
          (read ZF s <=> i = 58)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** the initial holding of the invariant ***)

    GHOST_INTRO_TAC `h1:int64` `read R12` THEN
    GHOST_INTRO_TAC `h2:int64` `read RBP` THEN
    GHOST_INTRO_TAC `l1:int64` `read RDI` THEN
    GHOST_INTRO_TAC `l2:int64` `read RSI` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(mm,k) s0 = highdigits m0 0 /\
      bignum_from_memory(nn,k) s0 = highdigits n0 0`
    MP_TAC THENL
     [ASM_SIMP_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUB_0; VAL_WORD_0; VAL_WORD_1] THEN
    REWRITE_TAC[WORD_SUB_LZERO; WORD_NEG_EQ_0; VAL_EQ_0] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
    SUBGOAL_THEN
     `word (bigdigit m0 0):int64 = word(m MOD 2 EXP 64) /\
      word (bigdigit n0 0):int64 = word(n MOD 2 EXP 64)`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [REWRITE_TAC[bigdigit; EXP; DIV_1; MULT_CLAUSES] THEN
        UNDISCH_THEN `lowdigits m0 l = m` (SUBST1_TAC o SYM) THEN
        UNDISCH_THEN `lowdigits n0 l = n` (SUBST1_TAC o SYM) THEN
        REWRITE_TAC[lowdigits; MOD_MOD_EXP_MIN] THEN
        ASM_SIMP_TAC[ARITH_RULE `~(l = 0) ==> MIN (64 * l) 64 = 64`];
      ALL_TAC] THEN
   DISCH_THEN(fun th ->
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th) THEN
      ASSUME_TAC th) THEN
   SUBGOAL_THEN `ODD n` ASSUME_TAC THENL
    [SUBST1_TAC(SYM(ASSUME `lowdigits n0 l = n`)) THEN
     REWRITE_TAC[lowdigits; ODD_MOD_POW2; DIMINDEX_64] THEN
     ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ];
     ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VAL_WORD; MOD_MOD_REFL; ODD_MOD_POW2; DIMINDEX_64] THEN
      ASM_REWRITE_TAC[ARITH_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[INT_MUL_LID; INT_MUL_LZERO; INT_POW] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_GCD_EQ THEN CONV_TAC INTEGER_RULE; ALL_TAC] THEN
    EXISTS_TAC `0` THEN
    REWRITE_TAC[INT_POW; INT_MUL_LID; INT_MUL_LZERO] THEN
    REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_MUL_LZERO] THEN
    REWRITE_TAC[INT_SUB_LZERO; INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG;
                INT_MUL_LID; INT_SUB_RZERO; INT_ADD_RID] THEN
    REWRITE_TAC[REAL_SUB_LZERO; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG;
                REAL_MUL_LID; REAL_SUB_RZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_POS; REAL_ABS_NUM; REAL_LE_REFL] THEN
    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC MOD_DOWN_CONV THEN CONJ_TAC THEN REFL_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `c = word_clz (word_or h1 h2:int64)` THEN
    MP_TAC(ISPEC `word_or h1 h2:int64` WORD_CLZ_LE_DIMINDEX) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word c:int64) = c` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `c <= 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (MESON[ODD] `ODD m ==> ~(m = 0)`)) THEN
    ASM_REWRITE_TAC[WORD_OR_EQ_0] THEN
    SUBGOAL_THEN `~(c = 64)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `word_or h1 h2:int64` WORD_CLZ_EQ_DIMINDEX) THEN
      ASM_REWRITE_TAC[DIMINDEX_64; WORD_OR_EQ_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `c < 64` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LT_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (word (63 - c)) (word 63):int64 = word c`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `i <= 63 <=> i < 64`] THEN
      REWRITE_TAC[WORD_BITWISE_RULE
       `word_xor a b:int64 = c <=> a = word_xor b c`] THEN
      SUBST1_TAC(ARITH_RULE `63 = 2 EXP 6 - 1`) THEN
      MATCH_MP_TAC WORD_SUB_MASK_WORD THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MOD_64_CLAUSES] THEN ASM_SIMP_TAC[MOD_LT] THEN
    SUBGOAL_THEN
     `val(word_subword (word_join (h1:int64) (l1:int64):int128)
                       (64 - c,64):int64) =
      (2 EXP c * (2 EXP 64 * val h1 + val l1)) DIV 2 EXP 64 /\
      val(word_subword (word_join (h2:int64) (l2:int64):int128)
                       (64 - c,64):int64) =
      (2 EXP c * (2 EXP 64 * val h2 + val l2)) DIV 2 EXP 64`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; LE_REFL] THEN
      SUBGOAL_THEN
       `!x. x DIV (2 EXP (64 - c)) = (2 EXP c * x) DIV 2 EXP 64`
       (fun th -> REWRITE_TAC[th])
      THENL
       [GEN_TAC THEN
        SUBGOAL_THEN
         `2 EXP 64 = 2 EXP c * 2 EXP (64 - c)`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
          UNDISCH_TAC `c <= 64` THEN ARITH_TAC;
          SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]];
        ALL_TAC] THEN
      MATCH_MP_TAC(MESON[MOD_LT]
       `x < n /\ y < n ==> x MOD n = x /\ y MOD n = y`) THEN
      SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      SUBGOAL_THEN `64 + 64 = c + 64 + (64 - c)` SUBST1_TAC THENL
       [UNDISCH_TAC `c <= 64` THEN ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[EXP_ADD] THEN
      SIMP_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
      ONCE_REWRITE_TAC[EXP_ADD] THEN CONJ_TAC THEN
      MATCH_MP_TAC (ARITH_RULE
       `e * h + e * 1 <= e * d /\ l < e ==> e * h + l < e * d`) THEN
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; VAL_BOUND_64; LE_MULT_LCANCEL] THEN
      REWRITE_TAC[EXP_EQ_0; ARITH_EQ; ARITH_RULE `h + 1 <= e <=> h < e`] THEN
      TRANS_TAC LET_TRANS `val(word_or h1 h2:int64)` THEN
      REWRITE_TAC[VAL_WORD_OR_LE] THEN
      MP_TAC(ISPECL [`word_or h1 h2:int64`; `c:num`]
        WORD_LE_CLZ_VAL) THEN
      ASM_REWRITE_TAC[DIMINDEX_64; LE_REFL];
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `a = 2 EXP 64 * h + l ==> 2 EXP 64 * h + l = a`))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `MAX (bitsize m) (bitsize n) + word_clz(word_or h1 h2:int64) = 64 * j`
    MP_TAC THENL
     [REWRITE_TAC[WORD_CLZ_OR] THEN
      DISJ_CASES_TAC(ARITH_RULE `m:num <= n \/ n <= m`) THENL
       [MATCH_MP_TAC(ARITH_RULE
         `m <= n /\ h2 <= h1 /\ n + h2 = x
          ==> MAX m n + MIN h1 h2 = x`) THEN
        ASM_SIMP_TAC[BITSIZE_MONO] THEN
        SUBGOAL_THEN `val(h1:int64) <= val(h2:int64)` MP_TAC THENL
         [SUBGOAL_THEN
           `2 EXP 64 * val(h1:int64) + val(l1:int64) <=
            2 EXP 64 * val(h2:int64) + val(l2:int64)`
          MP_TAC THENL
           [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIV_MONO THEN
            UNDISCH_TAC `m:num <= n` THEN ARITH_TAC;
            SIMP_TAC[LEXICOGRAPHIC_LE; VAL_BOUND_64] THEN ARITH_TAC];
          SIMP_TAC[WORD_CLZ_MONO]] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `h1 <= h2 ==> ~(h1 = 0 /\ h2 = 0) ==> ~(h2 = 0)`)) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[VAL_EQ_0] THEN UNDISCH_TAC `ODD n` THEN
          SIMP_TAC[GSYM NOT_EVEN; CONTRAPOS_THM; EVEN];
          DISCH_TAC] THEN
        ASM_CASES_TAC `n = 0` THENL
         [UNDISCH_TAC
           `2 EXP 64 * val(h2:int64) + val(l2:int64) =
            (2 EXP 128 * n) DIV 2 EXP (64 * j)` THEN
          ASM_REWRITE_TAC[MULT_CLAUSES; DIV_0; ADD_EQ_0] THEN
          ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ];
          ALL_TAC] THEN
        UNDISCH_THEN
         `2 EXP 64 * val(h2:int64) + val(l2:int64) =
          (2 EXP 128 * n) DIV 2 EXP (64 * j)`
         (MP_TAC o AP_TERM `bitsize`) THEN
        ASM_SIMP_TAC[BITSIZE_MULT_ADD; VAL_BOUND_64; VAL_EQ_0] THEN
        ASM_REWRITE_TAC[BITSIZE_DIV; BITSIZE_MULT] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `64 + b = (128 + m) - j
          ==> b <= 64 ==> m + (64 - b) = j`)) THEN
        REWRITE_TAC[WORD_CLZ_BITSIZE; DIMINDEX_64] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[BITSIZE_LE; VAL_BOUND_64];
        MATCH_MP_TAC(ARITH_RULE
         `n <= m /\ h1 <= h2 /\ m + h1 = x
          ==> MAX m n + MIN h1 h2 = x`) THEN
        ASM_SIMP_TAC[BITSIZE_MONO] THEN
        SUBGOAL_THEN `val(h2:int64) <= val(h1:int64)` MP_TAC THENL
         [SUBGOAL_THEN
           `2 EXP 64 * val(h2:int64) + val(l2:int64) <=
            2 EXP 64 * val(h1:int64) + val(l1:int64)`
          MP_TAC THENL
           [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIV_MONO THEN
            UNDISCH_TAC `n:num <= m` THEN ARITH_TAC;
            SIMP_TAC[LEXICOGRAPHIC_LE; VAL_BOUND_64] THEN ARITH_TAC];
          SIMP_TAC[WORD_CLZ_MONO]] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `h2 <= h1 ==> ~(h1 = 0 /\ h2 = 0) ==> ~(h1 = 0)`)) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[VAL_EQ_0] THEN UNDISCH_TAC `ODD n` THEN
          SIMP_TAC[GSYM NOT_EVEN; CONTRAPOS_THM; EVEN];
          DISCH_TAC] THEN
        ASM_CASES_TAC `m = 0` THENL
         [UNDISCH_TAC
           `2 EXP 64 * val(h1:int64) + val(l1:int64) =
            (2 EXP 128 * m) DIV 2 EXP (64 * j)` THEN
          ASM_REWRITE_TAC[MULT_CLAUSES; DIV_0; ADD_EQ_0] THEN
          ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ];
          ALL_TAC] THEN
        UNDISCH_THEN
         `2 EXP 64 * val(h1:int64) + val(l1:int64) =
          (2 EXP 128 * m) DIV 2 EXP (64 * j)`
         (MP_TAC o AP_TERM `bitsize`) THEN
        ASM_SIMP_TAC[BITSIZE_MULT_ADD; VAL_BOUND_64; VAL_EQ_0] THEN
        ASM_REWRITE_TAC[BITSIZE_DIV; BITSIZE_MULT] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `64 + b = (128 + m) - j
          ==> b <= 64 ==> m + (64 - b) = j`)) THEN
        REWRITE_TAC[WORD_CLZ_BITSIZE; DIMINDEX_64] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[BITSIZE_LE; VAL_BOUND_64]];
      ASM_REWRITE_TAC[]] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM INT_OF_NUM_EQ] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [GSYM INT_OF_NUM_CLAUSES] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INT_ARITH
     `bb + c:int = x ==> bb - &64 = x - (c + &64)`)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!x. (2 EXP c * (2 EXP 128 * x) DIV 2 EXP (64 * j)) DIV 2 EXP 64 =
          (2 EXP 128 * x) DIV 2 EXP (64 * j + (64 - c))`
     (fun th -> REWRITE_TAC[th])
    THENL
     [SUBGOAL_THEN `2 EXP 64 = 2 EXP c * 2 EXP (64 - c)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `c <= 64` THEN ARITH_TAC;
        SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]] THEN
      REWRITE_TAC[DIV_DIV; GSYM EXP_ADD];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV
     [INT_ARITH `base:int = &64 * j - (c + &64) <=>
                 (&64 * j + (&64 - c)) - &128 = base`] THEN
    DISCH_THEN(fun th -> SUBST1_TAC(SYM th) THEN ASSUME_TAC th) THEN
    SIMP_TAC[REAL_ZPOW_SUB; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV; REAL_ZPOW_NUM] THEN
    REWRITE_TAC[REAL_ARITH
     `m * inv(x:real) * &2 pow 128 = (&2 pow 128 * m) * inv x`] THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB] THEN REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[GSYM real_div; REAL_ZPOW_NUM] THEN
    GEN_REWRITE_TAC I [TAUT
     `p /\ q /\ r /\ s /\ t <=>
     ((p /\ r) /\ (q /\ s)) /\ (p /\ q /\ r /\ s ==> t)`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x - y:real <= &0 <=> x <= y`] THEN
      REWRITE_TAC[REAL_ARITH `--(&1):real <= x - y <=> y <= x + &1`] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_ARITH `x:real <= (a + &1) * y <=> x - a * y <= y`] THEN
      GEN_REWRITE_TAC (RAND_CONV o BINOP_CONV)
       [REAL_ARITH `x:real <= y <=> &0 <= y - x`] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES;
                  REWRITE_RULE[REAL_OF_NUM_MUL] (GSYM REAL_OF_NUM_MOD)] THEN
      REWRITE_TAC[LE_0] THEN
      SIMP_TAC[LT_IMP_LE; MOD_LT_EQ; ARITH_EQ; EXP_EQ_0];
      REWRITE_TAC[REAL_ARITH `--(&1) <= y - x <=> x:real <= y + &1`] THEN
      REWRITE_TAC[REAL_ARITH `x - y:real <= &0 <=> x <= y`] THEN
      STRIP_TAC THEN REWRITE_TAC[EXP; MULT_CLAUSES; LE_0] THEN
      ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `&2 pow 63 * &2 zpow base <= max (&m) (&n)` MP_TAC THENL
     [SUBST1_TAC(SYM(ASSUME
       `&(MAX (bitsize m) (bitsize n)) - &64:int = base`)) THEN
      REWRITE_TAC[GSYM BITSIZE_MAX] THEN
      SIMP_TAC[REAL_ZPOW_SUB; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[REAL_ZPOW_NUM; REAL_ARITH
       `&2 pow 63 * (x:real) / &2 pow 64 <= a <=> x <= &2 * a`] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC BITSIZE_REV_ALT THEN
      REWRITE_TAC[ARITH_RULE `MAX m n = 0 <=> m = 0 /\ n = 0`] THEN
      DISCH_TAC THEN UNDISCH_TAC `ODD n` THEN ASM_REWRITE_TAC[ODD];
      REWRITE_TAC[IMP_IMP]] THEN
    SUBST1_TAC(SYM(ASSUME `(&64 * &j + &64 - &c) - &128:int = base`)) THEN
    SIMP_TAC[REAL_ZPOW_SUB; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[REAL_ZPOW_NUM; REAL_ARITH
     `(x:real < y / &2 pow 128 * &2 pow 5 <=> &2 pow 123 * x < y) /\
      (&2 pow 63 * x / &2 pow 128 <= a <=> x <= &2 pow 65 * a)`] THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB] THEN REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_ZPOW_NUM; REAL_OF_NUM_CLAUSES] THEN
    DISJ_CASES_TAC(ARITH_RULE `m:num <= n \/ n <= m`) THEN
    ASM_SIMP_TAC[ARITH_RULE `m <= n ==> MAX m n = n /\ MIN m n = m`;
                 ARITH_RULE `n <= m ==> MAX m n = m /\ MIN m n = n`] THEN
    STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC(TAUT `(q /\ r ==> p) /\ q /\ r ==> p /\ q /\ r`) THEN
    (CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[ARITH_RULE
     `2 EXP 128 * m < n * 2 EXP 5 <=> 2 EXP 123 * m < n`] THEN
    MATCH_MP_TAC(ARITH_RULE `x <= y ==> x <= y + 31`) THEN
    ASM_SIMP_TAC[LE_RDIV_EQ; EXP_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[ARITH_RULE
     `m * 2 EXP 63 <= 2 EXP 128 * n <=> m <= 2 EXP 65 * n`];

    (*** The fact that the invariant is preserved over the loop ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `m_m:num` `\s. val(read R10 s)` THEN
    GHOST_INTRO_TAC `m_n:num` `\s. val(read R11 s)` THEN
    GHOST_INTRO_TAC `n_m:num` `\s. val(read RCX s)` THEN
    GHOST_INTRO_TAC `n_n:num` `\s. val(read RDX s)` THEN
    GHOST_INTRO_TAC `m_hi:num` `\s. val(read R12 s)` THEN
    GHOST_INTRO_TAC `n_hi:num` `\s. val(read RBP s)` THEN
    GHOST_INTRO_TAC `m_lo:num` `\s. val(read RDI s)` THEN
    GHOST_INTRO_TAC `n_lo:num` `\s. val(read RSI s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN

    ONCE_REWRITE_TAC[TAUT `p \/ q \/ r <=> ~p /\ ~q ==> r`] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TAUT `~p /\ ~q ==> r <=> p \/ q \/ r`]) THEN
    REWRITE_TAC[TAUT `~p /\ ~q ==> r <=> p \/ q \/ r`] THEN

    MAP_EVERY VAL_INT64_TAC
     [`m_m:num`; `m_n:num`; `n_m:num`; `n_n:num`;
      `m_hi:num`; `n_hi:num`; `m_lo:num`; `n_lo:num`] THEN

    X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--29) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    DISCARD_STATE_TAC "s29" THEN

    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `n - (i + 1) = n - i - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 58 ==> 1 <= 58 - i`];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM CONJ_ASSOC];
      VAL_INT64_TAC `58 - (i + 1)` THEN
      ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC] THEN

    REWRITE_TAC[WORD_AND_1_BITVAL; BIT_LSB_WORD; VAL_WORD_BITVAL;
                BITVAL_EQ_0; COND_SWAP] THEN
    SIMP_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[WORD_RULE
     `word_not (word_add x y) =
      word_neg(word_add x (word_add y (word 1)))`] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN

    REWRITE_TAC[COND_SWAP; MESON[VAL_WORD_0; CONJUNCT1 LT; NOT_LT]
     `(a < val(if p then x else word 0) <=> a < val x /\ p) /\
      (val(if p then x else word 0) <= a <=> ~(a < val x /\ p))`] THEN

    SUBGOAL_THEN
     `val(word(n_m + n_m):int64) = n_m + n_m /\
      val(word(n_n + n_n):int64) = n_n + n_n /\
      val(word(m_n + n_n):int64) = m_n + n_n /\
      val(word(m_m + n_m):int64) = m_m + n_m /\
      val(word(m_m + m_m):int64) = m_m + m_m /\
      val(word(m_n + m_n):int64) = m_n + m_n /\
      val(word(n_m + m_m):int64) = m_m + n_m /\
      val(word(n_n + m_n):int64) = m_n + n_n`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN REWRITE_TAC[ADD_SYM] THEN
      MATCH_MP_TAC VAL_WORD_EQ THEN
      TRANS_TAC LET_TRANS `2 EXP (i + 1)` THEN
      ASM_SIMP_TAC[LT_EXP; DIMINDEX_64; ARITH_RULE
       `i < 58 ==> i + 1 < 64`] THEN
      REWRITE_TAC[EXP_ADD] THEN
      MAP_EVERY UNDISCH_TAC
       [`m_m + m_n <= 2 EXP i`; `n_m + n_n <= 2 EXP i`] THEN
      ARITH_TAC;
      ALL_TAC] THEN

    ASM_CASES_TAC `m_hi < n_hi /\ ODD m_lo` THEN
    ASM_REWRITE_TAC[BIT_LSB_WORD; WORD_AND_MASK; WORD_NEG_SUB] THEN
    ASM_REWRITE_TAC[GSYM NOT_LT] THENL
     [ASM_REWRITE_TAC[NOT_LT];
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[NOT_LT]] THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_0; LE_0; ADD_CLAUSES] THEN
    REWRITE_TAC[WORD_NEG_SUB; WORD_RULE
     `word_add (word_neg x) y = word_sub y x`] THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; EXP_1; ADD_CLAUSES; WORD_SUB_0] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[EXP_ADD] THEN MAP_EVERY UNDISCH_TAC
       [`m_m + m_n <= 2 EXP i`; `n_m + n_n <= 2 EXP i`] THEN
      ARITH_TAC;
      ALL_TAC]) THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num`
     (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    MAP_EVERY ABBREV_TAC
     [`m':real = -- &1 pow q * (&m_m * &m - &m_n * &n)`;
      `n':real = --(-- &1 pow q) * (&n_m * &m - &n_n * &n)`] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD; INT_POW_ADD; INT_POW_1] THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC; INT_ADD_ASSOC] THEN
    MP_TAC(SPECL [`&2:real`; `base + &i:int`; `&1:int`]
        REAL_ZPOW_ADD) THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; REAL_ZPOW_1; ARITH_EQ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM INT_ADD_ASSOC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[INT_ARITH
         `(a + b) * x - (c + d) * y:int =
          (a * x - c * y) + (b * x - d * y)`] THEN
        ABBREV_TAC `mi:int = &m_m * &m - &m_n * &n` THEN
        ABBREV_TAC `ni:int = &n_m * &m - &n_n * &n` THEN
        ONCE_REWRITE_TAC[INT_ARITH `e * &2 * x:int = &2 * e * x`] THEN
        FIRST_X_ASSUM(fun th ->
         GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `&2:int` o MATCH_MP (INTEGER_RULE
         `(w * m:int == e * n) (mod d)
          ==> !t. (t * e) divides d /\ w pow 2 = &1
                   ==> e divides m /\ (m == e * w * n) (mod (e * t))`))) THEN
        REWRITE_TAC[INT_POW_ONE; INT_ARITH `(--x:int) pow 2 = x pow 2`] THEN
        ONCE_REWRITE_TAC[MESON[INT_POW_POW; MULT_SYM]
         `(x:int) pow m pow n = x pow n pow m`] THEN
        REWRITE_TAC[INT_POW_ONE; INT_ARITH `(--x:int) pow 2 = x pow 2`] THEN
        ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP; GSYM(CONJUNCT2 INT_POW);
                     ARITH_RULE `i < 58 ==> SUC i <= 64`] THEN
        SIMP_TAC[IMP_CONJ; int_divides; LEFT_IMP_EXISTS_THM; INTEGER_RULE
         `(a * x == a * y) (mod (a * n)) <=>
          a:int = &0 \/ (x == y) (mod n)`] THEN
        REWRITE_TAC[INT_POW_EQ_0; ARITH_EQ; INT_OF_NUM_EQ] THEN
        X_GEN_TAC `md:int` THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
        X_GEN_TAC `nd:int` THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
        REWRITE_TAC[GSYM INT_ADD_LDISTRIB; INT_GCD_LMUL] THEN
        REWRITE_TAC[INT_ARITH `&2 * x * y:int = x * &2 * y`] THEN
        AP_TERM_TAC THEN REWRITE_TAC[GSYM INT_MUL_2] THEN
        W(MP_TAC o PART_MATCH (lhand o rand)
         INT_GCD_COPRIME_DIVIDES_RMUL o lhand o snd) THEN
        REWRITE_TAC[INT_ABS_NUM; INT_GCD_ADD] THEN
        REWRITE_TAC[INT_GCD_SYM] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
         `(m:int == m') (mod t)
          ==> coprime(t,m') /\ t divides m' + n
              ==> coprime(t,m) /\ t divides m + n`)) THEN
        REWRITE_TAC[INT_COPRIME_RMUL; INT_COPRIME_RPOW; INT_COPRIME_RNEG] THEN
        ASM_REWRITE_TAC[GSYM num_coprime; COPRIME_2; ARITH] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
         `(n:int == n') (mod t)
          ==> t divides m + n' ==> t divides m + n`)) THEN
        ASM_REWRITE_TAC[INT_2_DIVIDES_ADD; INT_2_DIVIDES_MUL; INT_DIVIDES_RNEG;
          INT_2_DIVIDES_POW;GSYM num_divides; DIVIDES_2; ARITH] THEN
        ASM_REWRITE_TAC[GSYM NOT_ODD];
        ALL_TAC] THEN

      EXISTS_TAC `SUC q` THEN
      GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[INT_OF_NUM_MUL; DOUBLE_HALF; GSYM NOT_ODD;
                     ODD_VAL_WORD_SUB] THEN
        MP_TAC(ISPECL [`word n_lo:int64`; `word m_lo:int64`]
          INT_CONG_WORD_SUB) THEN
        ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_POW; DIMINDEX_64] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INT_CONG_SYM])) THEN
        SPEC_TAC(`(&2:int) pow 64`,`mm:int`) THEN CONV_TAC INTEGER_RULE;
        ALL_TAC] THEN

      REWRITE_TAC[real_pow] THEN
      REWRITE_TAC[GSYM REAL_NEG_MINUS1; REAL_NEG_NEG] THEN
      REWRITE_TAC[REAL_ARITH `(a + a) * b:real = &2 * a * b`] THEN
      ASM_REWRITE_TAC[REAL_ARITH
       `s * (&2 * x - &2 * y):real = &2 * s * (x - y)`] THEN
      ONCE_REWRITE_TAC[REAL_ARITH
       `s * x * &2 * y:real = (s * x) * &2 * y`] THEN
      ASM_REWRITE_TAC[REAL_ARITH
       `--(-- &1 pow q) * ((&m_m + &n_m) * &m - (&m_n + &n_n) * &n):real =
        --(-- &1 pow q) * (&n_m * &m - &n_n * &n) -
        -- &1 pow q * (&m_m * &m - &m_n * &n)`] THEN
      ASM_SIMP_TAC[VAL_WORD_SUB_CASES; LT_IMP_LE] THEN
      REWRITE_TAC[REAL_FIELD `(&2 * x) / (y * &2):real = x / y`] THEN
      ASM_REWRITE_TAC[GSYM ADD1] THEN REWRITE_TAC[ADD1] THEN

      GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_ARITH
         `--(e / &2):real <= x - y <=> --e <= &2 * x - &2 * y`] THEN
        REWRITE_TAC[REAL_ARITH
         `x - y:real <= e / &2 <=> &2 * x - &2 * y <= e`] THEN
        REWRITE_TAC[REAL_FIELD `&2 * x / (y * &2):real = x / y`] THEN
        MP_TAC(ARITH_RULE
         `0 <= (n_hi - m_hi) MOD 2 /\ (n_hi - m_hi) MOD 2 <= 1`) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
        ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
        MAP_EVERY UNDISCH_TAC
         [`--lowerr i <= &m_hi - m' / &2 zpow (base + &i)`;
          `--lowerr i <= &n_hi - n' / &2 zpow (base + &i)`;
          `&m_hi - m' / &2 zpow (base + &i) <= upperr i`;
          `&n_hi - n' / &2 zpow (base + &i) <= upperr i`] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN

      CONJ_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `--(lowerr:num->real) i` THEN
        ASM_SIMP_TAC[LT_IMP_LE];
        ALL_TAC] THEN

      CONJ_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `(upperr:num->real) i` THEN
        ASM_SIMP_TAC[LT_IMP_LE];
        ALL_TAC] THEN

      (*** The big-small invariant ***)

      CONJ_TAC THENL
       [DISCH_THEN(fun th ->
          FIRST_X_ASSUM(MP_TAC o C MP th) THEN ASSUME_TAC th) THEN
        ASM_REWRITE_TAC[ARITH_RULE `i <= 57 <=> i < 58`] THEN
        ASM_SIMP_TAC[ARITH_RULE `m:num < n ==> ~(n < m)`] THEN
        STRIP_TAC THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_ARITH
           `a * abs(&2 * b):real <= (e * &2) * c <=> a * abs b <= e * c`] THEN
          TRANS_TAC REAL_LE_TRANS `abs m' * abs n':real` THEN
          ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
          MATCH_MP_TAC(REAL_ARITH
           `&0:real <= x /\ &0 <= y /\ y <= &2 * x
            ==> abs(x - y) <= abs x`) THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN
           `m' / &2 zpow (base + &i) <= (&2 * n') / &2 zpow (base + &i)`
          MP_TAC THENL
           [ALL_TAC;
            ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT;
                         REAL_SUB_LE; ARITH]] THEN
          TRANS_TAC REAL_LE_TRANS `&m_hi + &1:real` THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[REAL_ARITH `(&2 * x) / y:real = &2 * x / y`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `n_hi - n':real <= i
            ==> m + &2 * i <= &2 * n_hi ==> m <= &2 * n'`)) THEN
          MATCH_MP_TAC(REAL_ARITH
           `u:real < &16 /\ m + &33 <= n ==> (m + &1) + &2 * u <= n`) THEN
          ASM_SIMP_TAC[REAL_OF_NUM_CLAUSES; LT_IMP_LE] THEN
          MATCH_MP_TAC(ARITH_RULE
           `m < 2 EXP 5 /\ 2 EXP 63 <= 2 EXP 57 * (n + 31)
            ==> m + 33 <= 2 * n`) THEN
          ASM_REWRITE_TAC[] THEN
          TRANS_TAC LE_TRANS `2 EXP i * (n_hi + 31)` THEN
          ASM_REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN
          UNDISCH_TAC `i < 58` THEN ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `i + 1 < 58 <=> i <= 56`] THEN DISCH_TAC THEN
        REWRITE_TAC[REAL_SUB_LE] THEN
        MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
         [SUBGOAL_THEN `m' / &2 zpow (base + &i) <= n' / &2 zpow (base + &i)`
          MP_TAC THENL
           [ALL_TAC;
            ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT;
                         REAL_SUB_LE; ARITH]] THEN
          TRANS_TAC REAL_LE_TRANS `&m_hi + &1:real` THEN ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `n_hi - n':real <= i ==> m + i <= n_hi ==> m <= n'`)) THEN
          MATCH_MP_TAC(REAL_ARITH
           `u:real < &16 /\ m + &17 <= n ==> (m + &1) + u <= n`) THEN
          ASM_SIMP_TAC[REAL_OF_NUM_CLAUSES; LT_IMP_LE] THEN
          MATCH_MP_TAC(ARITH_RULE
           `m < 2 EXP 5 /\ 2 EXP 63 <= 2 EXP 56 * (n + 31)
            ==> m + 17 <= n`) THEN
          ASM_REWRITE_TAC[] THEN
          TRANS_TAC LE_TRANS `2 EXP i * (n_hi + 31)` THEN
          ASM_REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN ARITH_TAC;
          DISCH_TAC] THEN

        CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN

        DISJ2_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC(ARITH_RULE
           `m < 2 EXP 5 /\ 2 EXP 63 <= 2 EXP 56 * (n + 31)
            ==> m < (n - m) DIV 2`) THEN
          ASM_REWRITE_TAC[] THEN
          TRANS_TAC LE_TRANS `2 EXP i * (n_hi + 31)` THEN
          ASM_SIMP_TAC[LE_MULT_RCANCEL; LE_EXP; LT_IMP_LE] THEN
          ARITH_TAC;
          ALL_TAC] THEN

        UNDISCH_TAC `2 EXP 63 <= 2 EXP i * (n_hi + 31)` THEN
        SUBGOAL_THEN `63 = (i + 1) + (62 - i)` SUBST1_TAC THENL
         [UNDISCH_TAC `i < 58` THEN ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [EXP_ADD] THEN
        GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [EXP_ADD] THEN
        REWRITE_TAC[GSYM MULT_ASSOC; LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
        UNDISCH_TAC `m_hi < 2 EXP 5` THEN ARITH_TAC;
        ALL_TAC] THEN

      (*** The main invariant with case splits ***)

      FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [ASM_CASES_TAC `m':real <= n'` THENL
         [DISJ1_TAC THEN ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_MUL; REAL_POS] THEN
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN CONJ_TAC THENL
           [MAP_EVERY UNDISCH_TAC
             [`min m' n':real <= &2 pow i * min (&m) (&n)`;
              `m':real <= n'`] THEN
            CONV_TAC REAL_ARITH;
            ALL_TAC] THEN
          TRANS_TAC REAL_LE_TRANS `n' * &2 * m':real` THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_RMUL THEN
            MAP_EVERY UNDISCH_TAC [`&0:real <= m'`; `m':real <= n'`] THEN
            CONV_TAC REAL_ARITH;
            UNDISCH_TAC `m' * n':real <= &2 pow i * &m * &n` THEN
            CONV_TAC REAL_ARITH];
          RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
          DISJ2_TAC THEN DISJ1_TAC THEN
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN
          ASM_REWRITE_TAC[REAL_ARITH `n' - m':real < &0 <=> n' < m'`] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC(ARITH_RULE `n < m + 32 ==> (n - m) DIV 2 < 16`) THEN
            REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
             `n - n':real <= u ==> u < &16 /\ n' <= m + &16
              ==> n < m + &32`)) THEN
            ASM_SIMP_TAC[LT_IMP_LE] THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
             `--l <= m - m':real ==> l < &16 /\ n' < m'
              ==> n' <= m + &16`)) THEN
            ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT;
                         LT_IMP_LE; ARITH];
            TRANS_TAC REAL_LTE_TRANS `&n_hi:real` THEN
            ASM_SIMP_TAC[REAL_OF_NUM_LT] THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
             `n - n':real <= u ==> u < &16 /\ n' <= m
              ==> n <= m + &16`)) THEN
            ASM_SIMP_TAC[LT_IMP_LE] THEN
            ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ZPOW_LT;
                         REAL_OF_NUM_LT; ARITH] THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
             `min m n:real <= e ==> n < m /\ e <= d ==> n <= d`)) THEN
            ASM_REWRITE_TAC[real_div; GSYM REAL_ZPOW_NEG] THEN
            ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_ZPOW_ADD;
                         REAL_OF_NUM_EQ; ARITH_EQ] THEN
            REWRITE_TAC[INT_ARITH `--b + b + i:int = i`] THEN
            REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL; REAL_ZPOW_NUM]]];
        DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_ARITH `m:real < &0 ==> &2 * m < &0`] THEN
        ASM_SIMP_TAC[REAL_ARITH `m:real < &0 /\ &0 <= n ==> &0 <= n - m`] THEN
        TRANS_TAC REAL_LET_TRANS `&n_hi:real` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
        DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL] THEN
        ASM_SIMP_TAC[REAL_ARITH `m:real < &0 /\ &0 <= n ==> m - n < &0`] THEN
        TRANS_TAC LET_TRANS `n_hi:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];

      (*** Second main split ****)

      UNDISCH_TAC `~(m_hi:num < n_hi /\ ODD m_lo)` THEN
      ASM_REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[INT_ARITH
         `(a + b) * x - (c + d) * y:int =
          (a * x - c * y) + (b * x - d * y)`] THEN
        ABBREV_TAC `mi:int = &m_m * &m - &m_n * &n` THEN
        ABBREV_TAC `ni:int = &n_m * &m - &n_n * &n` THEN
        ONCE_REWRITE_TAC[INT_ARITH `e * &2 * x:int = &2 * e * x`] THEN
        FIRST_X_ASSUM(fun th ->
         GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `&2:int` o MATCH_MP (INTEGER_RULE
         `(w * m:int == e * n) (mod d)
          ==> !t. (t * e) divides d /\ w pow 2 = &1
                   ==> e divides m /\ (m == e * w * n) (mod (e * t))`))) THEN
        REWRITE_TAC[INT_POW_ONE; INT_ARITH `(--x:int) pow 2 = x pow 2`] THEN
        ONCE_REWRITE_TAC[MESON[INT_POW_POW; MULT_SYM]
         `(x:int) pow m pow n = x pow n pow m`] THEN
        REWRITE_TAC[INT_POW_ONE; INT_ARITH `(--x:int) pow 2 = x pow 2`] THEN
        ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP; GSYM(CONJUNCT2 INT_POW);
                     ARITH_RULE `i < 58 ==> SUC i <= 64`] THEN
        SIMP_TAC[IMP_CONJ; int_divides; LEFT_IMP_EXISTS_THM; INTEGER_RULE
         `(a * x == a * y) (mod (a * n)) <=>
          a:int = &0 \/ (x == y) (mod n)`] THEN
        REWRITE_TAC[INT_POW_EQ_0; ARITH_EQ; INT_OF_NUM_EQ] THEN
        X_GEN_TAC `md:int` THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
        X_GEN_TAC `nd:int` THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
        REWRITE_TAC[GSYM INT_ADD_LDISTRIB; INT_GCD_LMUL] THEN
        REWRITE_TAC[INT_ARITH `&2 * x * y:int = x * &2 * y`] THEN
        AP_TERM_TAC THEN REWRITE_TAC[GSYM INT_MUL_2] THEN
        W(MP_TAC o PART_MATCH (lhand o rand)
         INT_GCD_COPRIME_DIVIDES_RMUL o lhand o snd) THEN
        REWRITE_TAC[INT_ABS_NUM; INT_GCD_ADD] THEN
        REWRITE_TAC[INT_GCD_SYM] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
         `(n:int == n') (mod t)
          ==> coprime(t,n') /\ t divides m + n'
              ==> coprime(t,n) /\ t divides m + n`)) THEN
        REWRITE_TAC[INT_COPRIME_RMUL; INT_COPRIME_RPOW; INT_COPRIME_RNEG] THEN
        ASM_REWRITE_TAC[GSYM num_coprime; COPRIME_2; ARITH] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
         `(m:int == m') (mod t)
          ==> t divides m' + n ==> t divides m + n`)) THEN
        ASM_REWRITE_TAC[INT_2_DIVIDES_ADD; INT_2_DIVIDES_MUL; INT_DIVIDES_RNEG;
          INT_2_DIVIDES_POW;GSYM num_divides; DIVIDES_2; ARITH] THEN
        ASM_REWRITE_TAC[GSYM NOT_ODD];
        ALL_TAC] THEN

      EXISTS_TAC `q:num` THEN
      GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[INT_OF_NUM_MUL; DOUBLE_HALF; GSYM NOT_ODD;
                     ODD_VAL_WORD_SUB] THEN
        MP_TAC(ISPECL [`word m_lo:int64`; `word n_lo:int64`]
          INT_CONG_WORD_SUB) THEN
        ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_POW; DIMINDEX_64] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INT_CONG_SYM])) THEN
        SPEC_TAC(`(&2:int) pow 64`,`mm:int`) THEN CONV_TAC INTEGER_RULE;
        ALL_TAC] THEN
      REWRITE_TAC[real_pow] THEN
      REWRITE_TAC[REAL_ARITH `(a + a) * b:real = &2 * a * b`] THEN
      ASM_REWRITE_TAC[REAL_ARITH
       `s * (&2 * x - &2 * y):real = &2 * s * (x - y)`] THEN
      ASM_REWRITE_TAC[REAL_ARITH
       `-- &1 pow q * ((&m_m + &n_m) * &m - (&m_n + &n_n) * &n):real =
        -- &1 pow q * (&m_m * &m - &m_n * &n) -
        --(-- &1 pow q) * (&n_m * &m - &n_n * &n)`] THEN
      ASM_SIMP_TAC[VAL_WORD_SUB_CASES; LT_IMP_LE] THEN
      REWRITE_TAC[REAL_FIELD `(&2 * x) / (y * &2):real = x / y`] THEN
      ASM_REWRITE_TAC[GSYM ADD1] THEN REWRITE_TAC[ADD1] THEN

      GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_ARITH
         `--(e / &2):real <= x - y <=> --e <= &2 * x - &2 * y`] THEN
        REWRITE_TAC[REAL_ARITH
         `x - y:real <= e / &2 <=> &2 * x - &2 * y <= e`] THEN
        REWRITE_TAC[REAL_FIELD `&2 * x / (y * &2):real = x / y`] THEN
        MP_TAC(ARITH_RULE
         `0 <= (m_hi - n_hi) MOD 2 /\ (m_hi - n_hi) MOD 2 <= 1`) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
        ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
        MAP_EVERY UNDISCH_TAC
         [`--lowerr i <= &m_hi - m' / &2 zpow (base + &i)`;
          `--lowerr i <= &n_hi - n' / &2 zpow (base + &i)`;
          `&m_hi - m' / &2 zpow (base + &i) <= upperr i`;
          `&n_hi - n' / &2 zpow (base + &i) <= upperr i`] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN

      CONJ_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `--(lowerr:num->real) i` THEN
        ASM_SIMP_TAC[LT_IMP_LE];
        ALL_TAC] THEN

      CONJ_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `(upperr:num->real) i` THEN
        ASM_SIMP_TAC[LT_IMP_LE];
        ALL_TAC] THEN

      (*** The big-small invariant ***)

      CONJ_TAC THENL
       [DISCH_THEN(fun th ->
          FIRST_X_ASSUM(MP_TAC o C MP th) THEN ASSUME_TAC th) THEN
        ASM_REWRITE_TAC[ARITH_RULE `i <= 57 <=> i < 58`] THEN
        ASM_SIMP_TAC[ARITH_RULE `m:num <= n ==> ~(n < m)`] THEN
        STRIP_TAC THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_ARITH
           `a * abs(&2 * b):real <= (e * &2) * c <=> a * abs b <= e * c`] THEN
          TRANS_TAC REAL_LE_TRANS `abs m' * abs n':real` THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
          MATCH_MP_TAC(REAL_ARITH
           `&0:real <= x /\ &0 <= y /\ y <= &2 * x
            ==> abs(x - y) <= abs x`) THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN
           `n' / &2 zpow (base + &i) <= (&2 * m') / &2 zpow (base + &i)`
          MP_TAC THENL
           [ALL_TAC;
            ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT;
                         REAL_SUB_LE; ARITH]] THEN
          TRANS_TAC REAL_LE_TRANS `&n_hi + &1:real` THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[REAL_ARITH `(&2 * x) / y:real = &2 * x / y`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `n_hi - n':real <= i
            ==> m + &2 * i <= &2 * n_hi ==> m <= &2 * n'`)) THEN
          MATCH_MP_TAC(REAL_ARITH
           `u:real < &16 /\ m + &33 <= n ==> (m + &1) + &2 * u <= n`) THEN
          ASM_SIMP_TAC[REAL_OF_NUM_CLAUSES; LT_IMP_LE] THEN
          MATCH_MP_TAC(ARITH_RULE
           `m < 2 EXP 5 /\ 2 EXP 63 <= 2 EXP 57 * (n + 31)
            ==> m + 33 <= 2 * n`) THEN
          ASM_REWRITE_TAC[] THEN
          TRANS_TAC LE_TRANS `2 EXP i * (m_hi + 31)` THEN
          ASM_REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN
          UNDISCH_TAC `i < 58` THEN ARITH_TAC;
          ALL_TAC] THEN

        REWRITE_TAC[ARITH_RULE `i + 1 < 58 <=> i <= 56`] THEN DISCH_TAC THEN
        REWRITE_TAC[REAL_SUB_LE] THEN
        MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
         [SUBGOAL_THEN `n' / &2 zpow (base + &i) <= m' / &2 zpow (base + &i)`
          MP_TAC THENL
           [ALL_TAC;
            ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT;
                         REAL_SUB_LE; ARITH]] THEN
          TRANS_TAC REAL_LE_TRANS `&n_hi + &1:real` THEN ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `n_hi - n':real <= i ==> m + i <= n_hi ==> m <= n'`)) THEN
          MATCH_MP_TAC(REAL_ARITH
           `u:real < &16 /\ m + &17 <= n ==> (m + &1) + u <= n`) THEN
          ASM_SIMP_TAC[REAL_OF_NUM_CLAUSES; LT_IMP_LE] THEN
          MATCH_MP_TAC(ARITH_RULE
           `m < 2 EXP 5 /\ 2 EXP 63 <= 2 EXP 56 * (n + 31)
            ==> m + 17 <= n`) THEN
          ASM_REWRITE_TAC[] THEN
          TRANS_TAC LE_TRANS `2 EXP i * (m_hi + 31)` THEN
          ASM_REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN ARITH_TAC;
          DISCH_TAC] THEN

        CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN

        DISJ2_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC(ARITH_RULE
           `m < 2 EXP 5 /\ 2 EXP 63 <= 2 EXP 56 * (n + 31)
            ==> m < (n - m) DIV 2`) THEN
          ASM_REWRITE_TAC[] THEN
          TRANS_TAC LE_TRANS `2 EXP i * (m_hi + 31)` THEN
          ASM_SIMP_TAC[LE_MULT_RCANCEL; LE_EXP; LT_IMP_LE] THEN
          ARITH_TAC;
          ALL_TAC] THEN

        UNDISCH_TAC `2 EXP 63 <= 2 EXP i * (m_hi + 31)` THEN
        SUBGOAL_THEN `63 = (i + 1) + (62 - i)` SUBST1_TAC THENL
         [UNDISCH_TAC `i < 58` THEN ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [EXP_ADD] THEN
        GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [EXP_ADD] THEN
        REWRITE_TAC[GSYM MULT_ASSOC; LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
        UNDISCH_TAC `n_hi < 2 EXP 5` THEN ARITH_TAC;
        ALL_TAC] THEN

      (*** The main invariant with case splits ***)

      FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [ASM_CASES_TAC `n':real <= m'` THENL
         [DISJ1_TAC THEN ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_MUL; REAL_POS] THEN
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN CONJ_TAC THENL
           [MAP_EVERY UNDISCH_TAC
             [`min m' n':real <= &2 pow i * min (&m) (&n)`;
              `n':real <= m'`] THEN
            CONV_TAC REAL_ARITH;
            ALL_TAC] THEN
          TRANS_TAC REAL_LE_TRANS `m' * &2 * n':real` THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_RMUL THEN
            MAP_EVERY UNDISCH_TAC [`&0:real <= n'`; `n':real <= m'`] THEN
            CONV_TAC REAL_ARITH;
            UNDISCH_TAC `m' * n':real <= &2 pow i * &m * &n` THEN
            CONV_TAC REAL_ARITH];
          RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
          DISJ2_TAC THEN DISJ1_TAC THEN
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN
          ASM_REWRITE_TAC[REAL_ARITH `n' - m':real < &0 <=> n' < m'`] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC(ARITH_RULE `m < n + 32 ==> (m - n) DIV 2 < 16`) THEN
            REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
             `m - m':real <= u ==> u < &16 /\ m' <= n + &16
              ==> m < n + &32`)) THEN
            ASM_SIMP_TAC[LT_IMP_LE] THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
             `--l <= n - n':real ==> l < &16 /\ m' < n'
              ==> m' <= n + &16`)) THEN
            ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT;
                         LT_IMP_LE; ARITH];
            TRANS_TAC REAL_LET_TRANS `&m_hi:real` THEN
            ASM_SIMP_TAC[REAL_OF_NUM_LE] THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
             `m - m':real <= u ==> u < &16 /\ m' <= n
              ==> m < n + &16`)) THEN
            ASM_SIMP_TAC[LT_IMP_LE] THEN
            ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ZPOW_LT;
                         REAL_OF_NUM_LT; ARITH] THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
             `min m n:real <= e ==> m < n /\ e <= d ==> m <= d`)) THEN
            ASM_REWRITE_TAC[real_div; GSYM REAL_ZPOW_NEG] THEN
            ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_ZPOW_ADD;
                         REAL_OF_NUM_EQ; ARITH_EQ] THEN
            REWRITE_TAC[INT_ARITH `--b + b + i:int = i`] THEN
            REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL; REAL_ZPOW_NUM]]];

        DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL] THEN
        ASM_SIMP_TAC[REAL_ARITH `m:real < &0 /\ &0 <= n ==> m - n < &0`] THEN
        TRANS_TAC LET_TRANS `m_hi:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_ARITH `m:real < &0 ==> &2 * m < &0`] THEN
        ASM_SIMP_TAC[REAL_ARITH `m:real < &0 /\ &0 <= n ==> &0 <= n - m`] THEN
        TRANS_TAC REAL_LET_TRANS `&m_hi:real` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC];

      (*** Now the even-n / even_m case ***)

      CONJ_TAC THENL
       [ASM_REWRITE_TAC[GSYM INT_MUL_2; GSYM INT_MUL_ASSOC] THEN
        REWRITE_TAC[GSYM INT_SUB_LDISTRIB] THEN
        ABBREV_TAC `mi:int = &m_m * &m - &m_n * &n` THEN
        ABBREV_TAC `ni:int = &n_m * &m - &n_n * &n` THEN
        ONCE_REWRITE_TAC[INT_ARITH `e * &2 * x:int = &2 * e * x`] THEN
        FIRST_X_ASSUM(fun th ->
         GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `&2:int` o MATCH_MP (INTEGER_RULE
         `(w * m:int == e * n) (mod d)
          ==> !t. (t * e) divides d /\ w pow 2 = &1
                   ==> e divides m /\ (m == e * w * n) (mod (e * t))`))) THEN
        REWRITE_TAC[INT_POW_ONE; INT_ARITH `(--x:int) pow 2 = x pow 2`] THEN
        ONCE_REWRITE_TAC[MESON[INT_POW_POW; MULT_SYM]
         `(x:int) pow m pow n = x pow n pow m`] THEN
        REWRITE_TAC[INT_POW_ONE; INT_ARITH `(--x:int) pow 2 = x pow 2`] THEN
        ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP; GSYM(CONJUNCT2 INT_POW);
                     ARITH_RULE `i < 58 ==> SUC i <= 64`] THEN
        SIMP_TAC[IMP_CONJ; int_divides; LEFT_IMP_EXISTS_THM; INTEGER_RULE
         `(a * x == a * y) (mod (a * n)) <=>
          a:int = &0 \/ (x == y) (mod n)`] THEN
        REWRITE_TAC[INT_POW_EQ_0; ARITH_EQ; INT_OF_NUM_EQ] THEN
        X_GEN_TAC `md:int` THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
        X_GEN_TAC `nd:int` THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
        REWRITE_TAC[INT_ARITH `&2 * x * y:int = x * &2 * y`] THEN
        REWRITE_TAC[GSYM INT_ADD_LDISTRIB; INT_GCD_LMUL] THEN
        REWRITE_TAC[INT_ARITH `&2 * x * y:int = x * &2 * y`] THEN
        AP_TERM_TAC THEN REWRITE_TAC[GSYM INT_MUL_2] THEN
        W(MP_TAC o PART_MATCH (lhand o rand)
         INT_GCD_COPRIME_DIVIDES_RMUL o lhand o snd) THEN
        REWRITE_TAC[INT_ABS_NUM; INT_GCD_ADD] THEN
        REWRITE_TAC[INT_GCD_SYM] THEN DISCH_THEN MATCH_MP_TAC THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
           `(n:int == n') (mod t)
            ==> coprime(t,n') ==> coprime(t,n)`)) THEN
          REWRITE_TAC[INT_COPRIME_RMUL; INT_COPRIME_RPOW; INT_COPRIME_RNEG] THEN
          ASM_REWRITE_TAC[GSYM num_coprime; COPRIME_2; ARITH];
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
           `(m:int == m') (mod t)
            ==> t divides m' ==> t divides m`)) THEN
          ASM_REWRITE_TAC[INT_2_DIVIDES_ADD; INT_2_DIVIDES_MUL;
            INT_DIVIDES_RNEG;
            INT_2_DIVIDES_POW;GSYM num_divides; DIVIDES_2; ARITH] THEN
          ASM_REWRITE_TAC[GSYM NOT_ODD]];
        ALL_TAC] THEN

      EXISTS_TAC `q:num` THEN
      GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[INT_OF_NUM_MUL; DOUBLE_HALF; GSYM NOT_ODD] THEN
        ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INT_CONG_SYM])) THEN
        SPEC_TAC(`(&2:int) pow 64`,`mm:int`) THEN CONV_TAC INTEGER_RULE;
        ALL_TAC] THEN
      REWRITE_TAC[real_pow; REAL_ARITH `(a + a) * b:real = &2 * a * b`] THEN
      ASM_REWRITE_TAC[REAL_ARITH
       `s * (&2 * x - &2 * y):real = &2 * s * (x - y)`] THEN
      REWRITE_TAC[REAL_FIELD `(&2 * x) / (y * &2):real = x / y`] THEN
      ASM_REWRITE_TAC[GSYM ADD1] THEN REWRITE_TAC[ADD1] THEN

      GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_ARITH
         `--(e / &2):real <= x - y <=> --e <= &2 * x - &2 * y`] THEN
        REWRITE_TAC[REAL_ARITH
         `x - y:real <= e / &2 <=> &2 * x - &2 * y <= e`] THEN
        REWRITE_TAC[REAL_FIELD `&2 * x / (y * &2):real = x / y`] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `mhi - m:real <= u
         ==> mm <= mhi /\ mhi <= mm + &1 /\ --l <= mhi - m /\
             &0 <= l /\ &0 <= u
          ==> --(l + u + &1) <= mm - m /\ mm - m <= l + u`)) THEN
        ASM_SIMP_TAC[LT_IMP_LE] THEN
        MP_TAC(ARITH_RULE
         `0 <= m_hi MOD 2 /\ m_hi MOD 2 <= 1`) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN

      CONJ_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `--(lowerr:num->real) i` THEN
        ASM_SIMP_TAC[LT_IMP_LE];
        ALL_TAC] THEN

      CONJ_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `(upperr:num->real) i` THEN
        ASM_SIMP_TAC[LT_IMP_LE];
        ALL_TAC] THEN

      (*** The big-small invariant ***)

      CONJ_TAC THENL
       [DISCH_THEN(fun th ->
          FIRST_X_ASSUM(MP_TAC o C MP th) THEN ASSUME_TAC th) THEN
        ASM_REWRITE_TAC[ARITH_RULE `i <= 57 <=> i < 58`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
         [CONJ_TAC THENL
           [REWRITE_TAC[REAL_ARITH
             `a * abs(&2 * b):real <= (e * &2) * c <=>
              a * abs b <= e * c`] THEN
            ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          REWRITE_TAC[ARITH_RULE `i + 1 < 58 <=> i <= 56`] THEN DISCH_TAC THEN
          CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
          DISJ1_TAC THEN CONJ_TAC THENL
           [MATCH_MP_TAC(ARITH_RULE `m < n ==> m DIV 2 < n`) THEN
            ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC(ARITH_RULE `m < n ==> m DIV 2 < n`) THEN
            ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          CONJ_TAC THENL
           [TRANS_TAC LE_TRANS `2 EXP i * (n_hi + 31)` THEN
            ASM_REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC[REAL_FIELD `m / (n * &2):real = m / n / &2`] THEN
          REWRITE_TAC[REAL_ARITH `x:real <= y / &2 <=> &2 * x <= y`] THEN
          REWRITE_TAC[REAL_ARITH `y / &2 <= x <=> y:real <= &2 * x`] THEN
          CONJ_TAC THENL
           [TRANS_TAC REAL_LE_TRANS `&m_hi:real` THEN ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
            TRANS_TAC REAL_LE_TRANS `&m_hi + &1:real` THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC];
          CONJ_TAC THENL
           [REWRITE_TAC[REAL_ARITH
             `a * abs(&2 * b):real <= (e * &2) * c <=>
              a * abs b <= e * c`] THEN
            ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          REWRITE_TAC[ARITH_RULE `i + 1 < 58 <=> i <= 56`] THEN DISCH_TAC THEN
          CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
          DISJ2_TAC THEN CONJ_TAC THENL
           [TRANS_TAC LTE_TRANS `2 EXP 5` THEN ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC(ARITH_RULE
             `2 EXP 63 <= 2 EXP 56 * (m + 31) ==> 2 EXP 5 <= m DIV 2`) THEN
            TRANS_TAC LE_TRANS `2 EXP i * (m_hi + 31)` THEN
            ASM_REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN ARITH_TAC;
            TRANS_TAC LE_TRANS `2 EXP i * (m_hi + 31)` THEN
            ASM_REWRITE_TAC[EXP_ADD; GSYM MULT_ASSOC; EXP_1] THEN
            REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0] THEN ARITH_TAC]];
        ALL_TAC] THEN

      (*** The main invariant with case splits ***)

      FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [DISJ1_TAC THEN ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL] THEN
        ASM_REWRITE_TAC[REAL_ARITH
         `m * &2 * n:real <= (e * &2) * a <=> m * n <= e * a`] THEN
        ASM_SIMP_TAC[REAL_ARITH
         `&0 <= m /\ &0 <= n /\ min m n:real <= a * b
          ==> min m (&2 * n) <= (a * &2) * b`];

        DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL] THEN
        TRANS_TAC LET_TRANS `m_hi:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;

        DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[REAL_ARITH `&2 * n:real < &0 <=> n < &0`] THEN
        TRANS_TAC REAL_LET_TRANS `&m_hi:real` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC]];

    (*** This is now the trivial loop-back thing ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[TAUT `p \/ q \/ r <=> ~p /\ ~q ==> r`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TAUT `~p /\ ~q ==> r <=> p \/ q \/ r`]) THEN
    REWRITE_TAC[TAUT `~p /\ ~q ==> r <=> p \/ q \/ r`] THEN
    X86_STEPS_TAC BIGNUM_COPRIME_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    ALL_TAC] THEN

  (*** Now manually massage the final invariant into what we really want ***)

  GHOST_INTRO_TAC `m_m:num` `\s. val(read R10 s)` THEN
  GHOST_INTRO_TAC `m_n:num` `\s. val(read R11 s)` THEN
  GHOST_INTRO_TAC `n_m:num` `\s. val(read RCX s)` THEN
  GHOST_INTRO_TAC `n_n:num` `\s. val(read RDX s)` THEN
  GHOST_INTRO_TAC `m_hi:num` `\s. val(read R12 s)` THEN
  GHOST_INTRO_TAC `n_hi:num` `\s. val(read RBP s)` THEN
  GHOST_INTRO_TAC `m_lo:num` `\s. val(read RDI s)` THEN
  GHOST_INTRO_TAC `n_lo:num` `\s. val(read RSI s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN

  MAP_EVERY ABBREV_TAC
   [`m':int = &m_m * &m - &m_n * &n`;
    `n':int = &n_m * &m - &n_n * &n`] THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x205`
   `\s. read RSP s = stackpointer /\
        read (memory :> bytes64(word_add stackpointer (word 40))) s = evenor /\
        read R8 s = mm /\
        read R15 s = nn /\
        read R14 s = word k /\
        read (memory :> bytes64(word_add stackpointer (word 32))) s = word t /\
        read R13 s = word l /\
        bignum_from_memory (mm,l) s = m /\
        bignum_from_memory (nn,l) s = n /\
        bignum_from_memory (mm,k) s = m0 /\
        bignum_from_memory (nn,k) s = n0 /\
        read (memory :> bytes64 stackpointer) s = word m_m /\
        read (memory :> bytes64(word_add stackpointer (word 8))) s =
        word m_n /\
        read (memory :> bytes64(word_add stackpointer (word 16))) s =
        word n_m /\
        read (memory :> bytes64(word_add stackpointer (word 24))) s =
        word n_n /\
        m_m + m_n <= 2 EXP 58 /\
        n_m + n_n <= 2 EXP 58 /\
        (ODD a \/ ODD b
         ==> &2 pow 58 divides m' /\
             &2 pow 58 divides n' /\
             ~(&2 pow 59 divides n') /\
             gcd(m',n') = &2 pow 58 * gcd(&m,&n) /\
             abs m' * abs n':int <= &2 pow 58 * &m * &n)` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[TAUT `p \/ q \/ r <=> ~p /\ ~q ==> r`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TAUT `~p /\ ~q ==> r <=> p \/ q \/ r`]) THEN
    REWRITE_TAC[TAUT `~p /\ ~q ==> r <=> p \/ q \/ r`] THEN
    X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num` MP_TAC) THEN

    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC(INTEGER_RULE
       `coprime(w:int,d) /\ d divides e
        ==> (w * m == d * n) (mod e) ==> d divides m`) THEN
      REWRITE_TAC[INT_COPRIME_LPOW; INT_COPRIME_LNEG; INT_COPRIME_1] THEN
      MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
      ALL_TAC] THEN

    GEN_REWRITE_TAC RAND_CONV [CONJ_ASSOC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
       [MATCH_MP_TAC(INTEGER_RULE
         `coprime(w:int,d) /\ d divides e
          ==> (w * m == d * n) (mod e) ==> d divides m`) THEN
        REWRITE_TAC[INT_COPRIME_LPOW; INT_COPRIME_LNEG; INT_COPRIME_1] THEN
        MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;

        REWRITE_TAC[TAUT `p ==> ~q <=> ~(p /\ q)`] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
         `(w * m == d * n) (mod e) /\ p divides m
          ==> coprime(w:int,d) /\ p divides e ==> p divides d * n`)) THEN
        REWRITE_TAC[INT_COPRIME_LPOW; INT_COPRIME_LNEG; INT_COPRIME_1] THEN
        SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH] THEN
        REWRITE_TAC[INT_ARITH `&2 pow 59 = (&2:int) pow 58 * &2`] THEN
        ASM_SIMP_TAC[INT_DIVIDES_LMUL2_EQ; INT_POW_EQ_0; INT_OF_NUM_EQ;
                     ARITH_EQ; GSYM num_divides; NOT_EVEN; DIVIDES_2]];
      ALL_TAC] THEN

    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["m'"; "n'"] THEN
    REWRITE_TAC[int_le; int_abs_th; int_mul_th; int_pow_th;
                int_sub_th; int_of_num_th] THEN
    MAP_EVERY ABBREV_TAC
    [`mr:real = &m_m * &m - &m_n * &n`;
     `nr:real = &n_m * &m - &n_n * &n`] THEN

    REWRITE_TAC[ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NEG] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LID; REAL_POW_ONE] THEN
    ASM_CASES_TAC `min (&m) (&n) < &2 zpow base * &2 pow 5` THEN
    ASM_SIMP_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN

    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [REWRITE_TAC[IMP_CONJ] THEN
      REPLICATE_TAC 2 (DISCH_THEN(SUBST1_TAC o MATCH_MP
        (REAL_ARITH `&0:real <= x ==> x = abs x`))) THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_POW;
                  REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID];
      DISCH_TAC] THEN

    SUBGOAL_THEN `&m * &n:real = min (&m) (&n) * max (&m) (&n)`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_min; real_max] THEN MESON_TAC[REAL_MUL_SYM];
      ALL_TAC] THEN

    TRANS_TAC REAL_LE_TRANS
     `&2 pow 58 * min (&m) (&n) *
                  (&2 pow 63 * &2 zpow base)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC]) THEN
      ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(SYM(ASSUME
       `&(MAX (bitsize m) (bitsize n)) - &64:int = base`)) THEN
      REWRITE_TAC[GSYM BITSIZE_MAX] THEN
      SIMP_TAC[REAL_ZPOW_SUB; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[REAL_ZPOW_NUM; REAL_ARITH
       `&2 pow 63 * (x:real) / &2 pow 64 <= a <=> x <= &2 * a`] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC BITSIZE_REV_ALT THEN
      REWRITE_TAC[ARITH_RULE `MAX m n = 0 <=> m = 0 /\ n = 0`] THEN
      STRIP_TAC THEN
      UNDISCH_TAC `&2 zpow base * &2 pow 5 <= min (&m) (&n)` THEN
      ASM_REWRITE_TAC[REAL_NOT_LE] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_ARITH `&0 < (x:real) * &32 <=> &0 < x`] THEN
      MATCH_MP_TAC REAL_ZPOW_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV] THEN

    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [TRANS_TAC REAL_LE_TRANS
       `(&16 * &2 zpow (base + &58)) * abs nr:real` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
         `x:real < &0 ==> abs x = --x`)) THEN
        REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_POW;
                    REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
        DISCH_THEN SUBST1_TAC THEN
        SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_ZPOW_LT;
                 REAL_OF_NUM_LT; ARITH] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `m - m' / z:real <= u
          ==> &0 <= m /\ m < &16 /\ u < &16 /\ m' < &0
              ==> --m' / z <= &16`)) THEN
        ASM_SIMP_TAC[REAL_OF_NUM_LT; REAL_POS; LE_REFL];
        SIMP_TAC[REAL_ZPOW_ADD; REAL_OF_NUM_EQ; ARITH_EQ] THEN
        REWRITE_TAC[REAL_ZPOW_NUM; REAL_ARITH
         `(&16 * b * &2 pow 58) * x:real <= &2 pow 58 * y * &2 pow 63 * b <=>
          b * x <= b * &2 pow 59 * y`] THEN
        SIMP_TAC[REAL_LE_LMUL_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT; ARITH] THEN
        MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
        EXISTS_TAC `inv(&2 zpow (base + &58))` THEN
        SIMP_TAC[REAL_LT_INV_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT; ARITH] THEN
        REWRITE_TAC[GSYM real_div] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
         `&0:real <= x ==> abs x = x`)) THEN
        REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_POW;
                    REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
        DISCH_THEN SUBST1_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `--l:real <= m - m'
          ==> l < &16 /\ &16 + m <= e
              ==> m' <= e`)) THEN
        ASM_SIMP_TAC[LE_REFL; REAL_ZPOW_ADD; REAL_OF_NUM_EQ; ARITH_EQ] THEN
        REWRITE_TAC[REAL_ZPOW_NUM; REAL_FIELD
         `(&2 pow 59 * x) / (y * &2 pow 58) = &2 * x / y`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `n:real < x + &16 /\ &32 <= x ==> &16 + n <= &2 * x`) THEN
        ASM_REWRITE_TAC[] THEN
        SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT; ARITH] THEN
        ASM_REWRITE_TAC[REAL_ARITH `&32 * x:real = x * &2 pow 5`]];

      (*** Symmetrical-ish; just one mul other way round ***)

      TRANS_TAC REAL_LE_TRANS
       `abs mr * (&16 * &2 zpow (base + &58)):real` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
         `x:real < &0 ==> abs x = --x`)) THEN
        REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_POW;
                    REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
        DISCH_THEN SUBST1_TAC THEN
        SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_ZPOW_LT;
                 REAL_OF_NUM_LT; ARITH] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `m - m' / z:real <= u
          ==> &0 <= m /\ m < &16 /\ u < &16 /\ m' < &0
              ==> --m' / z <= &16`)) THEN
        ASM_SIMP_TAC[REAL_OF_NUM_LT; REAL_POS; LE_REFL];
        SIMP_TAC[REAL_ZPOW_ADD; REAL_OF_NUM_EQ; ARITH_EQ] THEN
        REWRITE_TAC[REAL_ZPOW_NUM; REAL_ARITH
         `x * (&16 * b * &2 pow 58):real <= &2 pow 58 * y * &2 pow 63 * b <=>
          b * x <= b * &2 pow 59 * y`] THEN
        SIMP_TAC[REAL_LE_LMUL_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT; ARITH] THEN
        MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
        EXISTS_TAC `inv(&2 zpow (base + &58))` THEN
        SIMP_TAC[REAL_LT_INV_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT; ARITH] THEN
        REWRITE_TAC[GSYM real_div] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
         `&0:real <= x ==> abs x = x`)) THEN
        REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_POW;
                    REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
        DISCH_THEN SUBST1_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `--l:real <= m - m'
          ==> l < &16 /\ &16 + m <= e
              ==> m' <= e`)) THEN
        ASM_SIMP_TAC[LE_REFL; REAL_ZPOW_ADD; REAL_OF_NUM_EQ; ARITH_EQ] THEN
        REWRITE_TAC[REAL_ZPOW_NUM; REAL_FIELD
         `(&2 pow 59 * x) / (y * &2 pow 58) = &2 * x / y`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `n:real < x + &16 /\ &32 <= x ==> &16 + n <= &2 * x`) THEN
        ASM_REWRITE_TAC[] THEN
        SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ZPOW_LT; REAL_OF_NUM_LT; ARITH] THEN
        ASM_REWRITE_TAC[REAL_ARITH `&32 * x:real = x * &2 pow 5`]]];
    ALL_TAC] THEN

  (*** A little bit more cleaning up ***)

  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `lowerr:num->real` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `upperr:num->real` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `base:int` o concl))) THEN

  (*** Cross-multiplication "crossloop" and duplex negation "optnegloop" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2c4`
   `\s. read RSP s = stackpointer /\
        read (memory :> bytes64 (word_add stackpointer (word 40))) s =
        evenor /\
        read R8 s = mm /\
        read R15 s = nn /\
        read R14 s = word k /\
        read (memory :> bytes64 (word_add stackpointer (word 32))) s =
        word t /\
        read R13 s = word l /\
        bignum_from_memory (word_add mm (word (8 * l)),k - l) s =
        highdigits m0 l /\
        bignum_from_memory (word_add nn (word (8 * l)),k - l) s =
        highdigits n0 l /\
        &2 pow (64 * l) * &(val(read RDI s)) +
        &(bignum_from_memory (mm,l) s):int = abs m' /\
        &2 pow (64 * l) * &(val(read RSI s)) +
        &(bignum_from_memory (nn,l) s):int = abs n'` THEN
  CONJ_TAC THENL
   [
    (*** The cross-multiplications loop updating m and n ***)

    ENSURES_WHILE_UP_TAC `l:num` `pc + 0x214` `pc + 0x278`
     `\i s. read RSP s = stackpointer /\
            read (memory :> bytes64(word_add stackpointer (word 40))) s =
            evenor /\
            read R8 s = mm /\
            read R15 s = nn /\
            read R14 s = word k /\
            read (memory :> bytes64(word_add stackpointer (word 32))) s =
            word t /\
            read R13 s = word l /\
            read R9 s = word i /\
            read (memory :> bytes64 stackpointer) s = word m_m /\
            read (memory :> bytes64(word_add stackpointer (word 8))) s =
            word m_n /\
            read (memory :> bytes64(word_add stackpointer (word 16))) s =
            word n_m /\
            read (memory :> bytes64(word_add stackpointer (word 24))) s =
            word n_n /\
            bignum_from_memory(word_add mm (word(8 * l)),k - l) s =
            highdigits m0 l /\
            bignum_from_memory(word_add nn (word(8 * l)),k - l) s =
            highdigits n0 l /\
            bignum_from_memory(word_add mm (word(8 * i)),l - i) s =
            highdigits m i /\
            bignum_from_memory(word_add nn (word(8 * i)),l - i) s =
            highdigits n i /\
            val(word_neg(read R12 s)) <= 1 /\
            val(word_neg(read RBP s)) <= 1 /\
            &2 pow (64 * i) *
            (&(val(read RDI s)) - &2 pow 64 * &(val(word_neg(read R12 s)))) +
            &(bignum_from_memory(mm,i) s):real =
            &m_m * &(lowdigits m i) - &m_n * &(lowdigits n i) /\
            &2 pow (64 * i) *
            (&(val(read RSI s)) - &2 pow 64 * &(val(word_neg(read RBP s)))) +
            &(bignum_from_memory(nn,i) s):real =
            &n_m * &(lowdigits m i) - &n_n * &(lowdigits n i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--5) THEN
      REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; LE_0] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[VAL_WORD_0; SUB_0; MULT_CLAUSES; WORD_ADD_0] THEN
      REWRITE_TAC[LOWDIGITS_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[GSYM HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_REFL];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      GHOST_INTRO_TAC `h1:num` `\s. val(read RDI s)` THEN
      GHOST_INTRO_TAC `h2:num` `\s. val(read RSI s)` THEN
      GHOST_INTRO_TAC `c1:num` `\s. val(word_neg(read R12 s))` THEN
      GHOST_INTRO_TAC `c2:num` `\s. val(word_neg(read RBP s))` THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `b1:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[VAL_EQ_BITVAL] THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `b2:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[VAL_EQ_BITVAL] THEN
      REWRITE_TAC[REAL_ARITH
       `&2 pow e * c + x:real = y <=> x = y - &2 pow e * c`] THEN
      MP_TAC(GEN `x:int64` (ISPECL [`x:int64`; `l - i:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `l - i = 0 <=> ~(i < l)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `l - i - 1 = l - (i + 1)`] THEN
      ABBREV_TAC `mm':int64 = word_add mm (word (8 * l))` THEN
      ABBREV_TAC `nn':int64 = word_add nn (word (8 * l))` THEN
      SUBGOAL_THEN
       `nonoverlapping (mm':int64,8 * (k - l)) (mm,8 * l) /\
        nonoverlapping (nn':int64,8 * (k - l)) (mm,8 * l) /\
        nonoverlapping (mm':int64,8 * (k - l)) (nn,8 * l) /\
        nonoverlapping (nn':int64,8 * (k - l)) (nn,8 * l)`
      MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
       [MAP_EVERY EXPAND_TAC ["mm'"; "nn'"] THEN
        REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; STRIP_TAC] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_COPRIME_EXEC [3;4;5;8;9;10;14] (1--15) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_sub x (word_neg y):int64 = word_add x y`]) THEN
      ACCUMULATE_ARITH_TAC "s15" THEN
      X86_ACCSTEPS_TAC BIGNUM_COPRIME_EXEC [16;17;22] (16--23) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_sub x (word_neg y):int64 = word_add x y`]) THEN
      ACCUMULATE_ARITH_TAC "s23" THEN
      X86_ACCSTEPS_TAC BIGNUM_COPRIME_EXEC [24;25] (24--29) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_UNMASK_64; WORD_NEG_NEG; VAL_WORD_BITVAL] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_CLAUSES] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL] THEN
      REWRITE_TAC[WORD_ADD; REAL_OF_NUM_LE; BITVAL_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; REAL_POW_ADD] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[BITVAL_POS] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      CONV_TAC REAL_RING;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2);

      ALL_TAC] THEN

    (*** A little bit more cleanup ***)

    SUBGOAL_THEN `m < 2 EXP (64 * l) /\ n < 2 EXP (64 * l)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[LOWDIGITS_BOUND];
      ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

    (*** Clean signs and the duplex optional negation loop "optnegloop" ***)

    ABBREV_TAC `sgn1 <=> m':int < &0` THEN
    GHOST_INTRO_TAC `m1:num` `bignum_from_memory (mm,l)` THEN
    BIGNUM_TERMRANGE_TAC `l:num` `m1:num` THEN
    GHOST_INTRO_TAC `h1:int64` `read RDI` THEN
    GHOST_INTRO_TAC `cv1:num` `\s. val(word_neg (read R12 s))` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    SUBGOAL_THEN `cv1 = bitval sgn1` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `b1:bool` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[EQ_BITVAL] THEN MAP_EVERY EXPAND_TAC ["sgn1"; "m'"] THEN
      REWRITE_TAC[INT_ARITH `x - y:int < &0 <=> x < y`] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
      EXISTS_TAC `64 * (l + 1)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      UNDISCH_THEN
       `&2 pow (64 * l) * (&(val(h1:int64)) -
        &2 pow 64 * &(bitval b1)) + &m1:real =
        &m_m * &m - &m_n * &n` (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[ARITH_RULE `64 * (l + 1) = 64 * l + 64`; REAL_POW_ADD] THEN
      REWRITE_TAC[REAL_ARITH
       `(ee * e) * c + ee * (s - e * c) + z:real = ee * s + z`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0:real <= ee * s /\ &0 <= z /\ z < ee /\ ee * (s + &1) <= ee * e
        ==> &0 <= ee * s + z /\ ee * s + z < ee * e`) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
      ASM_REWRITE_TAC[VAL_BOUND_64; ARITH_RULE `s + 1 <= e <=> s < e`];
      ALL_TAC] THEN

    ABBREV_TAC `sgn2 <=> n':int < &0` THEN
    GHOST_INTRO_TAC `n1:num` `bignum_from_memory (nn,l)` THEN
    BIGNUM_TERMRANGE_TAC `l:num` `n1:num` THEN
    GHOST_INTRO_TAC `h2:int64` `read RSI` THEN
    GHOST_INTRO_TAC `cv2:num` `\s. val(word_neg (read RBP s))` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    SUBGOAL_THEN `cv2 = bitval sgn2` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `b2:bool` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[EQ_BITVAL] THEN MAP_EVERY EXPAND_TAC ["sgn2"; "n'"] THEN
      REWRITE_TAC[INT_ARITH `x - y:int < &0 <=> x < y`] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
      EXISTS_TAC `64 * (l + 1)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      UNDISCH_THEN
       `&2 pow (64 * l) * (&(val(h2:int64)) -
        &2 pow 64 * &(bitval b2)) + &n1:real =
        &n_m * &m - &n_n * &n` (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[ARITH_RULE `64 * (l + 1) = 64 * l + 64`; REAL_POW_ADD] THEN
      REWRITE_TAC[REAL_ARITH
       `(ee * e) * c + ee * (s - e * c) + z:real = ee * s + z`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0:real <= ee * s /\ &0 <= z /\ z < ee /\ ee * (s + &1) <= ee * e
        ==> &0 <= ee * s + z /\ ee * s + z < ee * e`) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
      ASM_REWRITE_TAC[VAL_BOUND_64; ARITH_RULE `s + 1 <= e <=> s < e`];
      ALL_TAC] THEN

    ENSURES_WHILE_UP_TAC `l:num` `pc + 0x28c` `pc + 0x2b9`
     `\i s. read RSP s = stackpointer /\
            read (memory :> bytes64 (word_add stackpointer (word 40))) s =
            evenor /\
            read R8 s = mm /\
            read R15 s = nn /\
            read R14 s = word k /\
            read (memory :> bytes64 (word_add stackpointer (word 32))) s =
            word t /\
            read R13 s = word l /\
            read R9 s = word i /\
            bignum_from_memory (word_add mm (word (8 * l)),k - l) s =
            highdigits m0 l /\
            bignum_from_memory (word_add nn (word (8 * l)),k - l) s =
            highdigits n0 l /\
            bignum_from_memory (word_add mm (word (8 * i)),l - i) s =
            highdigits m1 i /\
            bignum_from_memory (word_add nn (word (8 * i)),l - i) s =
            highdigits n1 i /\
            read R12 s = word_neg(word(bitval sgn1)) /\
            read RBP s = word_neg(word(bitval sgn2)) /\
            val(word_neg(read R10 s)) <= 1 /\
            2 EXP (64 * i) * val(word_neg(read R10 s)) +
            bignum_from_memory(mm,i) s =
            (if sgn1 then 2 EXP (64 * i) - lowdigits m1 i
             else lowdigits m1 i) /\
            val(word_neg(read R11 s)) <= 1 /\
            2 EXP (64 * i) * val(word_neg(read R11 s)) +
            bignum_from_memory(nn,i) s =
            (if sgn2 then 2 EXP (64 * i) - lowdigits n1 i
             else lowdigits n1 i) /\
            read RDI s = (if sgn1 then word_not h1 else h1) /\
            read RSI s = (if sgn2 then word_not h2 else h2)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[VAL_EQ_BITVAL; WORD_RULE
       `word_neg x:int64 = y <=> x = word_neg y`] THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--7) THEN
      REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL; LOWDIGITS_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; ADD_CLAUSES] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; WORD_ADD_0; BITVAL_BOUND] THEN
      ASM_REWRITE_TAC[WORD_XOR_MASK; HIGHDIGITS_0; EXP; SUB_0] THEN
      REWRITE_TAC[MULT_CLAUSES; bitval];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      MP_TAC(GEN `x:int64` (ISPECL [`x:int64`; `l - i:num`]
        BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `l - i = 0 <=> ~(i < l)`] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      GHOST_INTRO_TAC `c1:num` `\s. val(word_neg(read R10 s))` THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `b1:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      GHOST_INTRO_TAC `c2:num` `\s. val(word_neg(read R11 s))` THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `b2:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ABBREV_TAC `mm':int64 = word_add mm (word (8 * l))` THEN
      ABBREV_TAC `nn':int64 = word_add nn (word (8 * l))` THEN
      SUBGOAL_THEN
       `nonoverlapping (mm':int64,8 * (k - l))
                       (word_add mm (word (8 * i)),8 * 1) /\
        nonoverlapping (mm':int64,8 * (k - l))
                       (word_add nn (word (8 * i)),8 * 1) /\
        nonoverlapping (nn':int64,8 * (k - l))
                       (word_add mm (word (8 * i)),8 * 1) /\
        nonoverlapping (nn':int64,8 * (k - l))
                       (word_add nn (word (8 * i)),8 * 1)`
      MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
       [REPEAT CONJ_TAC THEN MAP_EVERY EXPAND_TAC ["mm'"; "nn'"] THEN
        (SUBGOAL_THEN `8 * l = 8 * i + 8 * (l - i)` SUBST1_TAC THENL
          [UNDISCH_TAC `i:num < l` THEN ARITH_TAC; NONOVERLAPPING_TAC]);
        STRIP_TAC] THEN
      X86_ACCSTEPS_TAC BIGNUM_COPRIME_EXEC [4;10] (1--13) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND; WORD_ADD] THEN
      CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUM_RING
       `c + z:num = w ==> a + w + b = c + d ==> a + z + b = d`)) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      SIMP_TAC[GSYM REAL_OF_NUM_SUB; LOWDIGITS_BOUND; LT_IMP_LE] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; BITVAL_CLAUSES; WORD_NEG_0; WORD_NEG_1;
                  WORD_XOR_NOT; WORD_XOR_0; WORD_NEG_EQ_0;
                  WORD_BITVAL_EQ_0] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; REAL_POW_ADD;
                  GSYM REAL_OF_NUM_CLAUSES; REAL_VAL_WORD_NOT] THEN
      SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
      CONV_TAC REAL_RING;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC (1--2);

      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
      GHOST_INTRO_TAC `hv1:num` `\s. val(word_neg (read R10 s))` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `hb1:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      GHOST_INTRO_TAC `hv2:num` `\s. val(word_neg (read R11 s))` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `hb2:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[VAL_EQ_BITVAL; WORD_RULE
       `word_neg x:int64 = y <=> x = word_neg y`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_COPRIME_EXEC [3;4] (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["m'"; "n'"] THEN REWRITE_TAC[int_eq] THEN
      REWRITE_TAC[int_add_th; int_mul_th; int_abs_th; int_sub_th;
                  int_pow_th; int_of_num_th] THEN
      CONJ_TAC THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`64 * (l + 1)`; `&0:real`] THEN
      REWRITE_TAC[REAL_ABS_POS; INTEGER_CLOSED] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; REAL_POW_ADD] THEN
      (CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN MATCH_MP_TAC(ARITH_RULE
        `z < ee /\ ee * (s + 1) <= ee * e ==> ee * s + z < ee * e`) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LE_MULT_LCANCEL] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND; EXP_EQ_0; ARITH_EQ] THEN
        REWRITE_TAC[VAL_BOUND_64; ARITH_RULE `n + 1 <= e <=> n < e`];
        ALL_TAC] THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC(REAL_ARITH
          `&0 <= a /\ a < e * ee /\ &0 <= b /\ b < e * ee
           ==> abs(a - b:real) < ee * e`) THEN
         REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
         CONJ_TAC THEN MATCH_MP_TAC LT_MULT2 THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       SUBGOAL_THEN
        `abs(&m_m * &m - &m_n * &n):real =
         (if sgn1 then --(&m_m * &m - &m_n * &n) else &m_m * &m - &m_n * &n) /\
         abs(&n_m * &m - &n_n * &n):real =
         (if sgn2 then --(&n_m * &m - &n_n * &n) else &n_m * &m - &n_n * &n)`
       (CONJUNCTS_THEN SUBST1_TAC) THENL
        [MAP_EVERY EXPAND_TAC ["sgn1"; "sgn2"; "m'"; "n'"] THEN
         REWRITE_TAC[int_lt; int_sub_th; int_mul_th; int_of_num_th] THEN
         REAL_ARITH_TAC;
         ALL_TAC]) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
       REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
        `&2 pow (64 * l) * (b - c) + z:real = w
         ==> w = &2 pow (64 * l) * (b - c) + z`))) THEN
       REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
        `&2 pow (64 * l) * b + z:real = w
         ==> z = w - &2 pow (64 * l) * b`))) THEN
       ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
       DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
       COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
       REWRITE_TAC[BITVAL_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
       REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64; REAL_ADD_RID] THEN
       REWRITE_TAC[real_div; REAL_INV_MUL] THEN
       ONCE_REWRITE_TAC[REAL_ARITH `x * y * inv z:real = (x * inv z) * y`] THEN
       CONV_TAC(RAND_CONV(LAND_CONV REAL_POLY_CONV)) THEN
       REWRITE_TAC[REAL_MUL_ASSOC; REAL_FIELD
        `(x * &2 pow n + y * &2 pow n) * inv(&2 pow n):real = x + y`] THEN
       REAL_INTEGER_TAC];
     ALL_TAC] THEN

  (*** The shift-right-by-58-bits duplex loop "shiftloop" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2f6`
   `\s. read RSP s = stackpointer /\
        read (memory :> bytes64 (word_add stackpointer (word 40))) s =
        evenor /\
        read R8 s = mm /\
        read R15 s = nn /\
        read R14 s = word k /\
        read (memory :> bytes64 (word_add stackpointer (word 32))) s =
        word t /\
        read R13 s = word l /\
        bignum_from_memory (word_add mm (word (8 * l)),k - l) s =
        highdigits m0 l /\
        bignum_from_memory (word_add nn (word (8 * l)),k - l) s =
        highdigits n0 l /\
        &(bignum_from_memory (mm,l) s):int = abs m' div &2 pow 58 /\
        &(bignum_from_memory (nn,l) s):int = abs n' div &2 pow 58` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `m2:num` `bignum_from_memory (mm,l)` THEN
    GHOST_INTRO_TAC `n2:num` `bignum_from_memory (nn,l)` THEN
    MAP_EVERY (BIGNUM_TERMRANGE_TAC `l:num`) [`m2:num`; `n2:num`] THEN
    GHOST_INTRO_TAC `mh:num` `\s. val(read RDI s)` THEN
    GHOST_INTRO_TAC `nh:num` `\s. val(read RSI s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    ABBREV_TAC `m3 = 2 EXP (64 * l) * mh + m2` THEN
    ABBREV_TAC `n3 = 2 EXP (64 * l) * nh + n2` THEN

    ENSURES_WHILE_PDOWN_TAC `l:num` `pc + 0x2c7` `pc + 0x2f4`
     `\i s. (read RSP s = stackpointer /\
             read (memory :> bytes64 (word_add stackpointer (word 40))) s =
             evenor /\
             read R8 s = mm /\
             read R15 s = nn /\
             read R14 s = word k /\
             read (memory :> bytes64 (word_add stackpointer (word 32))) s =
             word t /\
             read R13 s = word l /\
             bignum_from_memory (word_add mm (word (8 * l)),k - l) s =
             highdigits m0 l /\
             bignum_from_memory (word_add nn (word (8 * l)),k - l) s =
             highdigits n0 l /\
             read R9 s = word i /\
             read RDI s = word(bigdigit m3 i) /\
             read RSI s = word(bigdigit n3 i) /\
             bignum_from_memory(mm,i) s = lowdigits m3 i /\
             bignum_from_memory(nn,i) s = lowdigits n3 i /\
             bignum_from_memory(word_add mm (word (8 * i)),l - i) s =
             highdigits (m3 DIV 2 EXP 58) i /\
             bignum_from_memory(word_add nn (word (8 * i)),l - i) s =
             highdigits (n3 DIV 2 EXP 58) i) /\
            (read ZF s <=> i = 0)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_COPRIME_EXEC [1] THEN
      MAP_EVERY EXPAND_TAC ["m3"; "n3"] THEN
      REWRITE_TAC[lowdigits; bigdigit; MOD_MULT_ADD] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      ASM_SIMP_TAC[DIV_LT; MOD_LT; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[ADD_CLAUSES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
      REWRITE_TAC[DIMINDEX_64; MOD_MOD_REFL] THEN
      CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC HIGHDIGITS_ZERO THEN
      SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      MAP_EVERY EXPAND_TAC ["m3"; "n3"] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_POW_ADD] THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["m'"; "n'"] THEN
      MATCH_MP_TAC(INT_ARITH
       `&0:int <= x /\ &0 <= y /\ x < e /\ y < e ==> abs(x - y) < e`) THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0] THEN CONJ_TAC THEN
      MATCH_MP_TAC(MESON[LET_TRANS]
       `x * y:num <= a * y /\ a * y < a * b ==> x * y < a * b`) THEN
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; LE_MULT_RCANCEL; EXP_EQ_0] THEN
      UNDISCH_THEN `lowdigits m0 l = m` (SUBST1_TAC o SYM) THEN
      UNDISCH_THEN `lowdigits n0 l = n` (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[LOWDIGITS_BOUND] THEN
      MAP_EVERY UNDISCH_TAC
       [`m_m + m_n <= 2 EXP 58`; `n_m + n_n <= 2 EXP 58`] THEN
      ARITH_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`i:num`; `i + 1`] THEN
      MP_TAC(SPEC `i:num` WORD_INDEX_WRAP) THEN DISCH_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ABBREV_TAC `mm':int64 = word_add mm (word (8 * l))` THEN
      ABBREV_TAC `nn':int64 = word_add nn (word (8 * l))` THEN
      SUBGOAL_THEN
       `nonoverlapping (mm':int64,8 * (k - l))
                       (word_add mm (word (8 * i)),8 * 1) /\
        nonoverlapping (mm':int64,8 * (k - l))
                       (word_add nn (word (8 * i)),8 * 1) /\
        nonoverlapping (nn':int64,8 * (k - l))
                       (word_add mm (word (8 * i)),8 * 1) /\
        nonoverlapping (nn':int64,8 * (k - l))
                       (word_add nn (word (8 * i)),8 * 1)`
      MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
       [REPEAT CONJ_TAC THEN MAP_EVERY EXPAND_TAC ["mm'"; "nn'"] THEN
        (SUBGOAL_THEN `8 * l = 8 * i + 8 * (l - i)` SUBST1_TAC THENL
          [UNDISCH_TAC `i:num < l` THEN ARITH_TAC; NONOVERLAPPING_TAC]);
        STRIP_TAC] THEN
      X86_STEPS_TAC BIGNUM_COPRIME_EXEC (1--11) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[WORD_RULE
       `word_sub (word (i + 1)) (word 1) = word i`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
      ASM_REWRITE_TAC[ARITH_RULE `l - i = 0 <=> ~(i < l)`] THEN
      ASM_REWRITE_TAC[ARITH_RULE `l - i - 1 = l - (i + 1)`] THEN
      REWRITE_TAC[WORD_RULE
       `word_add (word_add z (word (8 * i))) (word 8) =
        word_add z (word (8 * (i + 1)))`] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; DIMINDEX_64] THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; LE_REFL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [HIGHDIGITS_STEP] THEN
      REWRITE_TAC[ARITH_RULE `a + n:num = n + b <=> a = b`] THEN
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
      ARITH_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC [1];

      REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; SUB_0] THEN
      REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES] THEN
      X86_SIM_TAC BIGNUM_COPRIME_EXEC [1] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_DIV] THEN
      MAP_EVERY EXPAND_TAC ["m3"; "n3"] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN

  (*** The grand finale, justifying the use of l-sized computations ***)

  X86_SIM_TAC BIGNUM_COPRIME_EXEC [1] THEN CONJ_TAC THENL
   [DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o
        GEN_REWRITE_RULE I [IMP_CONJ_ALT])));
    VAL_INT64_TAC `t:num` THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REFL_TAC] THEN

  UNDISCH_TAC `ODD n0` THEN ASM_CASES_TAC `n0 = 0` THEN
  ASM_REWRITE_TAC[ODD] THEN REPEAT DISCH_TAC THEN
  UNDISCH_TAC `~(&2 pow 59 divides (n':int))` THEN
  ONCE_REWRITE_TAC[GSYM INT_DIVIDES_RABS] THEN
  UNDISCH_TAC `gcd(m':int,n'):int = &2 pow 58 * gcd(&m,&n)` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
   [MESON[INT_GCD_LABS; INT_GCD_RABS] `gcd(a,b):int = gcd(abs a,abs b)`] THEN
  MAP_EVERY UNDISCH_TAC
   [`abs m' * abs n':int <= &2 pow 58 * &m * &n`;
    `&(read(memory :> bytes(mm,8 * l)) s1) = abs m' div &2 pow 58`;
    `&(read(memory :> bytes(nn,8 * l)) s1) = abs n' div &2 pow 58`] THEN
  SUBGOAL_THEN `?m1. abs(m'):int = &2 pow 58 * &m1`
  (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `&2 pow 58 divides (m':int)` THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM INT_DIVIDES_RABS] THEN
    SPEC_TAC(`m':int`,`x:int`) THEN REWRITE_TAC[GSYM INT_FORALL_ABS] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_divides] THEN
    REWRITE_TAC[divides];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n1. abs(n'):int = &2 pow 58 * &n1`
  (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `&2 pow 58 divides (n':int)` THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM INT_DIVIDES_RABS] THEN
    SPEC_TAC(`n':int`,`x:int`) THEN REWRITE_TAC[GSYM INT_FORALL_ABS] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_divides] THEN
    REWRITE_TAC[divides];
    ALL_TAC] THEN
  REWRITE_TAC[INT_GCD_LMUL; INT_ABS_POW; INT_ABS_NUM] THEN
  ONCE_REWRITE_TAC[INT_ARITH `(&2:int) pow 59 = &2 pow 58 * &2`] THEN
  SIMP_TAC[INT_DIVIDES_LMUL2_EQ; INT_EQ_MUL_LCANCEL; INT_LE_LMUL_EQ;
           GSYM INT_MUL_ASSOC;  INT_LT_POW2; INT_DIV_MUL; INT_POW_EQ_0;
           INT_OF_NUM_EQ; ARITH_EQ; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[DIVIDES_2; INT_OF_NUM_CLAUSES; NOT_EVEN;
              GSYM num_divides; GSYM NUM_GCD] THEN
  REPEAT DISCH_TAC THEN

  MP_TAC(GEN `x:int64` (ISPECL [`x:int64`; `l:num`; `k - l:num`]
        BIGNUM_FROM_MEMORY_SPLIT)) THEN
  ASM_SIMP_TAC[ARITH_RULE `l:num <= k ==> l + k - l = k`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ASM_SIMP_TAC[HIGHDIGITS_ZERO; ADD_CLAUSES; MULT_CLAUSES] THEN
  UNDISCH_TAC `lowdigits m0 l = m` THEN
  ASM_SIMP_TAC[LOWDIGITS_SELF] THEN DISCH_THEN SUBST_ALL_TAC THEN

  UNDISCH_TAC `~(m = 0) ==> n0 < 2 EXP (64 * l)` THEN
  REWRITE_TAC[TAUT `~p ==> q <=> q \/ p`] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `lowdigits n0 l = n` THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `m1 * 2 EXP 58 * n1 <= e ==> e < 2 EXP 58 * d ==> m1 * n1 < d`)) THEN
    TRANS_TAC LTE_TRANS `2 EXP t` THEN
    ASM_REWRITE_TAC[GSYM EXP_ADD; LE_EXP] THEN ARITH_TAC;
    ALL_TAC] THEN

  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `m1 * 2 EXP 58 * n1 <= 0 * n ==> m1 * n1 = 0`)) THEN
  ASM_REWRITE_TAC[MULT_EQ_0] THEN UNDISCH_TAC `ODD n1` THEN
  ASM_CASES_TAC `n1 = 0` THEN ASM_REWRITE_TAC[ODD] THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[ODD_ADD; ODD_MULT; ODD_EXP; MULT_CLAUSES; EXP_LT_0;
                  MULT_EQ_0; ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY UNDISCH_TAC [`gcd(0,n0) = gcd(a,b)`; `gcd(0,n1) = gcd(0,n)`] THEN
  REWRITE_TAC[GCD_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_THEN `lowdigits n0 l = n` (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[HIGH_LOW_DIGITS]);;

let BIGNUM_COPRIME_NOIBT_SUBROUTINE_CORRECT = prove
 (`!m x a n y b w pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 96),104)
                       (w,8 * 2 * MAX (val m) (val n)) /\
        ALLPAIRS nonoverlapping
         [(w,8 * 2 * MAX (val m) (val n));
          (word_sub stackpointer (word 96),96)]
         [(word pc,LENGTH bignum_coprime_tmc); (x,8 * val m); (y,8 * val n)] /\
        val m < 2 EXP 57 /\ val n < 2 EXP 57
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_coprime_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [m;x;n;y;w] s /\
                  bignum_from_memory(x,val m) s = a /\
                  bignum_from_memory(y,val n) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = if coprime(a,b) then word 1 else word 0)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(w,2 * MAX (val m) (val n));
                       memory :> bytes(word_sub stackpointer (word 96),96)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_coprime_tmc BIGNUM_COPRIME_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 96);;

let BIGNUM_COPRIME_SUBROUTINE_CORRECT = prove
 (`!m x a n y b w pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 96),104)
                       (w,8 * 2 * MAX (val m) (val n)) /\
        ALLPAIRS nonoverlapping
         [(w,8 * 2 * MAX (val m) (val n));
          (word_sub stackpointer (word 96),96)]
         [(word pc,LENGTH bignum_coprime_mc); (x,8 * val m); (y,8 * val n)] /\
        val m < 2 EXP 57 /\ val n < 2 EXP 57
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_coprime_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [m;x;n;y;w] s /\
                  bignum_from_memory(x,val m) s = a /\
                  bignum_from_memory(y,val n) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = if coprime(a,b) then word 1 else word 0)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(w,2 * MAX (val m) (val n));
                       memory :> bytes(word_sub stackpointer (word 96),96)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_COPRIME_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_coprime_windows_mc = define_from_elf
   "bignum_coprime_windows_mc" "x86/generic/bignum_coprime.obj";;

let bignum_coprime_windows_tmc = define_trimmed "bignum_coprime_windows_tmc" bignum_coprime_windows_mc;;

let BIGNUM_COPRIME_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!m x a n y b w pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 112),120)
                       (w,8 * 2 * MAX (val m) (val n)) /\
        ALLPAIRS nonoverlapping
         [(w,8 * 2 * MAX (val m) (val n));
          (word_sub stackpointer (word 112),112)]
         [(word pc,LENGTH bignum_coprime_windows_tmc); (x,8 * val m); (y,8 * val n)] /\
        val m < 2 EXP 57 /\ val n < 2 EXP 57
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_coprime_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [m;x;n;y;w] s /\
                  bignum_from_memory(x,val m) s = a /\
                  bignum_from_memory(y,val n) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  WINDOWS_C_RETURN s = if coprime(a,b) then word 1 else word 0)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(w,2 * MAX (val m) (val n));
                       memory :> bytes(word_sub stackpointer (word 112),112)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_coprime_windows_tmc bignum_coprime_tmc
    BIGNUM_COPRIME_CORRECT `[RBX; RBP; R12; R13; R14; R15]` 96);;

let BIGNUM_COPRIME_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!m x a n y b w pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 112),120)
                       (w,8 * 2 * MAX (val m) (val n)) /\
        ALLPAIRS nonoverlapping
         [(w,8 * 2 * MAX (val m) (val n));
          (word_sub stackpointer (word 112),112)]
         [(word pc,LENGTH bignum_coprime_windows_mc); (x,8 * val m); (y,8 * val n)] /\
        val m < 2 EXP 57 /\ val n < 2 EXP 57
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_coprime_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [m;x;n;y;w] s /\
                  bignum_from_memory(x,val m) s = a /\
                  bignum_from_memory(y,val n) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  WINDOWS_C_RETURN s = if coprime(a,b) then word 1 else word 0)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(w,2 * MAX (val m) (val n));
                       memory :> bytes(word_sub stackpointer (word 112),112)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_COPRIME_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

