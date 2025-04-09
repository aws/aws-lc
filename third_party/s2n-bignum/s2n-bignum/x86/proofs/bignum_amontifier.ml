(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Almost-Montgomerifier computation.                                        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_amontifier.o";;
 ****)

let bignum_amontifier_mc =
  define_assert_from_elf "bignum_amontifier_mc" "x86/generic/bignum_amontifier.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x89; 0xcd;        (* MOV (% r13) (% rcx) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x0f; 0x84; 0x0b; 0x03; 0x00; 0x00;
                           (* JE (Imm32 (word 779)) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x49; 0x8b; 0x0c; 0xdc;  (* MOV (% rcx) (Memop Quadword (%%% (r12,3,rbx))) *)
  0x49; 0x89; 0x4c; 0xdd; 0x00;
                           (* MOV (Memop Quadword (%%% (r13,3,rbx))) (% rcx) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x48; 0x39; 0xfb;        (* CMP (% rbx) (% rdi) *)
  0x72; 0xef;              (* JB (Imm8 (word 239)) *)
  0x48; 0x89; 0xfb;        (* MOV (% rbx) (% rdi) *)
  0x48; 0xff; 0xcb;        (* DEC (% rbx) *)
  0x74; 0x2c;              (* JE (Imm8 (word 44)) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x49; 0x89; 0xfb;        (* MOV (% r11) (% rdi) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x49; 0x8b; 0x44; 0xed; 0x00;
                           (* MOV (% rax) (Memop Quadword (%%% (r13,3,rbp))) *)
  0x48; 0x0f; 0x42; 0xc8;  (* CMOVB (% rcx) (% rax) *)
  0x49; 0x89; 0x4c; 0xed; 0x00;
                           (* MOV (Memop Quadword (%%% (r13,3,rbp))) (% rcx) *)
  0x48; 0xff; 0xc5;        (* INC (% rbp) *)
  0x49; 0xff; 0xcb;        (* DEC (% r11) *)
  0x75; 0xe7;              (* JNE (Imm8 (word 231)) *)
  0x48; 0xff; 0xcb;        (* DEC (% rbx) *)
  0x75; 0xd4;              (* JNE (Imm8 (word 212)) *)
  0x48; 0x0f; 0xbd; 0xc9;  (* BSR (% rcx) (% rcx) *)
  0x48; 0x83; 0xf1; 0x3f;  (* XOR (% rcx) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x49; 0x8b; 0x44; 0xdd; 0x00;
                           (* MOV (% rax) (Memop Quadword (%%% (r13,3,rbx))) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x4c; 0x0f; 0xa5; 0xc8;  (* SHLD (% rax) (% r9) (% cl) *)
  0x49; 0x89; 0x44; 0xdd; 0x00;
                           (* MOV (Memop Quadword (%%% (r13,3,rbx))) (% rax) *)
  0x49; 0x89; 0xe9;        (* MOV (% r9) (% rbp) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x48; 0x39; 0xfb;        (* CMP (% rbx) (% rdi) *)
  0x72; 0xe4;              (* JB (Imm8 (word 228)) *)
  0x4d; 0x8b; 0x5c; 0xfd; 0xf8;
                           (* MOV (% r11) (Memop Quadword (%%%% (r13,3,rdi,-- &8))) *)
  0x41; 0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 1)) *)
  0x4d; 0x89; 0xd9;        (* MOV (% r9) (% r11) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0xbb; 0x3e; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 62)) *)
  0x4d; 0x01; 0xc0;        (* ADD (% r8) (% r8) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x49; 0x39; 0xc1;        (* CMP (% r9) (% rax) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4c; 0x21; 0xd8;        (* AND (% rax) (% r11) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x48; 0xff; 0xcb;        (* DEC (% rbx) *)
  0x75; 0xdd;              (* JNE (Imm8 (word 221)) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x4d; 0x39; 0xcb;        (* CMP (% r11) (% r9) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x49; 0x8b; 0x44; 0xdd; 0x00;
                           (* MOV (% rax) (Memop Quadword (%%% (r13,3,rbx))) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x04; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,rbx))) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x48; 0x39; 0xfb;        (* CMP (% rbx) (% rdi) *)
  0x72; 0xe2;              (* JB (Imm8 (word 226)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x40;
                           (* MOV (% rax) (Imm64 (word 4611686018427387904)) *)
  0x48; 0x29; 0xc1;        (* SUB (% rcx) (% rax) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x49; 0xf7; 0xd0;        (* NOT (% r8) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x49; 0x8b; 0x44; 0xdd; 0x00;
                           (* MOV (% rax) (Memop Quadword (%%% (r13,3,rbx))) *)
  0x4c; 0x21; 0xc0;        (* AND (% rax) (% r8) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x48; 0x1b; 0x04; 0xde;  (* SBB (% rax) (Memop Quadword (%%% (rsi,3,rbx))) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x89; 0x04; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,rbx))) (% rax) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x48; 0x39; 0xfb;        (* CMP (% rbx) (% rdi) *)
  0x72; 0xe2;              (* JB (Imm8 (word 226)) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0x8b; 0x04; 0xee;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,rbp))) *)
  0x48; 0x0f; 0xac; 0xc1; 0x3f;
                           (* SHRD (% rcx) (% rax) (Imm8 (word 63)) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x49; 0x1b; 0x4c; 0xed; 0x00;
                           (* SBB (% rcx) (Memop Quadword (%%% (r13,3,rbp))) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x89; 0x0c; 0xee;  (* MOV (Memop Quadword (%%% (rsi,3,rbp))) (% rcx) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0xff; 0xc5;        (* INC (% rbp) *)
  0x48; 0x39; 0xfd;        (* CMP (% rbp) (% rdi) *)
  0x72; 0xdd;              (* JB (Imm8 (word 221)) *)
  0x48; 0xc1; 0xe9; 0x3f;  (* SHR (% rcx) (Imm8 (word 63)) *)
  0x4c; 0x01; 0xc9;        (* ADD (% rcx) (% r9) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x49; 0x8b; 0x44; 0xed; 0x00;
                           (* MOV (% rax) (Memop Quadword (%%% (r13,3,rbp))) *)
  0x48; 0x21; 0xc8;        (* AND (% rax) (% rcx) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x48; 0x13; 0x04; 0xee;  (* ADC (% rax) (Memop Quadword (%%% (rsi,3,rbp))) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x89; 0x04; 0xee;  (* MOV (Memop Quadword (%%% (rsi,3,rbp))) (% rax) *)
  0x48; 0xff; 0xc5;        (* INC (% rbp) *)
  0x48; 0x39; 0xfd;        (* CMP (% rbp) (% rdi) *)
  0x72; 0xe2;              (* JB (Imm8 (word 226)) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0x8b; 0x04; 0xee;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,rbp))) *)
  0x48; 0x0f; 0xac; 0xc1; 0x3f;
                           (* SHRD (% rcx) (% rax) (Imm8 (word 63)) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x49; 0x1b; 0x4c; 0xed; 0x00;
                           (* SBB (% rcx) (Memop Quadword (%%% (r13,3,rbp))) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x89; 0x0c; 0xee;  (* MOV (Memop Quadword (%%% (rsi,3,rbp))) (% rcx) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0xff; 0xc5;        (* INC (% rbp) *)
  0x48; 0x39; 0xfd;        (* CMP (% rbp) (% rdi) *)
  0x72; 0xdd;              (* JB (Imm8 (word 221)) *)
  0x48; 0xc1; 0xe9; 0x3f;  (* SHR (% rcx) (Imm8 (word 63)) *)
  0x4c; 0x01; 0xc9;        (* ADD (% rcx) (% r9) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x49; 0x8b; 0x44; 0xed; 0x00;
                           (* MOV (% rax) (Memop Quadword (%%% (r13,3,rbp))) *)
  0x48; 0x21; 0xc8;        (* AND (% rax) (% rcx) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x48; 0x13; 0x04; 0xee;  (* ADC (% rax) (Memop Quadword (%%% (rsi,3,rbp))) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x89; 0x04; 0xee;  (* MOV (Memop Quadword (%%% (rsi,3,rbp))) (% rax) *)
  0x49; 0x89; 0x44; 0xed; 0x00;
                           (* MOV (Memop Quadword (%%% (r13,3,rbp))) (% rax) *)
  0x48; 0xff; 0xc5;        (* INC (% rbp) *)
  0x48; 0x39; 0xfd;        (* CMP (% rbp) (% rdi) *)
  0x72; 0xdd;              (* JB (Imm8 (word 221)) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x89; 0xfb;        (* MOV (% rbx) (% rdi) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x49; 0x89; 0xf8;        (* MOV (% r8) (% rdi) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x4c; 0x11; 0xc9;        (* ADC (% rcx) (% r9) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x04; 0xee;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,rbp))) *)
  0x49; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% r11) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x4d; 0x8b; 0x4c; 0xed; 0x00;
                           (* MOV (% r9) (Memop Quadword (%%% (r13,3,rbp))) *)
  0x49; 0x89; 0x44; 0xed; 0x00;
                           (* MOV (Memop Quadword (%%% (r13,3,rbp))) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xff; 0xc5;        (* INC (% rbp) *)
  0x49; 0xff; 0xc8;        (* DEC (% r8) *)
  0x75; 0xd8;              (* JNE (Imm8 (word 216)) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x4d; 0x89; 0xcb;        (* MOV (% r11) (% r9) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x8b; 0x44; 0xed; 0x00;
                           (* MOV (% rax) (Memop Quadword (%%% (r13,3,rbp))) *)
  0x4c; 0x8b; 0x0c; 0xee;  (* MOV (% r9) (Memop Quadword (%%% (rsi,3,rbp))) *)
  0x4d; 0x21; 0xd1;        (* AND (% r9) (% r10) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x4c; 0x11; 0xc8;        (* ADC (% rax) (% r9) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x49; 0x89; 0x44; 0xed; 0x00;
                           (* MOV (Memop Quadword (%%% (r13,3,rbp))) (% rax) *)
  0x48; 0xff; 0xc5;        (* INC (% rbp) *)
  0x48; 0x39; 0xfd;        (* CMP (% rbp) (% rdi) *)
  0x72; 0xde;              (* JB (Imm8 (word 222)) *)
  0x49; 0x29; 0xcb;        (* SUB (% r11) (% rcx) *)
  0x48; 0xff; 0xcb;        (* DEC (% rbx) *)
  0x75; 0x93;              (* JNE (Imm8 (word 147)) *)
  0x49; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (r12,0))) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x48; 0xc1; 0xe1; 0x02;  (* SHL (% rcx) (Imm8 (word 2)) *)
  0x49; 0x29; 0xc9;        (* SUB (% r9) (% rcx) *)
  0x49; 0x83; 0xf1; 0x02;  (* XOR (% r9) (Imm8 (word 2)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0x0f; 0xaf; 0xc8;  (* IMUL (% rcx) (% rax) *)
  0xb8; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 2)) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x48; 0x83; 0xc1; 0x01;  (* ADD (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x0f; 0xaf; 0xc8;  (* IMUL (% r9) (% rax) *)
  0x48; 0x0f; 0xaf; 0xc9;  (* IMUL (% rcx) (% rcx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x4c; 0x0f; 0xaf; 0xc8;  (* IMUL (% r9) (% rax) *)
  0x48; 0x0f; 0xaf; 0xc9;  (* IMUL (% rcx) (% rcx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x4c; 0x0f; 0xaf; 0xc8;  (* IMUL (% r9) (% rax) *)
  0x48; 0x0f; 0xaf; 0xc9;  (* IMUL (% rcx) (% rcx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x4c; 0x0f; 0xaf; 0xc8;  (* IMUL (% r9) (% rax) *)
  0x49; 0x8b; 0x4d; 0x00;  (* MOV (% rcx) (Memop Quadword (%% (r13,0))) *)
  0x4c; 0x0f; 0xaf; 0xc9;  (* IMUL (% r9) (% rcx) *)
  0x49; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (r12,0))) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0xbd; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ebp) (Imm32 (word 1)) *)
  0x49; 0x89; 0xf8;        (* MOV (% r8) (% rdi) *)
  0x49; 0xff; 0xc8;        (* DEC (% r8) *)
  0x74; 0x25;              (* JE (Imm8 (word 37)) *)
  0x49; 0x13; 0x4c; 0xed; 0x00;
                           (* ADC (% rcx) (Memop Quadword (%%% (r13,3,rbp))) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x49; 0x8b; 0x04; 0xec;  (* MOV (% rax) (Memop Quadword (%%% (r12,3,rbp))) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x49; 0x89; 0x44; 0xed; 0xf8;
                           (* MOV (Memop Quadword (%%%% (r13,3,rbp,-- &8))) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xff; 0xc5;        (* INC (% rbp) *)
  0x49; 0xff; 0xc8;        (* DEC (% r8) *)
  0x75; 0xdb;              (* JNE (Imm8 (word 219)) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x4d; 0x89; 0x5c; 0xfd; 0xf8;
                           (* MOV (Memop Quadword (%%%% (r13,3,rdi,-- &8))) (% r11) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x8b; 0x44; 0xed; 0x00;
                           (* MOV (% rax) (Memop Quadword (%%% (r13,3,rbp))) *)
  0x4d; 0x8b; 0x0c; 0xec;  (* MOV (% r9) (Memop Quadword (%%% (r12,3,rbp))) *)
  0x4d; 0x21; 0xd1;        (* AND (% r9) (% r10) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x4c; 0x19; 0xc8;        (* SBB (% rax) (% r9) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x89; 0x04; 0xee;  (* MOV (Memop Quadword (%%% (rsi,3,rbp))) (% rax) *)
  0x48; 0xff; 0xc5;        (* INC (% rbp) *)
  0x48; 0x39; 0xfd;        (* CMP (% rbp) (% rdi) *)
  0x72; 0xdf;              (* JB (Imm8 (word 223)) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0xc3                     (* RET *)
];;

let bignum_amontifier_tmc = define_trimmed "bignum_amontifier_tmc" bignum_amontifier_mc;;

let BIGNUM_AMONTIFIER_EXEC = X86_MK_CORE_EXEC_RULE bignum_amontifier_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** This actually works mod 32 but if anything this is more convenient ***)

let WORD_NEGMODINV_SEED_LEMMA_16 = prove
 (`!a x:int64.
        ODD a /\
        word_xor (word_sub (word a) (word_shl (word a) 2)) (word 2) = x
        ==> (a * val x + 1 == 0) (mod 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONG; MOD_0] THEN
  TRANS_TAC EQ_TRANS
   `(val(word a:int64) MOD 16 * val(x:int64) MOD 16 + 1) MOD 16` THEN
  REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`] THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    REWRITE_TAC[VAL_MOD; NUMSEG_LT; ARITH_EQ; ARITH]] THEN
  SUBGOAL_THEN `bit 0 (word a:int64)` MP_TAC THENL
   [ASM_REWRITE_TAC[BIT_LSB_WORD];
    EXPAND_TAC "x" THEN POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 1 (word a:int64)`;`bit 2 (word a:int64)`;`bit 3 (word a:int64)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** This is for the rather specific remainder computation below ***)

let remalemma = prove
 (`!x n q b.
        (x <= q * n <=> b) /\ ~(n divides x) /\ abs(&x - &q * &n:real) <= &n
        ==> &(x MOD n):real = &(bitval b) * &n + &x - &q * &n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM int_of_num_th; GSYM int_sub_th; GSYM int_add_th;
              GSYM int_mul_th; GSYM int_add_th; GSYM int_abs_th] THEN
  REWRITE_TAC[GSYM int_le; GSYM int_eq] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; num_divides] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_MUL] THEN
  ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  STRIP_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THENL
   [EXISTS_TAC `&q - &1:int`; EXISTS_TAC `&q:int`] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[INT_ABS_NUM; INT_MUL_LZERO; INT_MUL_LID; INT_ADD_LID] THEN
  REWRITE_TAC[INT_ARITH `n + x - qn:int < n <=> x < qn`] THEN
  REWRITE_TAC[INT_ARITH `x - q * n:int < n <=> x < (q + &1) * n`] THEN
  REWRITE_TAC[INT_LT_LE] THEN
  (CONJ_TAC THENL [ASM_INT_ARITH_TAC; DISCH_TAC]) THEN
  UNDISCH_TAC `~((&n:int) divides (&x))` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INTEGER_RULE);;

let BIGNUM_AMONTIFIER_CORRECT = time prove
 (`!k z m t n pc.
        nonoverlapping (z,8 * val k) (t,8 * val k) /\
        ALLPAIRS nonoverlapping [(z,8 * val k); (t,8 * val k)]
                                [(word pc,0x327); (m,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_amontifier_tmc) /\
                  read RIP s = word(pc + 0x6) /\
                  C_ARGUMENTS [k; z; m; t] s /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = word(pc + 0x320) /\
                  (ODD n
                   ==> (bignum_from_memory (z,val k) s ==
                        2 EXP (128 * val k)) (mod n)))
             (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RBP;
                         R8; R9; R10; R11; R12; R13] ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                         memory :> bytes(t,8 * val k)] ,,
              MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `mm:int64`; `t:int64`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `m:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ODD];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_1)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Initial copying into temporary buffer, "copyinloop" ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x18` `pc + 0x24`
   `\i s. (read RDI s = word k /\
           read RSI s = z /\
           read R12 s = mm /\
           read R13 s = t /\
           bignum_from_memory(mm,k) s = m /\
           read RBX s = word i /\
           bignum_from_memory(word_add mm (word(8 * i)),k - i) s =
           highdigits m i /\
           bignum_from_memory(t,i) s = lowdigits m i) /\
          (read RCX s = word(bigdigit m (i - 1)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--5) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; HIGHDIGITS_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[LOWDIGITS_CLAUSES; ADD_SUB] THEN ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2);
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** The digitwise normalization "normloop" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x5d`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R12 s = mm /\
        read R13 s = t /\
        bignum_from_memory(mm,k) s = m /\
        m divides bignum_from_memory(t,k) s /\
        read RCX s = word(bigdigit (bignum_from_memory(t,k) s) (k - 1)) /\
        (~(m = 0) ==> 2 EXP (64 * (k - 1)) <= bignum_from_memory(t,k) s)` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--5) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF; DIVIDES_REFL; SUB_REFL] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP (64 * 0) <= m <=> ~(m = 0)`];
      ALL_TAC] THEN

    MP_TAC(ARITH_RULE `k - 1 = 0 <=> k = 0 \/ k = 1`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    ENSURES_WHILE_PUP_TAC `k - 1` `pc + 0x31` `pc + 0x5b`
     `\i s. (read RDI s = word k /\
             read RSI s = z /\
             read R12 s = mm /\
             read R13 s = t /\
             bignum_from_memory(mm,k) s = m /\
             read RBX s = word(k - 1 - i) /\
             read RCX s = word(bigdigit (bignum_from_memory(t,k) s) (k - 1)) /\
             m divides bignum_from_memory(t,k) s /\
             (~(m = 0) ==> 2 EXP (64 * i) <= bignum_from_memory(t,k) s)) /\
            (read ZF s <=> i = k - 1)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`word k:int64`; `word 1:int64`] VAL_WORD_SUB_CASES) THEN
      ASM_SIMP_TAC[VAL_WORD_1; LE_1] THEN DISCH_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SUB_0] THEN
      ASM_SIMP_TAC[DIVIDES_REFL; WORD_SUB; LE_1] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP (64 * 0) <= m <=> ~(m = 0)`];
      ALL_TAC; (*** Do the main loop invariant below ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1];
      X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1]] THEN

    (*** Nested loop "shufloop" ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `n:num` `bignum_from_memory (t,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    ABBREV_TAC `topz <=> bigdigit n (k - 1) = 0` THEN

    ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x3f` `pc + 0x56`
     `\j s. (read RDI s = word k /\
             read RSI s = z /\
             read R12 s = mm /\
             read R13 s = t /\
             bignum_from_memory (mm,k) s = m /\
             read RBX s = word (k - 1 - i) /\
             read RBP s = word j /\
             read R11 s = word(k - j) /\
             read RAX s =
             (if j = 0 then word 0 else word(bigdigit n (j - 1))) /\
             (read CF s <=> ~topz) /\
             bignum_from_memory(word_add t (word(8 * j)),k - j) s =
             highdigits n j /\
             bignum_from_memory(t,j) s =
             lowdigits (if topz then 2 EXP 64 * n else n) j) /\
            (read RCX s =
             word(bigdigit (bignum_from_memory(t,j) s) (j - 1)) /\
             (read ZF s <=> j = k))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--4) THEN
      REWRITE_TAC[VAL_EQ_0; WORD_NEG_EQ_0] THEN
      ASM_SIMP_TAC[WORD_EQ_0; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_0; HIGHDIGITS_0; SUB_0] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
      ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[COND_SWAP; GSYM WORD_ADD];

      ALL_TAC; (*** Inner loop invariant below ***)

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1] THEN
      VAL_INT64_TAC `k - 1` THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> s) /\ q /\ r ==> p /\ q /\ r /\ s`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `a - (i + 1) = a - i - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < k - 1 ==> 1 <= k - 1 - i`];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [DISCH_THEN SUBST1_TAC THEN
        W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o
          lhand o lhand o snd) THEN
        REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THENL
         [ALL_TAC; DISCH_THEN SUBST1_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`k < 2 EXP 64`; `i < k - 1`] THEN ARITH_TAC;
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) LOWDIGITS_SELF o
        rand o lhand o snd) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "topz" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `n = lowdigits n ((k - 1) + 1)` SUBST1_TAC THENL
         [ASM_SIMP_TAC[SUB_ADD; LE_1; LOWDIGITS_SELF];
          ASM_REWRITE_TAC[LOWDIGITS_CLAUSES; ADD_CLAUSES; MULT_CLAUSES]] THEN
        SUBGOAL_THEN `64 * k = 64 + 64 * (k - 1)` SUBST1_TAC THENL
         [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; REWRITE_TAC[EXP_ADD]] THEN
        SIMP_TAC[LT_MULT_LCANCEL; LOWDIGITS_BOUND; EXP_EQ_0; ARITH_EQ];
        DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_SIMP_TAC[DIVIDES_LMUL; EXP_ADD; LE_MULT_LCANCEL; EXP_EQ_0;
                     ARITH_EQ; ARITH_RULE `64 * (i + 1) = 64 + 64 * i`];
        DISCH_TAC THEN TRANS_TAC LE_TRANS `2 EXP (64 * (k - 1))`] THEN
      ASM_SIMP_TAC[LE_EXP; ARITH_EQ; ARITH_RULE
        `i < k - 1 ==> 64 * (i + 1) <= 64 * (k - 1)`] THEN
      SUBGOAL_THEN `n = lowdigits n ((k - 1) + 1)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[SUB_ADD; LE_1; LOWDIGITS_SELF];
        ASM_REWRITE_TAC[LOWDIGITS_CLAUSES; ADD_CLAUSES; MULT_CLAUSES]] THEN
      MATCH_MP_TAC(ARITH_RULE `e * 1 <= e * d ==> e <= e * d + c`) THEN
      ASM_SIMP_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; LE_1]] THEN

    X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ADD_SUB; GSYM WORD_ADD; ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `j < j + 1`] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `a - (i + 1) = a - i - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `j < k ==> 1 <= k - j`];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ASSOC]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM CONJ_ASSOC];
      W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o
        lhand o lhand o snd) THEN
      REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THENL
       [ALL_TAC; DISCH_THEN SUBST1_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`k < 2 EXP 64`; `j:num < k`] THEN
      ARITH_TAC] THEN
    UNDISCH_THEN `bigdigit n (k - 1) = 0 <=> topz` (SUBST_ALL_TAC o SYM) THEN
    ASM_CASES_TAC `bigdigit n (k - 1) = 0` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LOWDIGITS_CLAUSES; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THENL
     [ALL_TAC; ARITH_TAC] THEN
    ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; EXP] THEN
    REWRITE_TAC[LOWDIGITS_0; VAL_WORD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[REWRITE_RULE[lowdigits] (GSYM LOWDIGITS_1)] THEN
    REWRITE_TAC[MULT_CLAUSES; MOD_MULT] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    MATCH_MP_TAC(NUM_RING `x:num = y ==> a + e * x = e * y + a`) THEN
    SUBGOAL_THEN `j = SUC(j - 1)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
    THENL [UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[bigdigit; EXP_ADD; ARITH_RULE `64 * SUC j = 64 + 64 * j`] THEN
    SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ];

    ALL_TAC] THEN

  (*** Bitwise stage of normalization ***)

  ENSURES_SEQUENCE_TAC `pc + 0x87`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R12 s = mm /\
        read R13 s = t /\
        bignum_from_memory(mm,k) s = m /\
        m divides bignum_from_memory(t,k) s /\
        (~(m = 0) ==> 2 EXP (64 * k - 1) <= bignum_from_memory(t,k) s)` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `n:num` `bignum_from_memory (t,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN GLOBALIZE_PRECONDITION_TAC THEN

    (*** The shift to apply which we accept a priori for the next loop ***)

    ENSURES_SEQUENCE_TAC `pc + 0x65`
     `\s. read RDI s = word k /\
          read RSI s = z /\
          read R12 s = mm /\
          read R13 s = t /\
          bignum_from_memory (mm,k) s = m /\
          bignum_from_memory (t,k) s = n /\
          (~(bigdigit n (k - 1) = 0)
           ==> val(read RCX s) = 64 - bitsize(bigdigit n (k - 1)))` THEN
    CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      SIMP_TAC[GSYM VAL_EQ_0; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      DISCH_TAC THEN REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      CONV_TAC WORD_REDUCE_CONV THEN ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN
      SUBST1_TAC(ARITH_RULE `63 = 2 EXP 6 - 1`) THEN
      W(MP_TAC o PART_MATCH (rand o rand)
        WORD_SUB_MASK_WORD o lhand o snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC VAL_WORD_LT THEN ARITH_TAC;
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_SUB] THEN
      REWRITE_TAC[BITSIZE_LE; BIGDIGIT_BOUND] THEN
      MP_TAC(ISPEC `word (bigdigit n (k - 1)):int64` WORD_CLZ_LT_DIMINDEX) THEN
      ASM_SIMP_TAC[WORD_EQ_0; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      SIMP_TAC[ARITH_RULE `i <= 63 <=> i < 64`] THEN DISCH_THEN(K ALL_TAC) THEN
      SIMP_TAC[WORD_CLZ_BITSIZE; WORD_SUB; DIMINDEX_64; BITSIZE_LE; VAL_WORD_LT;
               BIGDIGIT_BOUND; VAL_WORD_EQ] THEN
      CONV_TAC WORD_RULE;
      GHOST_INTRO_TAC `c:num` `\s. val(read RCX s)` THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      GLOBALIZE_PRECONDITION_TAC] THEN

    (*** The "bitloop" loop ***)

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x6b` `pc + 0x82`
     `\i s. read RDI s = word k /\
            read RSI s = z /\
            read R12 s = mm /\
            read R13 s = t /\
            bignum_from_memory (mm,k) s = m /\
            read RCX s = word c /\
            read RBX s = word i /\
            bignum_from_memory(word_add t (word (8 * i)),k - i) s =
            highdigits n i /\
            2 EXP (64 * i) * val(read R9 s) DIV 2 EXP (64 - c MOD 64) +
            bignum_from_memory(t,i) s =
            2 EXP (c MOD 64) * lowdigits n i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[LOWDIGITS_0; DIV_0; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES;
                  WORD_ADD_0; HIGHDIGITS_0; SUB_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `b:int64` `read R9` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - i = 0 <=> ~(i < n)`] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--6) THEN
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
      X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2);

      GHOST_INTRO_TAC `b:int64` `read R9` THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
      X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2)] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `e * b + z = cn
      ==> (e * b < e * 1 ==> e * b = 0)
          ==> cn < e ==> z = cn`)) THEN
    ANTS_TAC THENL
     [SIMP_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; MULT_EQ_0] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES; EXP_LT_0; ARITH_EQ] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      ASM_REWRITE_TAC[CONJUNCT1 LE; EXP_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
     `m divides n ==> m = 0 ==> n = 0`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(m = 0) ==> 2 EXP (64 * (k - 1)) <= n` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_THEN
     `~(bigdigit n (k - 1) = 0) ==> c = 64 - bitsize (bigdigit n (k - 1))`
     (MP_TAC o CONV_RULE(RAND_CONV SYM_CONV)) THEN
    ASM_SIMP_TAC[GSYM HIGHDIGITS_TOP; HIGHDIGITS_EQ_0; NOT_LT] THEN
    ASM_SIMP_TAC[HIGHDIGITS_TOP] THEN DISCH_TAC THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `64 * k = c MOD 64 + (64 * k - c MOD 64)` SUBST1_TAC THENL
       [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
        REWRITE_TAC[EXP_ADD; LT_MULT_LCANCEL; ARITH_EQ; EXP_EQ_0]] THEN
      REWRITE_TAC[GSYM BITSIZE_LE] THEN
      SUBGOAL_THEN
       `n = 2 EXP (64 * (k - 1)) * highdigits n (k - 1) + lowdigits n (k - 1)`
      SUBST1_TAC THENL [REWRITE_TAC[HIGH_LOW_DIGITS]; ALL_TAC] THEN
      ASM_SIMP_TAC[HIGHDIGITS_TOP] THEN
      UNDISCH_THEN `64 - bitsize (bigdigit n (k - 1)) = c`
       (SUBST1_TAC o SYM) THEN
      ASM_CASES_TAC `bigdigit n (k - 1) = 0` THENL
       [ASM_REWRITE_TAC[BITSIZE_0; MULT_CLAUSES; ADD_CLAUSES] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITSIZE_LE; SUB_0] THEN
        TRANS_TAC LTE_TRANS `2 EXP (64 * (k - 1))` THEN
        ASM_REWRITE_TAC[LOWDIGITS_BOUND; LE_EXP; ARITH_EQ] THEN ARITH_TAC;
        ASM_SIMP_TAC[BITSIZE_MULT_ADD; LOWDIGITS_BOUND]] THEN
      MATCH_MP_TAC(ARITH_RULE `a + c <= b ==> a <= b - c MOD 64`) THEN
      MATCH_MP_TAC(ARITH_RULE
       `~(k = 0) /\ b <= 64 ==> (64 * (k - 1) + b) + (64 - b) <= 64 * k`) THEN
      ASM_REWRITE_TAC[BITSIZE_LE; BIGDIGIT_BOUND];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[DIVIDES_LMUL] THEN
    SUBGOAL_THEN `64 * k - 1 = c MOD 64 + (64 * k - 1 - c MOD 64)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      REWRITE_TAC[EXP_ADD; LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]] THEN
    UNDISCH_TAC `2 EXP (64 * (k - 1)) <= n` THEN
    REWRITE_TAC[GSYM NOT_LT; GSYM BITSIZE_LE] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `~(b = 0) /\ a <= b + c ==> a - 1 - c < b`) THEN
    ASM_REWRITE_TAC[BITSIZE_EQ_0] THEN
    UNDISCH_THEN `64 - bitsize (bigdigit n (k - 1)) = c`
     (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM HIGHDIGITS_TOP; highdigits; BITSIZE_DIV] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `b < a ==> 64 - (a - b) < 64`] THEN
    UNDISCH_TAC `64 * (k - 1) < bitsize n` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Introduce the multiple n, and abbreviations for high and low parts ***)
  (*** Also blunt the hypothesis for consistency with other consequences  ***)

  GHOST_INTRO_TAC `n:num` `bignum_from_memory (t,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (MESON[ODD]
   `(~(m = 0) ==> p) ==> ODD m ==> p`)) THEN

  ABBREV_TAC `h = bigdigit n (k - 1)` THEN
  ABBREV_TAC `l = lowdigits n (k - 1)` THEN

  SUBGOAL_THEN
   `h < 2 EXP 64 /\ l < 2 EXP (64 * (k - 1)) /\
    2 EXP (64 * (k - 1)) * h + l = n /\
    (ODD m ==> 2 EXP 63 <= h)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_THEN `bigdigit n (k - 1) = h` (SUBST1_TAC o SYM) THEN
    UNDISCH_THEN `lowdigits n (k - 1) = l` (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LOWDIGITS_BOUND; BIGDIGIT_BOUND] THEN
    ASM_SIMP_TAC[GSYM HIGHDIGITS_TOP; HIGH_LOW_DIGITS] THEN
    SIMP_TAC[highdigits; LE_RDIV_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 64 * (k - 1) + 63 = 64 * k - 1`];
    ALL_TAC] THEN

  (**** The somewhat stupid quotient loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0xca`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R12 s = mm /\
        read R13 s = t /\
        bignum_from_memory (mm,k) s = m /\
        bignum_from_memory (t,k) s = n /\
        (ODD m ==> read R8 s = word(2 EXP 126 DIV h))` THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_PUP_TAC `62` `pc + 0x9d` `pc + 0xbe`
     `\i s. (read RDI s = word k /\
             read RSI s = z /\
             read R12 s = mm /\
             read R13 s = t /\
             bignum_from_memory (mm,k) s = m /\
             bignum_from_memory (t,k) s = n /\
             read R11 s = word h /\
             read RBX s = word(62 - i) /\
             val(read R8 s) < 2 EXP (i + 1) /\
             (ODD m
              ==> val(read R8 s) * h + val(read R9 s) = 2 EXP (64 + i) /\
                  val(read R9 s) <= h)) /\
            (read ZF s <=> i = 62)` THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC;

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      MP_TAC(ISPECL [`k:num`; `t:int64`; `s0:x86state`; `k - 1`]
         BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - 1 < k <=> ~(k = 0)`] THEN
      DISCH_THEN(MP_TAC o SYM) THEN
      GEN_REWRITE_TAC LAND_CONV [VAL_WORD_GALOIS] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC THEN
      MP_TAC(SPEC `k - 1` WORD_INDEX_WRAP) THEN
      ASM_SIMP_TAC[SUB_ADD; LE_1] THEN DISCH_TAC THEN
      VAL_INT64_TAC `k - 1` THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[VAL_WORD_1; EXP_1; ADD_CLAUSES; SUB_0; ARITH_RULE `1 < 2`] THEN
      DISCH_THEN(fun th -> REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MP th))) THEN
      REWRITE_TAC[WORD_SUB_LZERO; VAL_WORD_1; MULT_CLAUSES] THEN
      REWRITE_TAC[VAL_WORD_NEG_CASES; DIMINDEX_64] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC [`2 EXP 63 <= h`; `h < 2 EXP 64`] THEN ARITH_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `q:num` `\s. val(read R8 s)` THEN
      GHOST_INTRO_TAC `r:num` `\s. val(read R9 s)` THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--11) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `a - (i + 1) = a - i - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < k ==> 1 <= k - i`];
        DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; WORD_NOT_MASK;
                   ARITH_RULE `i < 62 ==> (62 - (i + 1) = 0 <=> i + 1 = 62)`;
                   ARITH_RULE `62 - i < 2 EXP 64`] THEN
      REWRITE_TAC[WORD_RULE `word_sub x (word_neg y) = word_add x y`] THEN
      REWRITE_TAC[NOT_LT; GSYM WORD_ADD] THEN CONJ_TAC THENL
       [MATCH_MP_TAC VAL_WORD_LT THEN ONCE_REWRITE_TAC[EXP_ADD] THEN
        MATCH_MP_TAC(ARITH_RULE
         `q < i /\ b <= 1 ==> (q + q) + b < i * 2 EXP 1`) THEN
        ASM_REWRITE_TAC[BITVAL_BOUND];
        DISCH_THEN(fun th ->
          REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th)))] THEN
      SUBST1_TAC(ISPECL
       [`word h:int64`; `word r:int64`] VAL_WORD_SUB_CASES) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
      ASM_SIMP_TAC[ARITH_RULE `r <= h ==> (h - r <= r <=> h <= 2 * r)`] THEN
      REWRITE_TAC[WORD_AND_MASK; GSYM MULT_2] THEN

      ASM_CASES_TAC `h <= 2 * r` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
      REWRITE_TAC[WORD_SUB_0; GSYM MULT_2] THENL
       [SUBGOAL_THEN
         `word_sub (word (2 * r)) (word h):int64 = word(2 * r - h)`
        SUBST1_TAC THENL [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
        SUBGOAL_THEN `2 * r - h < 2 EXP 64` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`r:num <= h`; `h < 2 EXP 64`] THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `2 * q + 1 < 2 EXP 64` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
           `q < 2 EXP (i + 1)
            ==> 2 EXP 1 * 2 EXP (i + 1) <= 2 EXP 64
                ==> 2 * q + 1 < 2 EXP 64`)) THEN
          REWRITE_TAC[GSYM EXP_ADD; LE_EXP; ARITH_EQ] THEN
          UNDISCH_TAC `i < 62` THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
        REWRITE_TAC[ADD_ASSOC] THEN ONCE_REWRITE_TAC[EXP_ADD] THEN
        SIMPLE_ARITH_TAC;

        RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
        ASM_SIMP_TAC[VAL_WORD_LE; LT_IMP_LE] THEN
        SUBGOAL_THEN `2 * r < 2 EXP 64` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`2 * r < h`; `h < 2 EXP 64`] THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `2 * q < 2 EXP 64` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
           `q < 2 EXP (i + 1)
            ==> 2 EXP 1 * 2 EXP (i + 1) <= 2 EXP 64
                ==> 2 * q  < 2 EXP 64`)) THEN
          REWRITE_TAC[GSYM EXP_ADD; LE_EXP; ARITH_EQ] THEN
          UNDISCH_TAC `i < 62` THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
        ASM_REWRITE_TAC[GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
        REWRITE_TAC[EXP_ADD] THEN ARITH_TAC];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1];

      GHOST_INTRO_TAC `q:num` `\s. val(read R8 s)` THEN
      GHOST_INTRO_TAC `r:num` `\s. val(read R9 s)` THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--4) THEN
      DISCH_THEN(fun th ->
        REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th))) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; GSYM WORD_ADD] THEN
      SUBGOAL_THEN `r < 2 EXP 64 /\ h < 2 EXP 64` STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `r:num <= h /\ h < e ==> r < e /\ h < e`) THEN
        ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(ASSUME `bigdigit n (k - 1) = h`)) THEN
        SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND];
        ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]] THEN
      AP_TERM_TAC THEN REWRITE_TAC[WORD_ADD] THEN
      ASM_REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_1] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN COND_CASES_TAC THENL
       [ASM_SIMP_TAC[ARITH_RULE `r <= h ==> (h < r + 1 <=> h = r)`] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN
        EXISTS_TAC `if r = h then 0 else r` THEN
        UNDISCH_TAC `q * h + r = 2 EXP (64 + 62)` THEN
        UNDISCH_TAC `r:num <= h` THEN REWRITE_TAC[LE_LT] THEN
        UNDISCH_TAC `2 EXP 63 <= h` THEN
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES;LT_REFL] THEN ARITH_TAC;
        MATCH_MP_TAC(TAUT `F ==> p`) THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
         `~(r + 1 < e) ==> r <= h /\ h < e ==> r = e - 1 /\ h = e - 1`)) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        UNDISCH_TAC `q * h + r = 2 EXP (64 + 62)` THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
         `q * n + n:num = e ==> n divides e`)) THEN
        SIMP_TAC[DIVIDES_PRIMEPOW; PRIME_2] THEN
        DISCH_THEN(X_CHOOSE_THEN `i:num` (MP_TAC o CONJUNCT2)) THEN
        ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THENL
         [CONV_TAC NUM_REDUCE_CONV; DISCH_THEN(MP_TAC o AP_TERM `EVEN`)] THEN
        ASM_REWRITE_TAC[EVEN_EXP] THEN CONV_TAC NUM_REDUCE_CONV]];
    ALL_TAC] THEN

  (*** Ghost the quotient estimate q = floor(2^126/h) ***)

  GHOST_INTRO_TAC `q:int64` `read R8` THEN GLOBALIZE_PRECONDITION_TAC THEN

  (*** The "mulloop" doing q * n ***)

  ENSURES_SEQUENCE_TAC `pc + 0xee`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R12 s = mm /\
        read R13 s = t /\
        bignum_from_memory (mm,k) s = m /\
        bignum_from_memory (t,k) s = n /\
        2 EXP (64 * k) * val(read RCX s) + bignum_from_memory(z,k) s =
        val(q:int64) * n` THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `k:num` `pc + 0xd0` `pc + 0xe9`
     `\i s. read RDI s = word k /\
            read RSI s = z /\
            read R12 s = mm /\
            read R13 s = t /\
            bignum_from_memory (mm,k) s = m /\
            bignum_from_memory (t,k) s = n /\
            read R8 s = q /\
            read RBX s = word i /\
            bignum_from_memory(word_add t (word (8 * i)),k - i) s =
            highdigits n i /\
            2 EXP (64 * i) * val(read RCX s) + bignum_from_memory(z,i) s =
            val(q:int64) * lowdigits n i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_0; VAL_WORD_0] THEN
      REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; WORD_ADD_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `hin:int64` `read RCX` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [2;3;4] (1--7) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; MULT_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0]];
    ALL_TAC] THEN

  (*** The "remloop" producing remainder by sign-correction ***)
  (*** We introduce an exclusion of m = 1 temporarily here. ***)

  ENSURES_SEQUENCE_TAC `pc + 0x125`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R12 s = mm /\
        read R13 s = t /\
        bignum_from_memory (mm,k) s = m /\
        bignum_from_memory (t,k) s = n /\
        (ODD m /\ ~(m = 1)
         ==> bignum_from_memory(z,k) s = 2 EXP (64 * k + 62) MOD n)` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `rhi:num` `\s. val(read RCX s)` THEN
    GHOST_INTRO_TAC `rlo:num` `bignum_from_memory (z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `rlo:num` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    ABBREV_TAC `b <=> 2 EXP (64 * k + 62) <= val(q:int64) * n` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x107` `pc + 0x120`
     `\i s. read RDI s = word k /\
            read RSI s = z /\
            read R12 s = mm /\
            read R13 s = t /\
            read RBX s = word i /\
            bignum_from_memory (mm,k) s = m /\
            bignum_from_memory (t,k) s = n /\
            read R8 s = word_neg(word(bitval b)) /\
            val(word_neg(read RCX s)) <= 1 /\
            bignum_from_memory(word_add t (word (8 * i)),k - i) s =
            highdigits n i /\
            bignum_from_memory(word_add z (word (8 * i)),k - i) s =
            highdigits rlo i /\
            &(bignum_from_memory(z,i) s):real =
            &2 pow (64 * i) * &(val(word_neg(read RCX s))) +
            (&(bitval b) * &(lowdigits n i) - &(lowdigits rlo i))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--6) THEN
      REWRITE_TAC[VAL_WORD_0; WORD_NEG_0; BITVAL_CLAUSES; LE_0] THEN
      REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0; HIGHDIGITS_0] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0; BITVAL_CLAUSES] THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; BIGNUM_FROM_MEMORY_BYTES] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[WORD_NOT_MASK] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; NOT_LT] THEN
      REPLICATE_TAC 3 AP_TERM_TAC THEN EXPAND_TAC "b" THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD] THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [ARITH_RULE `x = x + 0`] THEN
      ASM_SIMP_TAC[LEXICOGRAPHIC_LE; EXP_LT_0; ARITH_EQ] THEN ARITH_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cval:num` `\s. val(word_neg(read RCX s))` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[VAL_EQ_BITVAL] THEN
      REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--7) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM WORD_ADD] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0] THEN
      REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0; MULT_CLAUSES] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      CONV_TAC REAL_RING;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      GHOST_INTRO_TAC `cval:num` `\s. val(word_neg(read RCX s))` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[VAL_EQ_BITVAL] THEN
      REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
      GHOST_INTRO_TAC `r:num` `bignum_from_memory (z,k)` THEN
      BIGNUM_TERMRANGE_TAC `k:num` `r:num` THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
      DISCH_THEN(fun th -> REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MP th)))] THEN
    UNDISCH_TAC `2 EXP (64 * k - 1) <= n` THEN ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[CONJUNCT1 LE; EXP_EQ_0; ARITH_EQ] THEN DISCH_TAC THEN

    SUBGOAL_THEN `val(q:int64) = 2 EXP 126 DIV h` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN MATCH_MP_TAC(ARITH_RULE
       `x <= 2 EXP 126 DIV 2 EXP 63 ==> x < 2 EXP 64`) THEN
      MATCH_MP_TAC DIV_MONO2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      UNDISCH_THEN `q:int64 = word(2 EXP 126 DIV h)` (K ALL_TAC)] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`64 * k`;
      `&(bitval b) * &n +
       (&2 pow (64 * k + 62) - &(2 EXP 126 DIV h) * &n):real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      UNDISCH_THEN `2 EXP (64 * k) * rhi + rlo = 2 EXP 126 DIV h * n`
       (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_POW_ADD] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
      REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; REAL_MUL_ASSOC] THEN
      SIMP_TAC[REAL_MUL_LINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      REAL_INTEGER_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC remalemma THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC `m:num` o MATCH_MP (NUMBER_RULE
       `n divides x ==> !m:num. m divides n ==> m divides x`)) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[DIVIDES_PRIMEPOW; PRIME_2] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` (SUBST_ALL_TAC o CONJUNCT2)) THEN
      MAP_EVERY UNDISCH_TAC [`~(2 EXP i = 1)`; `ODD(2 EXP i)`] THEN
      SIMP_TAC[ODD_EXP; ARITH; EXP];
      ALL_TAC] THEN

    MP_TAC(ASSUME `2 EXP (64 * (k - 1)) * h + l = n`) THEN DISCH_THEN(fun th ->
     GEN_REWRITE_TAC (LAND_CONV o funpow 4 RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    SUBGOAL_THEN `64 * k + 62 = 64 * (k - 1) + 126` SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; REWRITE_TAC[REAL_POW_ADD]] THEN
    REWRITE_TAC[REAL_ARITH
     `ee * e - d * (ee * h + l):real = ee * (e - d * h) - d * l`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; GSYM REAL_OF_NUM_MOD] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x y:real. &0 <= x /\ &0 <= y /\ x <= e /\ y <= e
                 ==> abs(x - y) <= e`) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `2 EXP (64 * (k - 1)) * h + l = n`) THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      MATCH_MP_TAC(ARITH_RULE `a:num < b ==> a <= b + c`) THEN
      REWRITE_TAC[LT_MULT_LCANCEL; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
      UNDISCH_TAC `2 EXP 63 <= h` THEN ARITH_TAC;

      TRANS_TAC LE_TRANS `2 EXP 63 * 2 EXP (64 * (k - 1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[LT_IMP_LE] THEN
        SUBST1_TAC(ARITH_RULE `2 EXP 63 = 2 EXP 126 DIV 2 EXP 63`) THEN
        MATCH_MP_TAC DIV_MONO2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        MP_TAC(ASSUME `2 EXP (64 * (k - 1)) * h + l = n`) THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
        MATCH_MP_TAC(ARITH_RULE
         `ee * e:num <= ee * h ==> e * ee <= ee * h + l`) THEN
        ASM_REWRITE_TAC[LE_MULT_LCANCEL]]];
    ALL_TAC] THEN

  (*** The first modular doubling, "dubloop1" and "corrloop1" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x17c`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R12 s = mm /\
        read R13 s = t /\
        bignum_from_memory (mm,k) s = m /\
        bignum_from_memory (t,k) s = n /\
        (ODD m /\ ~(m = 1)
         ==> bignum_from_memory(z,k) s = 2 EXP (64 * k + 63) MOD n)` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `p62:num` `bignum_from_memory (z,k)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    BIGNUM_TERMRANGE_TAC `k:num` `p62:num` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x12e` `pc + 0x14c`
      `\i s. read RDI s = word k /\
             read RSI s = z /\
             read R12 s = mm /\
             read R13 s = t /\
             bignum_from_memory (mm,k) s = m /\
             bignum_from_memory (t,k) s = n /\
             read RBP s = word i /\
             (read RCX s =
              if i = 0 then word 0 else word(bigdigit p62 (i - 1))) /\
             bignum_from_memory (word_add z (word(8 * i)),k - i) s =
             highdigits p62 i /\
             bignum_from_memory (word_add t (word(8 * i)),k - i) s =
             highdigits n i /\
             val(word_neg(read R9 s)) <= 1 /\
             &(bignum_from_memory(z,i) s):real =
             &2 pow (64 * i) * &(val(word_neg(read R9 s))) +
             &(lowdigits (2 * p62) i) - &(lowdigits n i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
      REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LE_0] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cinn:num` `\s. val(word_neg(read R9 s))` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[VAL_EQ_BITVAL] THEN
      REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--8) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
      SIMP_TAC[GSYM WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; REAL_POW_ADD] THEN
      MATCH_MP_TAC(REAL_RING
       `ee * y:real = w - z
        ==> --e * c + s = y ==> z + ee * s = (ee * e) * c + w`) THEN
      REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_ARITH
       `x - y:real = z <=> x = y + z`] THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      REWRITE_TAC[REAL_ARITH `(x:real) * &2 pow k = &2 pow k * x`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; LE_REFL] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
       [REWRITE_TAC[ARITH_RULE `(2 EXP 64 * x) DIV 2 EXP 63 = 2 * x`] THEN
        REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
        CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
        ALL_TAC] THEN
      TRANS_TAC EQ_TRANS
       `(highdigits p62 (i - 1) DIV 2 EXP 63) MOD 2 EXP 64` THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP] THEN
        ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> i - 1 + 1 = i`; DIV_MOD] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CONG] THEN
        MATCH_MP_TAC(NUMBER_RULE
         `(a:num == a') (mod n)
          ==> (e * a + b == e * a' + b) (mod (n * e))`) THEN
        REWRITE_TAC[bigdigit; highdigits; CONG; MOD_MOD_EXP_MIN] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
        REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
        ASM_SIMP_TAC[bigdigit; EXP; DIV_MULT2; ARITH_EQ; ARITH_RULE
         `~(i = 0) ==> 64 * i = SUC(64 * (i - 1) + 63)`]];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN
      VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
      ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

    GHOST_INTRO_TAC `hinn:num` `\s. val(word_neg(read R9 s))` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `hi:bool` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN
    REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
    GHOST_INTRO_TAC `lo:num` `bignum_from_memory(z,k)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
    BIGNUM_TERMRANGE_TAC `k:num` `lo:num` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x15e` `pc + 0x177`
      `\i s. read RDI s = word k /\
             read RSI s = z /\
             read R12 s = mm /\
             read R13 s = t /\
             bignum_from_memory (mm,k) s = m /\
             bignum_from_memory (t,k) s = n /\
             read RBP s = word i  /\
             bignum_from_memory (word_add z (word(8 * i)),k - i) s =
             highdigits lo i /\
             bignum_from_memory (word_add t (word(8 * i)),k - i) s =
             highdigits n i /\
             val(word_neg(read R9 s)) <= 1 /\
             (p62 < n
              ==> read RCX s = word_neg(word(bitval(2 * p62 < n))) /\
                  &(bignum_from_memory(z,i) s):real =
                  (&(lowdigits lo i) +
                  &(bitval(2 * p62 < n)) * &(lowdigits n i)) -
                  &2 pow (64 * i) * &(val(word_neg(read R9 s))))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0] THEN
      REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LE_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BITVAL_CLAUSES] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_REFL; REAL_ADD_LID] THEN
      DISCH_TAC THEN REWRITE_TAC[WORD_RULE
       `word_add a (word_neg b) = word_neg c <=> word_add c a = b`] THEN
      MP_TAC(GEN `x:int64` (ISPEC `x:int64` WORD_USHR_MSB)) THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_BITVAL; VAL_WORD_ADD_CASES] THEN
      SIMP_TAC[DIMINDEX_64; BITVAL_BOUND; ARITH_RULE
       `b <= 1 /\ c <= 1 ==> b + c < 2 EXP 64`] THEN
      SUBGOAL_THEN `2 * p62 < 2 * n /\ 2 * p62 < 2 * 2 EXP (64 * k)`
      MP_TAC THENL
       [ASM_REWRITE_TAC[LT_MULT_LCANCEL; ARITH_EQ]; ALL_TAC] THEN
      SUBGOAL_THEN
       `2 * p62 = 2 EXP (64 * k) *
                bitval(bit 63 (word(bigdigit p62 (k - 1)):int64)) +
                lowdigits (2 * p62) k`
      SUBST1_TAC THENL
       [MP_TAC(SPECL [`2 * p62`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        MP_TAC(ISPEC `word(bigdigit p62 (k - 1)):int64` WORD_USHR_MSB) THEN
        REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
        DISCH_THEN(MP_TAC o SYM o AP_TERM `val:int64->num`) THEN
        REWRITE_TAC[VAL_WORD_BITVAL; VAL_WORD_USHR] THEN
        DISCH_THEN SUBST1_TAC THEN
        SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
        ASM_SIMP_TAC[highdigits; ARITH_RULE
         `~(k = 0) ==> 64 * k = SUC(64 * (k - 1) + 63)`] THEN
        SIMP_TAC[DIV_MULT2; EXP; ARITH_EQ] THEN
        REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[bigdigit] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MOD_LT THEN
        ASM_SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
        ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 64 * (k - 1) + 64 = 64 * k`];
        ALL_TAC] THEN
      ASM_CASES_TAC `bit 63 (word(bigdigit p62 (k - 1)):int64)` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THENL
       [ASM_SIMP_TAC[ARITH_RULE `n:num < e ==> ~(e + a < n)`] THEN
        UNDISCH_TAC
         `&lo:real =
           &2 pow (64 * k) * &(bitval hi) + &(lowdigits (2 * p62) k) - &n` THEN
        UNDISCH_TAC `lo < 2 EXP (64 * k)` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOOL_CASES_TAC `hi:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
        REAL_ARITH_TAC;
        STRIP_TAC THEN AP_TERM_TAC THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
        EXISTS_TAC `64 * k` THEN REWRITE_TAC[GSYM REAL_BITVAL_NOT] THEN
        UNDISCH_THEN
         `&lo:real =
           &2 pow (64 * k) * &(bitval hi) + &(lowdigits (2 * p62) k) - &n`
         (SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0]];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cinn:num` `\s. val(word_neg(read R9 s))` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[VAL_EQ_BITVAL] THEN
      REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
      GHOST_INTRO_TAC `hi:int64` `read RCX` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--7) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[GSYM WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
      DISCH_THEN(fun th ->
        REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
        ASSUME_TAC th) THEN
      ASM_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; WORD_BITVAL_EQ_0;
                  LOWDIGITS_CLAUSES; WORD_NEG_EQ_0; BITVAL_BOUND; NOT_LT] THEN
      REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[NOT_LT] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0;
               BITVAL_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN
      VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
      ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th)) THEN
      ASSUME_TAC(CONJUNCT2 th) THEN MP_TAC(CONJUNCT1 th)) THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th)) THEN
      ASSUME_TAC th) THEN
    SUBGOAL_THEN `2 EXP (64 * k + 63) MOD n =
                  (2 * 2 EXP (64 * k + 62) MOD n) MOD n`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `n + 63 = SUC(n + 62)`; EXP] THEN
      CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p62:num < n`
     (fun th -> FIRST_X_ASSUM(MP_TAC o C MP th) THEN ASSUME_TAC th)
    THENL
     [ASM_REWRITE_TAC[MOD_LT_EQ] THEN
      UNDISCH_TAC `2 EXP (64 * k - 1) <= n` THEN
      SIMP_TAC[GSYM NOT_LT; CONTRAPOS_THM; EXP_LT_0] THEN ARITH_TAC;
      UNDISCH_THEN `p62 = 2 EXP (64 * k + 62) MOD n` (SUBST1_TAC o SYM)] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_ADD_CASES; MULT_2; ARITH_RULE
     `p62 < n ==> p62 + p62 < 2 * n`] THEN
    REWRITE_TAC[GSYM MULT_2] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`p62:num < n`; `n < 2 EXP (64 * k)`] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_FIELD `inv(&2 pow n) * &2 pow n = (&1:real)`] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[REAL_ARITH
     `--(&2) * e * a + e * b + c:real = e * (b - &2 * a) + c`] THEN
    MATCH_MP_TAC INTEGER_ADD THEN
    (CONJ_TAC THENL [ALL_TAC; REAL_INTEGER_TAC]) THEN
    REWRITE_TAC[REAL_ARITH `inv x * (a - b):real = (a - b) / x`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    W(MP_TAC o PART_MATCH (rand o rand) REAL_CONGRUENCE o snd) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[CONG; lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  (*** The second modular doubling, "dubloop2" and "corrloop2" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x1d8`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R12 s = mm /\
        read R13 s = t /\
        bignum_from_memory (mm,k) s = m /\
        (ODD m /\ ~(m = 1)
         ==> bignum_from_memory(z,k) s = 2 EXP (64 * k + 64) MOD n /\
             bignum_from_memory(t,k) s = 2 EXP (64 * k + 64) MOD n)` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `p63:num` `bignum_from_memory (z,k)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    BIGNUM_TERMRANGE_TAC `k:num` `p63:num` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x185` `pc + 0x1a3`
      `\i s. read RDI s = word k /\
             read RSI s = z /\
             read R12 s = mm /\
             read R13 s = t /\
             bignum_from_memory (mm,k) s = m /\
             bignum_from_memory(t,k) s = n /\
             read RBP s = word i /\
             (read RCX s =
              if i = 0 then word 0 else word(bigdigit p63 (i - 1))) /\
             bignum_from_memory (word_add z (word(8 * i)),k - i) s =
             highdigits p63 i /\
             bignum_from_memory (word_add t (word(8 * i)),k - i) s =
             highdigits n i /\
             val(word_neg(read R9 s)) <= 1 /\
             &(bignum_from_memory(z,i) s):real =
             &2 pow (64 * i) * &(val(word_neg(read R9 s))) +
             &(lowdigits (2 * p63) i) - &(lowdigits n i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
      REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LE_0] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cinn:num` `\s. val(word_neg(read R9 s))` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[VAL_EQ_BITVAL] THEN
      REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--8) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
      SIMP_TAC[GSYM WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; REAL_POW_ADD] THEN
      MATCH_MP_TAC(REAL_RING
       `ee * y:real = w - z
        ==> --e * c + s = y ==> z + ee * s = (ee * e) * c + w`) THEN
      REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_ARITH
       `x - y:real = z <=> x = y + z`] THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      REWRITE_TAC[REAL_ARITH `(x:real) * &2 pow k = &2 pow k * x`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; LE_REFL] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
       [REWRITE_TAC[ARITH_RULE `(2 EXP 64 * x) DIV 2 EXP 63 = 2 * x`] THEN
        REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
        CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
        ALL_TAC] THEN
      TRANS_TAC EQ_TRANS
       `(highdigits p63 (i - 1) DIV 2 EXP 63) MOD 2 EXP 64` THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP] THEN
        ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> i - 1 + 1 = i`; DIV_MOD] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CONG] THEN
        MATCH_MP_TAC(NUMBER_RULE
         `(a:num == a') (mod n)
          ==> (e * a + b == e * a' + b) (mod (n * e))`) THEN
        REWRITE_TAC[bigdigit; highdigits; CONG; MOD_MOD_EXP_MIN] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
        REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
        ASM_SIMP_TAC[bigdigit; EXP; DIV_MULT2; ARITH_EQ; ARITH_RULE
         `~(i = 0) ==> 64 * i = SUC(64 * (i - 1) + 63)`]];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN
      VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
      ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

    GHOST_INTRO_TAC `hinn:num` `\s. val(word_neg(read R9 s))` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `hi:bool` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN
    REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
    GHOST_INTRO_TAC `lo:num` `bignum_from_memory(z,k)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
    BIGNUM_TERMRANGE_TAC `k:num` `lo:num` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x1b5` `pc + 0x1d3`
      `\i s. read RDI s = word k /\
             read RSI s = z /\
             read R12 s = mm /\
             read R13 s = t /\
             bignum_from_memory (mm,k) s = m /\
             read RBP s = word i  /\
             bignum_from_memory (word_add z (word(8 * i)),k - i) s =
             highdigits lo i /\
             bignum_from_memory (word_add t (word(8 * i)),k - i) s =
             highdigits n i /\
             val(word_neg(read R9 s)) <= 1 /\
             (p63 < n
              ==> read RCX s = word_neg(word(bitval(2 * p63 < n))) /\
                  &(bignum_from_memory(z,i) s):real =
                  (&(lowdigits lo i) +
                  &(bitval(2 * p63 < n)) * &(lowdigits n i)) -
                  &2 pow (64 * i) * &(val(word_neg(read R9 s))) /\
                  &(bignum_from_memory(t,i) s):real =
                  (&(lowdigits lo i) +
                  &(bitval(2 * p63 < n)) * &(lowdigits n i)) -
                  &2 pow (64 * i) * &(val(word_neg(read R9 s))))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0] THEN
      REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LE_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BITVAL_CLAUSES] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_REFL; REAL_ADD_LID] THEN
      DISCH_TAC THEN REWRITE_TAC[WORD_RULE
       `word_add a (word_neg b) = word_neg c <=> word_add c a = b`] THEN
      MP_TAC(GEN `x:int64` (ISPEC `x:int64` WORD_USHR_MSB)) THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_BITVAL; VAL_WORD_ADD_CASES] THEN
      SIMP_TAC[DIMINDEX_64; BITVAL_BOUND; ARITH_RULE
       `b <= 1 /\ c <= 1 ==> b + c < 2 EXP 64`] THEN
      SUBGOAL_THEN `2 * p63 < 2 * n /\ 2 * p63 < 2 * 2 EXP (64 * k)`
      MP_TAC THENL
       [ASM_REWRITE_TAC[LT_MULT_LCANCEL; ARITH_EQ]; ALL_TAC] THEN
      SUBGOAL_THEN
       `2 * p63 = 2 EXP (64 * k) *
                bitval(bit 63 (word(bigdigit p63 (k - 1)):int64)) +
                lowdigits (2 * p63) k`
      SUBST1_TAC THENL
       [MP_TAC(SPECL [`2 * p63`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        MP_TAC(ISPEC `word(bigdigit p63 (k - 1)):int64` WORD_USHR_MSB) THEN
        REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
        DISCH_THEN(MP_TAC o SYM o AP_TERM `val:int64->num`) THEN
        REWRITE_TAC[VAL_WORD_BITVAL; VAL_WORD_USHR] THEN
        DISCH_THEN SUBST1_TAC THEN
        SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
        ASM_SIMP_TAC[highdigits; ARITH_RULE
         `~(k = 0) ==> 64 * k = SUC(64 * (k - 1) + 63)`] THEN
        SIMP_TAC[DIV_MULT2; EXP; ARITH_EQ] THEN
        REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[bigdigit] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MOD_LT THEN
        ASM_SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
        ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 64 * (k - 1) + 64 = 64 * k`];
        ALL_TAC] THEN
      ASM_CASES_TAC `bit 63 (word(bigdigit p63 (k - 1)):int64)` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THENL
       [ASM_SIMP_TAC[ARITH_RULE `n:num < e ==> ~(e + a < n)`] THEN
        UNDISCH_TAC
         `&lo:real =
           &2 pow (64 * k) * &(bitval hi) + &(lowdigits (2 * p63) k) - &n` THEN
        UNDISCH_TAC `lo < 2 EXP (64 * k)` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOOL_CASES_TAC `hi:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
        REAL_ARITH_TAC;
        STRIP_TAC THEN AP_TERM_TAC THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
        EXISTS_TAC `64 * k` THEN REWRITE_TAC[GSYM REAL_BITVAL_NOT] THEN
        UNDISCH_THEN
         `&lo:real =
           &2 pow (64 * k) * &(bitval hi) + &(lowdigits (2 * p63) k) - &n`
         (SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0]];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cinn:num` `\s. val(word_neg(read R9 s))` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[VAL_EQ_BITVAL] THEN
      REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
      GHOST_INTRO_TAC `hi:int64` `read RCX` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--8) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[GSYM WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
      DISCH_THEN(fun th ->
        REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
        ASSUME_TAC th) THEN
      ASM_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; WORD_BITVAL_EQ_0;
                  LOWDIGITS_CLAUSES; WORD_NEG_EQ_0; BITVAL_BOUND; NOT_LT] THEN
      REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[NOT_LT] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0;
               BITVAL_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN
      VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
      ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th)) THEN
      ASSUME_TAC(CONJUNCT2 th) THEN MP_TAC(CONJUNCT1 th)) THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th)) THEN
      ASSUME_TAC th) THEN
    SUBGOAL_THEN `2 EXP (64 * k + 64) MOD n =
                  (2 * 2 EXP (64 * k + 63) MOD n) MOD n`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `n + 64 = SUC(n + 63)`; EXP] THEN
      CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p63:num < n`
     (fun th -> FIRST_X_ASSUM(MP_TAC o C MP th) THEN ASSUME_TAC th)
    THENL
     [ASM_REWRITE_TAC[MOD_LT_EQ] THEN
      UNDISCH_TAC `2 EXP (64 * k - 1) <= n` THEN
      SIMP_TAC[GSYM NOT_LT; CONTRAPOS_THM; EXP_LT_0] THEN ARITH_TAC;
      UNDISCH_THEN `p63 = 2 EXP (64 * k + 63) MOD n` (SUBST1_TAC o SYM)] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_ADD_CASES; MULT_2; ARITH_RULE
     `p63 < n ==> p63 + p63 < 2 * n`] THEN
    REWRITE_TAC[GSYM MULT_2] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(MESON[] `x = y /\ x = a ==> x = a /\ y = a`) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`p63:num < n`; `n < 2 EXP (64 * k)`] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_FIELD `inv(&2 pow n) * &2 pow n = (&1:real)`] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[REAL_ARITH
     `--(&2) * e * a + e * b + c:real = e * (b - &2 * a) + c`] THEN
    MATCH_MP_TAC INTEGER_ADD THEN
    (CONJ_TAC THENL [ALL_TAC; REAL_INTEGER_TAC]) THEN
    REWRITE_TAC[REAL_ARITH `inv x * (a - b):real = (a - b) / x`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    W(MP_TAC o PART_MATCH (rand o rand) REAL_CONGRUENCE o snd) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[CONG; lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  (*** A bit of cleanup ***)

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `h:num` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `l:num` o concl))) THEN
  REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  GHOST_INTRO_TAC `r:num` `bignum_from_memory (z,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `r:num` THEN GLOBALIZE_PRECONDITION_TAC THEN

  (*** Now the main loop "modloop" ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x1de` `pc + 0x249`
   `\i s. (read RDI s = word k /\
           read RSI s = z /\
           read R12 s = mm /\
           read R13 s = t /\
           read RBX s = word(k - i) /\
           bignum_from_memory (mm,k) s = m /\
           bignum_from_memory (z,k) s = r /\
           (ODD m ==> (2 EXP (64 * k) * val(read R11 s) +
                       bignum_from_memory(t,k) s ==
                       2 EXP (64 * (k + i + 1))) (mod m))) /\
          (read ZF s <=> i = k)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES; SUB_0] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
    ASM_CASES_TAC `m = 1` THEN ASM_SIMP_TAC[CONG_MOD_1; MULT_CLAUSES] THEN
    DISCH_TAC THEN MATCH_MP_TAC(NUMBER_RULE
     `!m:num. (a == b) (mod n) /\ m divides n ==> (a == b) (mod m)`) THEN
    ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; CONG_LMOD; CONG_REFL];

    (*** The main loop invariant of "modloop" ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `h:num` `\s. val(read R11 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GHOST_INTRO_TAC `t1:num` `bignum_from_memory (t,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `t1:num` THEN GLOBALIZE_PRECONDITION_TAC THEN

    (*** The inner multiply-add loop "cmaloop" ***)

    ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x1ea` `pc + 0x210`
     `\j s. (read RDI s = word k /\
             read RSI s = z /\
             read R12 s = mm /\
             read R13 s = t /\
             read RBX s = word (k - i) /\
             bignum_from_memory (mm,k) s = m /\
             bignum_from_memory (z,k) s = r /\
             read R11 s = word h /\
             read RBP s = word j /\
             read R8 s = word(k - j) /\
             bignum_from_memory (word_add z (word(8 * j)),k - j) s =
             highdigits r j /\
             bignum_from_memory (word_add t (word(8 * j)),k - j) s =
             highdigits t1 j /\
             read R9 s = word(bigdigit (2 EXP 64 * t1) j) /\
             2 EXP (64 * j) * (bitval(read CF s) + val(read RCX s)) +
             bignum_from_memory(t,j) s =
             lowdigits (2 EXP 64 * t1) j + h * lowdigits r j) /\
            (read ZF s <=> j = k)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--4) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_0; BITVAL_CLAUSES; VAL_WORD_0] THEN
      REWRITE_TAC[WORD_ADD_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES; MOD_MULT];

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read RCX` THEN
      GHOST_INTRO_TAC `prd:int64` `read R9` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [1;4] (1--5) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
       `word_sub x (word_neg y):int64 = word_add x y`]) THEN
      ACCUMULATE_ARITH_TAC "s5" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [6] (6--11) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN REWRITE_TAC[bigdigit] THEN
        REWRITE_TAC[ARITH_RULE `64 * (j + 1) = 64 + 64 * j`] THEN
        SIMP_TAC[EXP_ADD; DIV_MULT2; EXP_EQ_0; ARITH_EQ];
        REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC];
        VAL_INT64_TAC `k - (j + 1)` THEN ASM_REWRITE_TAC[] THEN
        SIMPLE_ARITH_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV
       [ARITH_RULE `e * d1 + d0 + c * (e * a1 + a0):num =
                    e * (c * a1 + d1) + d0 + c * a0`] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (j + 1) = 64 * j + 64`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      GEN_REWRITE_TAC LAND_CONV
       [TAUT `p /\ q /\ r /\ s <=> p /\ s /\ q /\ r`] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

    (*** Additional absorption of the top digit before correction ***)

    ENSURES_SEQUENCE_TAC `pc + 0x218`
     `\s. read RDI s = word k /\
          read RSI s = z /\
          read R12 s = mm /\
          read R13 s = t /\
          read RBX s = word (k - i) /\
          bignum_from_memory (mm,k) s = m /\
          bignum_from_memory (z,k) s = r /\
          2 EXP (64 * k) * (2 EXP 64 * bitval(read CF s) + val(read R11 s)) +
          bignum_from_memory(t,k) s =
          2 EXP 64 * t1 + h * r` THEN
    CONJ_TAC THENL
     [GHOST_INTRO_TAC `hup:int64` `read RCX` THEN
      GHOST_INTRO_TAC `cup:bool` `read CF` THEN
      GHOST_INTRO_TAC `tup:num` `bignum_from_memory (t,k)` THEN
      BIGNUM_TERMRANGE_TAC `k:num` `tup:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [2] (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE
        `e * (a + b + c) + d:num = e * a + e * (c + b) + d`] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 LOWDIGITS_CLAUSES)] THEN
      MATCH_MP_TAC LOWDIGITS_SELF THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (j + 1) = 64 + 64 * j`] THEN
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ];
      GHOST_INTRO_TAC `hup:int64` `read R11` THEN
      GHOST_INTRO_TAC `cup:bool` `read CF` THEN
      GHOST_INTRO_TAC `tup:num` `bignum_from_memory (t,k)` THEN
      BIGNUM_TERMRANGE_TAC `k:num` `tup:num` THEN
      GLOBALIZE_PRECONDITION_TAC] THEN

    (**** The optional addition loop "oaloop" fixing things up ***)

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x221` `pc + 0x23e`
     `\j s. read RDI s = word k /\
            read RSI s = z /\
            read R12 s = mm /\
            read R13 s = t /\
            read RBX s = word (k - i) /\
            bignum_from_memory (mm,k) s = m /\
            bignum_from_memory (z,k) s = r /\
            read R11 s = hup /\
            read R10 s = word_neg(word(bitval cup)) /\
            read RBP s = word j /\
            bignum_from_memory (word_add z (word(8 * j)),k - j) s =
            highdigits r j /\
            bignum_from_memory (word_add t (word(8 * j)),k - j) s =
            highdigits tup j /\
            val(word_neg(read RCX s)) <= 1 /\
            2 EXP (64 * j) * val(word_neg(read RCX s)) +
            bignum_from_memory(t,j) s =
            lowdigits tup j + bitval(cup) * lowdigits r j` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--3) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_0; BITVAL_CLAUSES; VAL_WORD_0] THEN
      REWRITE_TAC[WORD_ADD_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      GHOST_INTRO_TAC `cinn:num` `\s. val(word_neg(read RCX s))` THEN
        GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[VAL_EQ_BITVAL] THEN
      REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[REAL_ARITH
      `&2 pow k * c + z:real = w <=> z = w - &2 pow k * c`] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [5] (1--8) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; LOWDIGITS_CLAUSES] THEN
      REWRITE_TAC[ARITH_RULE `64 * (j + 1) = 64 * j + 64`; REAL_POW_ADD] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_BITVAL_EQ_0; WORD_NEG_EQ_0] THEN
      REWRITE_TAC[WORD_AND_MASK] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; BITVAL_CLAUSES] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      CONV_TAC REAL_RING;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

    (*** The final case analysis and conclusion ***)

    GHOST_INTRO_TAC `topcv:num` `\s. val(word_neg(read RCX s))` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `topc:bool` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN
    REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
    GHOST_INTRO_TAC `tout:num` `bignum_from_memory(t,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `tout:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

    X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y) = word_add x y`]) THEN
    ACCUMULATE_ARITH_TAC "s3" THEN
    X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> r) /\ q ==> p /\ q /\ r `) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `a - (i + 1) = a - i - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < k ==> 1 <= k - i`];
      DISCH_THEN SUBST1_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o
        lhand o lhand o snd) THEN
      REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THENL
       [ALL_TAC; DISCH_THEN SUBST1_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`k < 2 EXP 64`; `i:num < k`] THEN ARITH_TAC;
      DISCH_THEN(fun th ->
        REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
        ASSUME_TAC th)] THEN
    REWRITE_TAC[ARITH_RULE
     `64 * (k + (i + 1) + 1) = 64 + 64 * (k + i + 1)`] THEN
    ONCE_REWRITE_TAC[EXP_ADD] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE `(x:num == a) (mod m)
                   ==> (e * x == y) (mod m) ==> (y == e * a) (mod m)`)) THEN
    UNDISCH_TAC `ODD m /\ ~(m = 1) ==> r = 2 EXP (64 * k + 64) MOD n` THEN
    ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[CONG_MOD_1] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP(MESON[CONG_RMOD; CONG_REFL]
     `x = y MOD n ==> (y == x) (mod n)`)) THEN
    REWRITE_TAC[ARITH_RULE `e * (ee * h + t):num = e * t + (ee * e) * h`] THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
     `(e1:num == r) (mod n)
      ==> m divides n /\ (t + r * h == z) (mod m)
          ==> (t + e1 * h == z) (mod m)`)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(sum_s3:int64) = val(hup:int64) + bitval topc`
    SUBST1_TAC THENL
     [ALL_TAC;
      MAP_EVERY UNDISCH_TAC
       [`2 EXP (64 * k) * (2 EXP 64 * bitval cup + val(hup:int64)) + tup =
         2 EXP 64 * t1 + h * r`;
        `2 EXP (64 * k) * bitval topc + tout = tup + bitval cup * r`;
        `(2 EXP (64 * k + 64) == r) (mod n)`; `(m:num) divides n`] THEN
      REWRITE_TAC[EXP_ADD] THEN SPEC_TAC(`2 EXP (64 * k)`,`ee:num`) THEN
      SPEC_TAC(`2 EXP 64`,`e:num`) THEN
      BOOL_CASES_TAC `cup:bool` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
      CONV_TAC NUMBER_RULE] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC(ARITH_RULE
     `(e * c < e * 1 ==> e * c = 0) /\ z < e
      ==> e * c + s:num = z ==> s = z`) THEN
    REWRITE_TAC[LT_MULT_LCANCEL; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `b < 1 ==> b = 0`] THEN
    SUBGOAL_THEN `2 EXP (64 * k) * (val(hup:int64) + bitval topc) <
                  2 EXP (64 * k) * 2 EXP 64`
    MP_TAC THENL
     [ALL_TAC; REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]] THEN
    MAP_EVERY UNDISCH_TAC
     [`2 EXP (64 * k) * (2 EXP 64 * bitval cup + val(hup:int64)) + tup =
       2 EXP 64 * t1 + h * r`;
      `2 EXP (64 * k) * bitval topc + tout = tup + bitval cup * r`] THEN
    ASM_CASES_TAC `cup:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THENL
     [SUBGOAL_THEN `2 EXP 64 * t1 < 2 EXP 64 * 2 EXP (64 * k) /\
                   (h + 1) * r <= 2 EXP 64 * 2 EXP (64 * k)`
      MP_TAC THENL [ALL_TAC; ARITH_TAC] THEN
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
      MATCH_MP_TAC LE_MULT2 THEN
      ASM_SIMP_TAC[LT_IMP_LE; ARITH_RULE `x + 1 <= y <=> x < y`];
      ALL_TAC] THEN
    ASM_CASES_TAC `topc:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THENL
     [MAP_EVERY UNDISCH_TAC
       [`tout < 2 EXP (64 * k)`; `tup < 2 EXP (64 * k)`] THEN
      ARITH_TAC;
      SIMP_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; VAL_BOUND_64]];

    (*** Trivial loop-back ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[] THEN X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1];

    ALL_TAC] THEN

  (*** Initial word modular inverse of Montgomery tail ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2a7`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R12 s = mm /\
        read R13 s = t /\
        bignum_from_memory (mm,k) s = m /\
        (ODD m
         ==> (2 EXP (64 * k) * val (read R11 s) +
              bignum_from_memory (t,k) s ==
              2 EXP (64 * (2 * k + 1))) (mod m)) /\
        (ODD m ==> (m * val(read R9 s) + 1 == 0) (mod (2 EXP 64)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC [1] THEN
    SUBGOAL_THEN `bignum_from_memory(mm,k) s1 = highdigits m 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC LAND_CONV[BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; WORD_MOD_SIZE] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC] THEN
    X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (2--7) THEN
    SUBGOAL_THEN `ODD m ==> (m * val (read R9 s7) + 1 == 0) (mod 16)`
    MP_TAC THENL [ASM_SIMP_TAC[WORD_NEGMODINV_SEED_LEMMA_16]; ALL_TAC] THEN
    REABBREV_TAC `x0 = read R9 s7` THEN DISCH_TAC THEN
    X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (8--25) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * k + 1 = k + k + 1`] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 16 EXP (2 EXP 4)`) THEN
    DISCH_TAC THEN UNDISCH_TAC
     `ODD m ==> (m * val(x0:int64) + 1 == 0) (mod 16)` THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`16`,`e:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUMBER_RULE;
    GHOST_INTRO_TAC `w:num` `\s. val(read R9 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64]] THEN

  (*** More cleanup and setup of Montgomery multiplier ***)

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
  GHOST_INTRO_TAC `h:num` `\s. val(read R11 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GHOST_INTRO_TAC `z1:num` `bignum_from_memory (t,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z1:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  ABBREV_TAC `q0 = (w * z1) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `q0 < 2 EXP 64 /\ val(word q0:int64) = q0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL];
    ALL_TAC] THEN

  (*** The prelude of the Montgomery reduction ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2c7`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R12 s = mm /\
        read R13 s = t /\
        bignum_from_memory (mm,k) s = m /\
        bignum_from_memory (t,k) s = z1 /\
        read R11 s = word h /\
        read R9 s = word q0 /\
        read RBP s = word 1 /\
        read R8 s = word(k - 1) /\
        (read ZF s <=> k = 1) /\
        ?r0. r0 < 2 EXP 64 /\
             2 EXP 64 * (bitval(read CF s) + val(read RCX s)) + r0 =
             q0 * bigdigit m 0 + bigdigit z1 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(mm,k) s0 = highdigits m 0 /\
      bignum_from_memory(t,k) s0 = highdigits z1 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [5; 6] (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_1] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM WORD_MUL] THEN ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[ADD_CLAUSES; DIMINDEX_64; VAL_WORD] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN
    EXISTS_TAC `val(sum_s5:int64)` THEN REWRITE_TAC[VAL_BOUND_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Break at "montend" to share the end reasoning ***)

  GHOST_INTRO_TAC `carin:bool` `read CF` THEN
  GHOST_INTRO_TAC `mulin:int64` `read RCX` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r0:num` STRIP_ASSUME_TAC) THEN

  ENSURES_SEQUENCE_TAC `pc + 0x2ee`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R12 s = mm /\
        read R13 s = t /\
        bignum_from_memory (mm,k) s = m /\
        read R11 s = word h /\
        read R9 s = word q0 /\
        2 EXP (64 * k) * (bitval(read CF s) + val(read RCX s)) +
        2 EXP 64 * bignum_from_memory (t,k - 1) s + r0 =
        lowdigits z1 k + q0 * lowdigits m k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUB_REFL; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[LOWDIGITS_1] THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The Montgomery reduction loop "montloop" ***)

    VAL_INT64_TAC `k - 1` THEN

    ENSURES_WHILE_PAUP_TAC `1` `k:num` `pc + 0x2c9` `pc + 0x2ec`
     `\i s. (read RDI s = word k /\
             read RSI s = z /\
             read R12 s = mm /\
             read R13 s = t /\
             bignum_from_memory (mm,k) s = m /\
             read R11 s = word h /\
             read R9 s = word q0 /\
             read RBP s = word i /\
             read R8 s = word(k - i) /\
             bignum_from_memory(word_add t (word (8 * i)),k - i) s =
             highdigits z1 i /\
             bignum_from_memory(word_add mm (word (8 * i)),k - i) s =
             highdigits m i /\
             2 EXP (64 * i) * (bitval(read CF s) + val(read RCX s)) +
             2 EXP 64 * bignum_from_memory(t,i-1) s + r0 =
             lowdigits z1 i + q0 * lowdigits m i) /\
            (read ZF s <=> i = k)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0 \/ k = 1)`];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTIFIER_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k <= 1 <=> k = 0 \/ k = 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[GSYM highdigits; BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LOWDIGITS_1] THEN ARITH_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`i:num`; `i - 1`] THEN
      SUBGOAL_THEN `word_sub (word i) (word 1):int64 = word(i - 1)`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read RCX` THEN
      MP_TAC(GENL [`x:int64`; `a:num`]
       (ISPECL [`x:int64`; `k - i:num`; `a:num`; `i:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - i = 0 <=> ~(i < k)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      UNDISCH_THEN `val(word q0:int64) = q0` (K ALL_TAC) THEN
      ABBREV_TAC `i' = i - 1` THEN
      SUBGOAL_THEN `i = i' + 1` SUBST_ALL_TAC THENL
       [EXPAND_TAC "i'" THEN UNDISCH_TAC `1 <= i` THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(i' + 1) + 1 = i' + 2`]) THEN
      REWRITE_TAC[ARITH_RULE `(i' + 1) + 1 = i' + 2`] THEN
      MP_TAC(SPEC `i':num` WORD_INDEX_WRAP) THEN DISCH_TAC THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [1;4] (1--5) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
       `word_sub x (word_neg y):int64 = word_add x y`]) THEN
      ACCUMULATE_ARITH_TAC "s5" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [6] (6--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `k - (i + 2) = k - (i + 1) - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 <= k - (i + 1) <=> i + 1 < k`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        ASM_SIMP_TAC[ARITH_RULE
         `i + 1 < k ==> (i + 2 = k <=> k - (i + 2) = 0)`] THEN
        REWRITE_TAC[VAL_EQ_0] THEN MATCH_MP_TAC WORD_EQ_0 THEN
        REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `k < 2 EXP 64` THEN
        ARITH_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(n + 2) - 1 = n + 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `i' + 2 = (i' + 1) + 1` MP_TAC THENL
       [ARITH_TAC; DISCH_THEN SUBST_ALL_TAC] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ONCE_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      GEN_REWRITE_TAC RAND_CONV
       [ARITH_RULE `(e * d1 + d0) + c * (e * a1 + a0):num =
                    e * (c * a1 + d1) + d0 + c * a0`] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      GEN_REWRITE_TAC LAND_CONV
       [TAUT `p /\ q /\ r /\ s <=> p /\ s /\ q /\ r`] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`i:num`; `i - 1`] THEN
      X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1];

      X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1]];

    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

 (*** The final digit write ****)

  ENSURES_SEQUENCE_TAC `pc + 0x2f9`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R12 s = mm /\
        read R13 s = t /\
        bignum_from_memory (mm,k) s = m /\
        ?c. read R10 s = word_neg(word(bitval c)) /\
            2 EXP 64 * (2 EXP (64 * k) * bitval c +
                        bignum_from_memory(t,k) s) + r0 =
            (2 EXP (64 * k) * h + z1) + q0 * m` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GHOST_INTRO_TAC `hin:int64` `read RCX` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    VAL_INT64_TAC `k - 1` THEN
    SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`];
      ALL_TAC] THEN
    MP_TAC(SPEC `k - 1` WORD_INDEX_WRAP) THEN
    ASM_SIMP_TAC[SUB_ADD; LE_1] THEN DISCH_TAC THEN
    X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [1] (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `carry_s1:bool` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `8 * k = 8 * ((k - 1) + 1)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES]] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    SUBGOAL_THEN `64 * k = 64 * (k - 1) + 64` SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; REWRITE_TAC[REAL_POW_ADD]] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN

  (*** The final correction to keep inside k digits, "osloop" ***)

  GHOST_INTRO_TAC `z2:num` `bignum_from_memory(t,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z2:num` THEN
  GHOST_INTRO_TAC `g8:int64` `read R10` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `cf:bool`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x2ff` `pc + 0x31b`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read R12 s = mm /\
          read R13 s = t /\
          read R10 s = word_neg (word (bitval cf)) /\
          read RBP s = word i /\
          bignum_from_memory (word_add t (word(8 * i)),k - i) s =
          highdigits z2 i /\
          bignum_from_memory (word_add mm (word(8 * i)),k - i) s =
          highdigits m i /\
          val(word_neg(read RCX s)) <= 1 /\
          &(bignum_from_memory(z,i) s):real =
          &2 pow (64 * i) * &(val(word_neg(read RCX s))) +
          &(lowdigits z2 i) - &(bitval cf) * &(lowdigits m i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    REWRITE_TAC[VAL_WORD_0; WORD_NEG_0; LE_0] THEN
    REWRITE_TAC[WORD_SUB_LZERO; SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; BITVAL_CLAUSES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
    REAL_ARITH_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `cval:num` `\s. val(word_neg(read RCX s))` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN
    REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [5] (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; WORD_BITVAL_EQ_0;
                LOWDIGITS_CLAUSES; WORD_NEG_EQ_0; BITVAL_BOUND; NOT_LT] THEN
    REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[NOT_LT] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0;
             BITVAL_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
    REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2);

    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    X86_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
      ASSUME_TAC th)] THEN

  (*** Finally deduce that the lowest digit is 0 by congruence reasoning ***)

  UNDISCH_THEN
    `2 EXP 64 * (bitval carin + val(mulin:int64)) + r0 =
     q0 * bigdigit m 0 + bigdigit z1 0`
   (MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`) THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN
  UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[MOD_LT; GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
  CONV_TAC(LAND_CONV MOD_DOWN_CONV) THEN
  REWRITE_TAC[ARITH_RULE `(w * z1) * m + z1 = z1 * (m * w + 1)`] THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  UNDISCH_TAC `(m * w + 1 == 0) (mod (2 EXP 64))` THEN
  GEN_REWRITE_TAC LAND_CONV [CONG] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV MOD_DOWN_CONV) THEN
  REWRITE_TAC[MULT_CLAUSES; MOD_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN

  (*** The final congruence/range reasoning ***)

  FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
  MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `2 EXP 64` THEN
  ASM_REWRITE_TAC[COPRIME_LEXP; COPRIME_2] THEN
  REWRITE_TAC[GSYM EXP_ADD; ARITH_RULE `64 + 128 * k = 64 * (2 * k + 1)`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
   `(x:num == y) (mod n) ==> (z == x) (mod n) ==> (z == y) (mod n)`)) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
   `x:num = y + q * m ==> (z == x) (mod m) ==> (z == y) (mod m)`)) THEN
  MATCH_MP_TAC CONG_LMUL THEN
  SUBGOAL_THEN `cin <=> z2 < bitval cf * m` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `64 * k` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    UNDISCH_THEN
     `&(read (memory :> bytes (z,8 * k)) s2) =
      &2 pow (64 * k) * &(bitval cin) + &z2 - &(bitval cf) * &m`
     (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND; LE_0];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (vfree_in `cf:bool` o concl))) THEN
  REWRITE_TAC[GSYM int_of_num_th; GSYM int_pow_th; GSYM int_mul_th;
              GSYM int_add_th; GSYM int_sub_th; GSYM int_eq] THEN
  SIMP_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
  BOOL_CASES_TAC `cf:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT] THEN
  REWRITE_TAC[INT_CONG_REFL; INT_ADD_LID; INT_SUB_RZERO] THEN
  ASM_CASES_TAC `z2:num < m` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THENL
   [REPEAT(DISCH_THEN(K ALL_TAC)) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INTEGER_RULE;
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`)] THEN
  MATCH_MP_TAC(ARITH_RULE `b:num < a ==> ~(a = b)`) THEN
  MATCH_MP_TAC(ARITH_RULE
   `x + q * m < 2 EXP 64 * ee + 2 EXP 64 * m /\ ~(z2 < m)
    ==> x + q * m < 2 EXP 64 * (ee + z2)`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LET_ADD2 THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (MESON[ODD] `ODD m ==> ~(m = 0)`)) THEN
  ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `z1:num < ee ==> (h + 1) * ee <= b ==> ee * h + z1 <= b`)) THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ] THEN
  ASM_REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`]);;

let BIGNUM_AMONTIFIER_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!k z m t n pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (t,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),40))
            [(z,8 * val k); (t,8 * val k)] /\
        ALLPAIRS nonoverlapping [(z,8 * val k); (t,8 * val k);
                                 (word_sub stackpointer (word 32),32)]
                                [(word pc,LENGTH bignum_amontifier_tmc); (m,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_amontifier_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; m; t] s /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD n
                   ==> (bignum_from_memory (z,val k) s ==
                        2 EXP (128 * val k)) (mod n)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                         memory :> bytes(t,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_amontifier_tmc BIGNUM_AMONTIFIER_CORRECT
   `[RBX; RBP; R12; R13]` 32);;

let BIGNUM_AMONTIFIER_SUBROUTINE_CORRECT = time prove
 (`!k z m t n pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (t,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),40))
            [(z,8 * val k); (t,8 * val k)] /\
        ALLPAIRS nonoverlapping [(z,8 * val k); (t,8 * val k);
                                 (word_sub stackpointer (word 32),32)]
                                [(word pc,LENGTH bignum_amontifier_mc); (m,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_amontifier_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; m; t] s /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD n
                   ==> (bignum_from_memory (z,val k) s ==
                        2 EXP (128 * val k)) (mod n)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                         memory :> bytes(t,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_AMONTIFIER_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_amontifier_windows_mc = define_from_elf
   "bignum_amontifier_windows_mc" "x86/generic/bignum_amontifier.obj";;

let bignum_amontifier_windows_tmc = define_trimmed "bignum_amontifier_windows_tmc" bignum_amontifier_windows_mc;;

let BIGNUM_AMONTIFIER_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z m t n pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (t,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),56))
            [(z,8 * val k); (t,8 * val k)] /\
        ALLPAIRS nonoverlapping [(z,8 * val k); (t,8 * val k);
                                 (word_sub stackpointer (word 48),48)]
                                [(word pc,LENGTH bignum_amontifier_windows_tmc); (m,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_amontifier_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; m; t] s /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD n
                   ==> (bignum_from_memory (z,val k) s ==
                        2 EXP (128 * val k)) (mod n)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                         memory :> bytes(t,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_amontifier_windows_tmc bignum_amontifier_tmc
    BIGNUM_AMONTIFIER_CORRECT `[RBX; RBP; R12; R13]` 32);;

let BIGNUM_AMONTIFIER_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z m t n pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (t,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),56))
            [(z,8 * val k); (t,8 * val k)] /\
        ALLPAIRS nonoverlapping [(z,8 * val k); (t,8 * val k);
                                 (word_sub stackpointer (word 48),48)]
                                [(word pc,LENGTH bignum_amontifier_windows_mc); (m,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_amontifier_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; m; t] s /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD n
                   ==> (bignum_from_memory (z,val k) s ==
                        2 EXP (128 * val k)) (mod n)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                         memory :> bytes(t,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_AMONTIFIER_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

