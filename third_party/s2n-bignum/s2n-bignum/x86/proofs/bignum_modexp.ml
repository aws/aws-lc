(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Modular exponentiation for bignums (with odd modulus).                    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_modexp.o";;
 ****)

let bignum_modexp_mc =
  define_assert_from_elf "bignum_modexp_mc" "x86/generic/bignum_modexp.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x83; 0xec; 0x48;  (* SUB (% rsp) (Imm8 (word 72)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x0f; 0x84; 0x40; 0x01; 0x00; 0x00;
                           (* JE (Imm32 (word 320)) *)
  0x48; 0x89; 0x3c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rdi) *)
  0x48; 0x89; 0x74; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rsi) *)
  0x48; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rdx) *)
  0x48; 0x89; 0x4c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r9) *)
  0x49; 0x8d; 0x04; 0xf9;  (* LEA (% rax) (%%% (r9,3,rdi)) *)
  0x48; 0x89; 0x44; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rax) *)
  0x48; 0x8d; 0x04; 0xf8;  (* LEA (% rax) (%%% (rax,3,rdi)) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x48; 0x8b; 0x3c; 0x24;  (* MOV (% rdi) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x74; 0x24; 0x40;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x54; 0x24; 0x20;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x38;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,56))) *)
  0xe8; 0xfe; 0x00; 0x00; 0x00;
                           (* CALL (Imm32 (word 254)) *)
  0x48; 0x8b; 0x3c; 0x24;  (* MOV (% rdi) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x74; 0x24; 0x28;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x8b; 0x54; 0x24; 0x40;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x10;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,32))) *)
  0xe8; 0x08; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1032)) *)
  0x48; 0x8b; 0x3c; 0x24;  (* MOV (% rdi) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x74; 0x24; 0x40;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x54; 0x24; 0x40;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x20;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,32))) *)
  0xe8; 0x4e; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1358)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xc1; 0xe0; 0x06;  (* SHL (% rax) (Imm8 (word 6)) *)
  0x48; 0x89; 0x44; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rax) *)
  0x48; 0x83; 0xe8; 0x01;  (* SUB (% rax) (Imm8 (word 1)) *)
  0x48; 0x89; 0x44; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rax) *)
  0x48; 0x8b; 0x3c; 0x24;  (* MOV (% rdi) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x74; 0x24; 0x38;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8b; 0x54; 0x24; 0x40;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x40;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,32))) *)
  0xe8; 0xbd; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 957)) *)
  0x48; 0x8b; 0x3c; 0x24;  (* MOV (% rdi) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x74; 0x24; 0x40;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x54; 0x24; 0x28;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x38;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,32))) *)
  0xe8; 0xa0; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 928)) *)
  0x48; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xc1; 0xea; 0x06;  (* SHR (% rdx) (Imm8 (word 6)) *)
  0x48; 0x8b; 0x74; 0x24; 0x18;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x8b; 0x3c; 0xd6;  (* MOV (% rdi) (Memop Quadword (%%% (rsi,3,rdx))) *)
  0x48; 0xd3; 0xef;        (* SHR (% rdi) (% cl) *)
  0x48; 0x83; 0xe7; 0x01;  (* AND (% rdi) (Imm8 (word 1)) *)
  0x48; 0x8b; 0x34; 0x24;  (* MOV (% rsi) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x54; 0x24; 0x40;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x40;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,56))) *)
  0xe8; 0xe0; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1504)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x85; 0xc0;        (* TEST (% rax) (% rax) *)
  0x0f; 0x85; 0x7b; 0xff; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294967163)) *)
  0x48; 0x8b; 0x3c; 0x24;  (* MOV (% rdi) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x74; 0x24; 0x40;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x54; 0x24; 0x40;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x20;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,32))) *)
  0xe8; 0xa4; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1188)) *)
  0x31; 0xff;              (* XOR (% edi) (% edi) *)
  0x48; 0x8b; 0x34; 0x24;  (* MOV (% rsi) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x54; 0x24; 0x08;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x40;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,64))) *)
  0xe8; 0xa0; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1440)) *)
  0x48; 0x83; 0xc4; 0x48;  (* ADD (% rsp) (Imm8 (word 72)) *)
  0xc3;                    (* RET *)
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
  0xc3;                    (* RET *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x83; 0xec; 0x08;  (* SUB (% rsp) (Imm8 (word 8)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x0f; 0x84; 0x38; 0x01; 0x00; 0x00;
                           (* JE (Imm32 (word 312)) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x49; 0x8b; 0x00;        (* MOV (% rax) (Memop Quadword (%% (r8,0))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xc1; 0xe2; 0x02;  (* SHL (% rdx) (Imm8 (word 2)) *)
  0x48; 0x29; 0xd3;        (* SUB (% rbx) (% rdx) *)
  0x48; 0x83; 0xf3; 0x02;  (* XOR (% rbx) (Imm8 (word 2)) *)
  0x48; 0x89; 0xda;        (* MOV (% rdx) (% rbx) *)
  0x48; 0x0f; 0xaf; 0xd0;  (* IMUL (% rdx) (% rax) *)
  0xb8; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 2)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x48; 0x83; 0xc2; 0x01;  (* ADD (% rdx) (Imm8 (word 1)) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x48; 0x0f; 0xaf; 0xd2;  (* IMUL (% rdx) (% rdx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x48; 0x0f; 0xaf; 0xd2;  (* IMUL (% rdx) (% rdx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x48; 0x0f; 0xaf; 0xd2;  (* IMUL (% rdx) (% rdx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x48; 0x89; 0x1c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rbx) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x4c; 0x89; 0x2c; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,rbx))) (% r13) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x48; 0x39; 0xfb;        (* CMP (% rbx) (% rdi) *)
  0x72; 0xf4;              (* JB (Imm8 (word 244)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x4b; 0x8b; 0x2c; 0xe9;  (* MOV (% rbp) (Memop Quadword (%%% (r9,3,r13))) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x49; 0x89; 0xfc;        (* MOV (% r12) (% rdi) *)
  0x4c; 0x13; 0x14; 0xde;  (* ADC (% r10) (Memop Quadword (%%% (rsi,3,rbx))) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x04; 0xd9;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,rbx))) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x48; 0x89; 0x04; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,rbx))) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x49; 0xff; 0xcc;        (* DEC (% r12) *)
  0x75; 0xdd;              (* JNE (Imm8 (word 221)) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x4c; 0x8b; 0x1e;        (* MOV (% r11) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x8b; 0x2c; 0x24;  (* MOV (% rbp) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x0f; 0xaf; 0xeb;  (* IMUL (% rbp) (% r11) *)
  0x49; 0x8b; 0x00;        (* MOV (% rax) (Memop Quadword (%% (r8,0))) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0xbb; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 1)) *)
  0x49; 0x89; 0xfc;        (* MOV (% r12) (% rdi) *)
  0x49; 0xff; 0xcc;        (* DEC (% r12) *)
  0x74; 0x24;              (* JE (Imm8 (word 36)) *)
  0x4c; 0x13; 0x14; 0xde;  (* ADC (% r10) (Memop Quadword (%%% (rsi,3,rbx))) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x49; 0x8b; 0x04; 0xd8;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,rbx))) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x48; 0x89; 0x44; 0xde; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsi,3,rbx,-- &8))) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x49; 0xff; 0xcc;        (* DEC (% r12) *)
  0x75; 0xdc;              (* JNE (Imm8 (word 220)) *)
  0x4d; 0x11; 0xf2;        (* ADC (% r10) (% r14) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x4d; 0x89; 0xfe;        (* MOV (% r14) (% r15) *)
  0x4c; 0x89; 0x54; 0xde; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsi,3,rbx,-- &8))) (% r10) *)
  0x49; 0xff; 0xc5;        (* INC (% r13) *)
  0x49; 0x39; 0xfd;        (* CMP (% r13) (% rdi) *)
  0x0f; 0x82; 0x64; 0xff; 0xff; 0xff;
                           (* JB (Imm32 (word 4294967140)) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x4c; 0x29; 0xf5;        (* SUB (% rbp) (% r14) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x49; 0x8b; 0x04; 0xd8;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,rbx))) *)
  0x48; 0x21; 0xe8;        (* AND (% rax) (% rbp) *)
  0x49; 0xf7; 0xdb;        (* NEG (% r11) *)
  0x48; 0x19; 0x04; 0xde;  (* SBB (Memop Quadword (%%% (rsi,3,rbx))) (% rax) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x48; 0x39; 0xfb;        (* CMP (% rbx) (% rdi) *)
  0x72; 0xe7;              (* JB (Imm8 (word 231)) *)
  0x48; 0x83; 0xc4; 0x08;  (* ADD (% rsp) (Imm8 (word 8)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x0f; 0x84; 0x04; 0x01; 0x00; 0x00;
                           (* JE (Imm32 (word 260)) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0xc1; 0xe3; 0x02;  (* SHL (% rbx) (Imm8 (word 2)) *)
  0x49; 0x29; 0xd8;        (* SUB (% r8) (% rbx) *)
  0x49; 0x83; 0xf0; 0x02;  (* XOR (% r8) (Imm8 (word 2)) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0xb8; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 2)) *)
  0x48; 0x01; 0xd8;        (* ADD (% rax) (% rbx) *)
  0x48; 0x83; 0xc3; 0x01;  (* ADD (% rbx) (Imm8 (word 1)) *)
  0x4c; 0x0f; 0xaf; 0xc0;  (* IMUL (% r8) (% rax) *)
  0x48; 0x0f; 0xaf; 0xdb;  (* IMUL (% rbx) (% rbx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd8;        (* ADD (% rax) (% rbx) *)
  0x4c; 0x0f; 0xaf; 0xc0;  (* IMUL (% r8) (% rax) *)
  0x48; 0x0f; 0xaf; 0xdb;  (* IMUL (% rbx) (% rbx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd8;        (* ADD (% rax) (% rbx) *)
  0x4c; 0x0f; 0xaf; 0xc0;  (* IMUL (% r8) (% rax) *)
  0x48; 0x0f; 0xaf; 0xdb;  (* IMUL (% rbx) (% rbx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd8;        (* ADD (% rax) (% rbx) *)
  0x4c; 0x0f; 0xaf; 0xc0;  (* IMUL (% r8) (% rax) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x48; 0x8b; 0x04; 0xda;  (* MOV (% rax) (Memop Quadword (%%% (rdx,3,rbx))) *)
  0x48; 0x89; 0x04; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,rbx))) (% rax) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x48; 0x39; 0xfb;        (* CMP (% rbx) (% rdi) *)
  0x72; 0xf0;              (* JB (Imm8 (word 240)) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4c; 0x8b; 0x1e;        (* MOV (% r11) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x89; 0xc5;        (* MOV (% rbp) (% r8) *)
  0x49; 0x0f; 0xaf; 0xeb;  (* IMUL (% rbp) (% r11) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0xbb; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 1)) *)
  0x49; 0x89; 0xfc;        (* MOV (% r12) (% rdi) *)
  0x49; 0xff; 0xcc;        (* DEC (% r12) *)
  0x74; 0x24;              (* JE (Imm8 (word 36)) *)
  0x4c; 0x13; 0x14; 0xde;  (* ADC (% r10) (Memop Quadword (%%% (rsi,3,rbx))) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x04; 0xd9;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,rbx))) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x48; 0x89; 0x44; 0xde; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsi,3,rbx,-- &8))) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x49; 0xff; 0xcc;        (* DEC (% r12) *)
  0x75; 0xdc;              (* JNE (Imm8 (word 220)) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x54; 0xde; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsi,3,rbx,-- &8))) (% r10) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xf9;        (* CMP (% r9) (% rdi) *)
  0x72; 0xa8;              (* JB (Imm8 (word 168)) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x49; 0x89; 0xfc;        (* MOV (% r12) (% rdi) *)
  0x48; 0x8b; 0x04; 0xde;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,rbx))) *)
  0x48; 0x1b; 0x04; 0xd9;  (* SBB (% rax) (Memop Quadword (%%% (rcx,3,rbx))) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x49; 0xff; 0xcc;        (* DEC (% r12) *)
  0x75; 0xf0;              (* JNE (Imm8 (word 240)) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0xf7; 0xd5;        (* NOT (% rbp) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x48; 0x8b; 0x04; 0xd9;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,rbx))) *)
  0x48; 0x21; 0xe8;        (* AND (% rax) (% rbp) *)
  0x49; 0xf7; 0xdb;        (* NEG (% r11) *)
  0x48; 0x19; 0x04; 0xde;  (* SBB (Memop Quadword (%%% (rsi,3,rbx))) (% rax) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x48; 0x39; 0xfb;        (* CMP (% rbx) (% rdi) *)
  0x72; 0xe7;              (* JB (Imm8 (word 231)) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x74; 0x1e;              (* JE (Imm8 (word 30)) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0xf7; 0xdf;        (* NEG (% rdi) *)
  0x4a; 0x8b; 0x04; 0xc9;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r9))) *)
  0x4b; 0x8b; 0x3c; 0xc8;  (* MOV (% rdi) (Memop Quadword (%%% (r8,3,r9))) *)
  0x48; 0x0f; 0x43; 0xc7;  (* CMOVAE (% rax) (% rdi) *)
  0x4a; 0x89; 0x04; 0xca;  (* MOV (Memop Quadword (%%% (rdx,3,r9))) (% rax) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x75; 0xe8;              (* JNE (Imm8 (word 232)) *)
  0xc3                     (* RET *)
];;

let bignum_modexp_tmc = define_trimmed "bignum_modexp_tmc" bignum_modexp_mc;;

let BIGNUM_MODEXP_EXEC = X86_MK_EXEC_RULE bignum_modexp_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness for the subroutines                                           *)
(* ------------------------------------------------------------------------- *)

let X86_CASEWISE_SUBROUTINE_SIM_ABBREV_TAC (mc,ex,d,smc,cth) ins outs s n =
  let ths = CONJUNCTS
    (REWRITE_RULE[LEFT_OR_DISTRIB; RIGHT_OR_DISTRIB; FORALL_AND_THM;
                  TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] cth) in
  MAP_FIRST (fun th g ->
     X86_SUBROUTINE_SIM_ABBREV_TAC (mc,ex,d,smc,th) ins outs s n g) ths;;

needs "x86/proofs/bignum_amontifier.ml";;

let LOCAL_AMONTIFIER_TAC =
  let baseth = X86_SIMD_SHARPEN_RULE BIGNUM_AMONTIFIER_NOIBT_SUBROUTINE_CORRECT
   (X86_PROMOTE_RETURN_STACK_TAC bignum_amontifier_tmc BIGNUM_AMONTIFIER_CORRECT
    `[RBX; RBP; R12; R13]` 32) in
  fun s n -> X86_SUBROUTINE_SIM_ABBREV_TAC
    (bignum_modexp_tmc,BIGNUM_MODEXP_EXEC,
     0x152,bignum_amontifier_tmc,baseth)
    [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
     `read (memory :> bytes(read RDX s,8 * k)) s`;
     `pc + 0x152`; `read RSP s`;
     `read (memory :> bytes64(read RSP s)) s`]
    `read (memory :> bytes(word_add t (word(16 * k)),8 * k)) s'` s n;;

needs "x86/proofs/bignum_amontmul.ml";;

let LOCAL_AMONTMUL_TAC =
  let baseth = X86_SIMD_SHARPEN_RULE BIGNUM_AMONTMUL_NOIBT_SUBROUTINE_CORRECT
  (X86_PROMOTE_RETURN_STACK_TAC
    bignum_amontmul_tmc BIGNUM_AMONTMUL_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 56) in
  fun s n -> X86_SUBROUTINE_SIM_ABBREV_TAC
    (bignum_modexp_tmc,BIGNUM_MODEXP_EXEC,
     0x479,bignum_amontmul_tmc,baseth)
    [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
     `read (memory :> bytes(read RDX s,8 * k)) s`;
     `read (memory :> bytes(read RCX s,8 * k)) s`;
     `read (memory :> bytes(read R8 s,8 * k)) s`;
     `pc + 0x479`; `read RSP s`;
     `read (memory :> bytes64(read RSP s)) s`]
    `read (memory :> bytes(read RSI s,8 * k)) s'` s n;;

needs "x86/proofs/bignum_demont.ml";;

let LOCAL_DEMONT_TAC =
  let baseth = X86_SIMD_SHARPEN_RULE BIGNUM_DEMONT_NOIBT_SUBROUTINE_CORRECT
  (X86_PROMOTE_RETURN_STACK_TAC bignum_demont_tmc BIGNUM_DEMONT_CORRECT
   `[RBX; RBP; R12]` 24) in
  fun s n -> X86_CASEWISE_SUBROUTINE_SIM_ABBREV_TAC
    (bignum_modexp_tmc,BIGNUM_MODEXP_EXEC,
     0x5d7,bignum_demont_tmc,baseth)
    [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
     `read (memory :> bytes(read RDX s,8 * k)) s`;
     `read (memory :> bytes(read RCX s,8 * k)) s`;
     `pc + 0x5d7`; `read RSP s`;
     `read (memory :> bytes64(read RSP s)) s`]
    `read (memory :> bytes(read RSI s,8 * k)) s'` s n;;

needs "x86/proofs/bignum_mux.ml";;

let LOCAL_MUX_TAC =
  let baseth = X86_SIMD_SHARPEN_RULE BIGNUM_MUX_NOIBT_SUBROUTINE_CORRECT
  (X86_PROMOTE_RETURN_NOSTACK_TAC bignum_mux_tmc BIGNUM_MUX_CORRECT) in
  fun s n -> X86_CASEWISE_SUBROUTINE_SIM_ABBREV_TAC
    (bignum_modexp_tmc,BIGNUM_MODEXP_EXEC,
     0x6ed,bignum_mux_tmc,baseth)
    [`read RDI s`; `read RSI s`; `read RCX s`; `read R8 s`; `read RDX s`;
     `read (memory :> bytes(read RCX s,8 * k)) s`;
     `read (memory :> bytes(read R8 s,8 * k)) s`;
     `pc + 0x6ed`; `read RSP s`;
     `read (memory :> bytes64(read RSP s)) s`]
    `read (memory :> bytes(read RDX s,8 * k)) s'` s n;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODEXP_CORRECT = prove
 (`!k z a x p y m n t pc stackpointer.
     val k < 2 EXP 58 /\
     ALL (nonoverlapping (word_sub stackpointer (word 64),136))
         [(word pc,0x711); (z,8 * val k); (t,24 * val k);
          (a,8 * val k); (p,8 * val k); (m,8 * val k)] /\
     ALL (nonoverlapping (word pc,0x711)) [(z,8 * val k); (t,24 * val k)] /\
     ALL (nonoverlapping (t,24 * val k))
         [(z,8 * val k); (a,8 * val k); (p,8 * val k); (m,8 * val k)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_modexp_tmc /\
               read RIP s = word(pc + 0x4) /\
               read RSP s = stackpointer /\
               C_ARGUMENTS [k; z; a; p; m; t] s /\
               bignum_from_memory(a,val k) s = x /\
               bignum_from_memory(p,val k) s = y /\
               bignum_from_memory(m,val k) s = n)
          (\s. read RIP s = word (pc + 0x14d) /\
               (ODD n ==> bignum_from_memory(z,val k) s = (x EXP y) MOD n))
          (MAYCHANGE [RIP] ,,
           MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
           MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(t,24 * val k);
                      memory :> bytes(word_sub stackpointer (word 64),136)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `a:int64`; `x:num`; `p:int64`; `y:num`;
    `m:int64`; `n:num`; `t:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN X_GEN_TAC `stackpointer:int64` THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`x:num`; `y:num`; `n:num`] THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN

  (*** Deal with degenerate case k = 0 first ***)

  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [X86_SIM_TAC BIGNUM_MODEXP_EXEC (1--2) THEN EXPAND_TAC "n" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; ODD];
    ALL_TAC] THEN

  (*** Setup of the main outer loop ***)

  ENSURES_WHILE_DOWN_TAC `64 * k` `pc + 0x96` `pc + 0x112`
   `\i s. read RSP s = word_add stackpointer (word 64) /\
          read (memory :> bytes64(word_add stackpointer (word 64))) s =
          word k /\
          read (memory :> bytes64(word_add stackpointer (word 72))) s = z /\
          read (memory :> bytes64(word_add stackpointer (word 80))) s = a /\
          read (memory :> bytes64(word_add stackpointer (word 88))) s = p /\
          read (memory :> bytes64(word_add stackpointer (word 96))) s = m /\
          read (memory :> bytes64(word_add stackpointer (word 104))) s = t /\
          read RAX s = word i /\
          read (memory :> bytes64(word_add stackpointer (word 120))) s =
          word_add t (word(8 * k)) /\
          read (memory :> bytes64(word_add stackpointer (word 128))) s =
          word_add t (word(16 * k)) /\
          bignum_from_memory(a,k) s = x /\
          bignum_from_memory(p,k) s = y /\
          bignum_from_memory(m,k) s = n /\
          (ODD n
           ==> (bignum_from_memory(word_add t (word(16 * k)),k) s ==
                2 EXP (64 * k) * x EXP (y DIV 2 EXP i)) (mod n) /\
               (bignum_from_memory(t,k) s ==
                2 EXP (64 * k) * x) (mod n))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ];

    (*** Initialization ***)

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (1--12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [WORD_RULE `word_add (word_add t (word (8 * k))) (word (8 * k)) =
                 word_add t (word(16 * k))`]) THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (13--17) THEN
    LOCAL_AMONTIFIER_TAC "z2" 18 THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (19--24) THEN
    LOCAL_AMONTMUL_TAC "z1" 25 THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (26--30) THEN
    LOCAL_DEMONT_TAC "z0" 31 THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (32--34) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DIV_LT; EXP] THEN
    REWRITE_TAC[ARITH_RULE `128 * k = 64 * k + 64 * k`; EXP_ADD] THEN
    MP_TAC(SPECL [`n:num`; `2 EXP (64 * k)`] INVERSE_MOD_LMUL) THEN
    ASM_REWRITE_TAC[COPRIME_REXP; COPRIME_2; CONG_LMOD] THEN
    CONV_TAC NUMBER_RULE;

    (*** Main loop invariant ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `x1:num` `bignum_from_memory(t,k)` THEN
    GHOST_INTRO_TAC `xn:num`
     `bignum_from_memory (word_add t (word(16 * k)),k)` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (1--8) THEN
    LOCAL_AMONTMUL_TAC "xn2" 9 THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (10--15) THEN
    LOCAL_AMONTMUL_TAC "xxn2" 16 THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [WORD_RULE `word_sub (word (i + 1)) (word 1) = word i`]) THEN
    SUBGOAL_THEN
     `read(memory :> bytes64
      (word_add p (word(8 * val(word_ushr (word i:int64) 6))))) s16 =
      word(y DIV (2 EXP (64 * i DIV 64)) MOD 2 EXP (64 * 1))`
    ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 64 * k ==> MIN (k - i DIV 64) 1 = 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
      VAL_INT64_TAC `i:num` THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (17--23) THEN
    SUBGOAL_THEN
     `word_and
        (word_ushr (word((y DIV 2 EXP (64 * i DIV 64)) MOD 2 EXP 64))
        (val (word(val (word i:int64) MOD 256):byte) MOD 64))
        (word 1:int64) =
      word(bitval(ODD(y DIV 2 EXP i)))`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[WORD_AND_1_BITVAL; MOD_64_CLAUSES] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[BIT_LSB; VAL_WORD_USHR] THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
      REWRITE_TAC[DIV_MOD; DIV_DIV; GSYM EXP_ADD] THEN
      REWRITE_TAC[ARITH_RULE `64 * i DIV 64 + i MOD 64 = i`] THEN
      REWRITE_TAC[ARITH_RULE `64 * i DIV 64 + 64 = i + (64 - i MOD 64)`] THEN
      REWRITE_TAC[EXP_ADD; GSYM DIV_MOD; ODD_MOD_POW2] THEN
      MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (24--28) THEN
    LOCAL_MUX_TAC "xmux" 29 THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC [30] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    ASM_REWRITE_TAC[WORD_BITVAL_EQ_0] THEN
    ABBREV_TAC `yi = y DIV 2 EXP (i + 1)` THEN
    ABBREV_TAC `b = ODD(y DIV 2 EXP i)` THEN
    SUBGOAL_THEN `y DIV 2 EXP i = yi + yi + bitval b` SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["b"; "yi"] THEN
      REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; BITVAL_ODD] THEN ARITH_TAC;
      SIMP_TAC[BITVAL_CLAUSES; ADD_CLAUSES; COND_ID]] THEN
    BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[EXP_ADD; EXP_1] THEN
    MP_TAC(SPECL [`n:num`; `2 EXP (64 * k)`] INVERSE_MOD_LMUL) THEN
    ASM_REWRITE_TAC[COPRIME_REXP; COPRIME_2; CONG_LMOD] THEN
    CONV_TAC NUMBER_RULE;

    (*** The trivial loop-back goal ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_MODEXP_EXEC (1--2);

    (*** The finale ***)

    GHOST_INTRO_TAC `xn:num`
     `bignum_from_memory (word_add t (word(16 * k)),k)` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (1--7) THEN
    LOCAL_DEMONT_TAC "z'" 8 THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (9--14) THEN
    LOCAL_MUX_TAC "res" 15 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    ASM_REWRITE_TAC[EXP; DIV_1] THEN SIMP_TAC[GSYM CONG] THEN
    MP_TAC(SPECL [`n:num`; `2 EXP (64 * k)`] INVERSE_MOD_LMUL) THEN
    ASM_REWRITE_TAC[COPRIME_REXP; COPRIME_2] THEN CONV_TAC NUMBER_RULE]);;

let BIGNUM_MODEXP_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z a x p y m n t pc stackpointer returnaddress.
     val k < 2 EXP 58 /\
     ALL (nonoverlapping (word_sub stackpointer (word 136),144))
         [(word pc,LENGTH bignum_modexp_tmc); (z,8 * val k); (t,24 * val k);
          (a,8 * val k); (p,8 * val k); (m,8 * val k)] /\
     ALL (nonoverlapping (word pc,LENGTH bignum_modexp_tmc)) [(z,8 * val k); (t,24 * val k)] /\
     ALL (nonoverlapping (t,24 * val k))
         [(z,8 * val k); (a,8 * val k); (p,8 * val k); (m,8 * val k)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_modexp_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [k; z; a; p; m; t] s /\
               bignum_from_memory(a,val k) s = x /\
               bignum_from_memory(p,val k) s = y /\
               bignum_from_memory(m,val k) s = n)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (ODD n ==> bignum_from_memory(z,val k) s = (x EXP y) MOD n))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(t,24 * val k);
                      memory :> bytes(word_sub stackpointer (word 136),136)])`,
  MP_TAC BIGNUM_MODEXP_CORRECT THEN
  REWRITE_TAC[fst BIGNUM_MODEXP_EXEC] THEN
  REPLICATE_TAC 10 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC 136 THEN
                       X_GEN_TAC `sptr:int64` THEN GEN_TAC THEN
                       MP_TAC(SPEC `word_add sptr (word 64):int64` th)) THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add x y) y = x`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC [1] THEN MP_TAC th THEN
    X86_BIGSTEP_TAC BIGNUM_MODEXP_EXEC "s2" THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    X86_STEPS_TAC BIGNUM_MODEXP_EXEC (3--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]));;

let BIGNUM_MODEXP_SUBROUTINE_CORRECT = prove
 (`!k z a x p y m n t pc stackpointer returnaddress.
     val k < 2 EXP 58 /\
     ALL (nonoverlapping (word_sub stackpointer (word 136),144))
         [(word pc,LENGTH bignum_modexp_mc); (z,8 * val k); (t,24 * val k);
          (a,8 * val k); (p,8 * val k); (m,8 * val k)] /\
     ALL (nonoverlapping (word pc,LENGTH bignum_modexp_mc)) [(z,8 * val k); (t,24 * val k)] /\
     ALL (nonoverlapping (t,24 * val k))
         [(z,8 * val k); (a,8 * val k); (p,8 * val k); (m,8 * val k)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_modexp_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [k; z; a; p; m; t] s /\
               bignum_from_memory(a,val k) s = x /\
               bignum_from_memory(p,val k) s = y /\
               bignum_from_memory(m,val k) s = n)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (ODD n ==> bignum_from_memory(z,val k) s = (x EXP y) MOD n))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(t,24 * val k);
                      memory :> bytes(word_sub stackpointer (word 136),136)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODEXP_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_modexp_windows_mc = define_from_elf
   "bignum_modexp_windows_mc" "x86/generic/bignum_modexp.obj";;

let bignum_modexp_windows_tmc = define_trimmed "bignum_modexp_windows_tmc" bignum_modexp_windows_mc;;

let BIGNUM_MODEXP_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z a x p y m n t pc stackpointer returnaddress.
     val k < 2 EXP 58 /\
     ALL (nonoverlapping (word_sub stackpointer (word 160),168))
         [(word pc,LENGTH bignum_modexp_windows_tmc); (z,8 * val k); (t,24 * val k);
          (a,8 * val k); (p,8 * val k); (m,8 * val k)] /\
     ALL (nonoverlapping (word pc,LENGTH bignum_modexp_windows_tmc)) [(z,8 * val k); (t,24 * val k)] /\
     ALL (nonoverlapping (t,24 * val k))
         [(z,8 * val k); (a,8 * val k); (p,8 * val k); (m,8 * val k)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_modexp_windows_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [k; z; a; p; m; t] s /\
               bignum_from_memory(a,val k) s = x /\
               bignum_from_memory(p,val k) s = y /\
               bignum_from_memory(m,val k) s = n)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (ODD n ==> bignum_from_memory(z,val k) s = (x EXP y) MOD n))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(t,24 * val k);
                      memory :> bytes(word_sub stackpointer (word 160),160)])`,
  let WINDOWS_BIGNUM_MODEXP_EXEC =
    X86_MK_EXEC_RULE bignum_modexp_windows_tmc
  and subth =
    X86_SIMD_SHARPEN_RULE
    (REWRITE_RULE[fst BIGNUM_MODEXP_EXEC]
      BIGNUM_MODEXP_NOIBT_SUBROUTINE_CORRECT)
    (MP_TAC BIGNUM_MODEXP_CORRECT THEN
     REPLICATE_TAC 10 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
     DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC 136 THEN
                          X_GEN_TAC `sptr:int64` THEN GEN_TAC THEN
                          MP_TAC(SPEC `word_add sptr (word 64):int64` th)) THEN
     REWRITE_TAC[WORD_RULE `word_sub (word_add x y) y = x`] THEN
     REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
     REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
     DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
      [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
     DISCH_THEN(fun th ->
       REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
       X86_STEPS_TAC BIGNUM_MODEXP_EXEC [1] THEN MP_TAC th THEN
       X86_BIGSTEP_TAC BIGNUM_MODEXP_EXEC "s2" THEN
       REWRITE_TAC(!simulation_precanon_thms) THEN
       X86_STEPS_TAC BIGNUM_MODEXP_EXEC (3--4) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[])) in
  REWRITE_TAC[fst WINDOWS_BIGNUM_MODEXP_EXEC] THEN
  REPLICATE_TAC 10 GEN_TAC THEN WORD_FORALL_OFFSET_TAC 160 THEN
  REWRITE_TAC[ALL; WINDOWS_C_ARGUMENTS; SOME_FLAGS;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  UNDISCH_THEN `read RSP s0 = word_add stackpointer (word 160)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  RULE_ASSUM_TAC
   (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  X86_STEPS_TAC WINDOWS_BIGNUM_MODEXP_EXEC (1--9) THEN
  X86_SUBROUTINE_SIM_TAC
   (bignum_modexp_windows_tmc,
    WINDOWS_BIGNUM_MODEXP_EXEC,
    0x20,bignum_modexp_tmc,subth)
   [`read RDI s`; `read RSI s`;
    `read RDX s`; `read (memory :> bytes(read RDX s,8 * val(k:int64))) s`;
    `read RCX s`; `read (memory :> bytes(read RCX s,8 * val(k:int64))) s`;
    `read R8 s`; `read (memory :> bytes(read R8 s,8 * val(k:int64))) s`;
    `read R9 s`; `pc + 0x20`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`] 10 THEN
  X86_STEPS_TAC WINDOWS_BIGNUM_MODEXP_EXEC (11--13) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let BIGNUM_MODEXP_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z a x p y m n t pc stackpointer returnaddress.
     val k < 2 EXP 58 /\
     ALL (nonoverlapping (word_sub stackpointer (word 160),168))
         [(word pc,LENGTH bignum_modexp_windows_mc); (z,8 * val k); (t,24 * val k);
          (a,8 * val k); (p,8 * val k); (m,8 * val k)] /\
     ALL (nonoverlapping (word pc,LENGTH bignum_modexp_windows_mc)) [(z,8 * val k); (t,24 * val k)] /\
     ALL (nonoverlapping (t,24 * val k))
         [(z,8 * val k); (a,8 * val k); (p,8 * val k); (m,8 * val k)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_modexp_windows_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [k; z; a; p; m; t] s /\
               bignum_from_memory(a,val k) s = x /\
               bignum_from_memory(p,val k) s = y /\
               bignum_from_memory(m,val k) s = n)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (ODD n ==> bignum_from_memory(z,val k) s = (x EXP y) MOD n))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(t,24 * val k);
                      memory :> bytes(word_sub stackpointer (word 160),160)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODEXP_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

