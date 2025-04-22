(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 6-word (384-bit) bignum to Montgomery form modulo p_384.  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p384/bignum_tomont_p384_alt.o";;
 ****)

let bignum_tomont_p384_alt_mc =
  define_assert_from_elf "bignum_tomont_p384_alt_mc" "x86/p384/bignum_tomont_p384_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0xbb; 0x01; 0x00; 0x00; 0x00; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rbx) (Imm64 (word 18446744065119617025)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc3;        (* ADD (% rbx) (% r8) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc9;              (* ADC (% ecx) (% ecx) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xde;        (* ADD (% r14) (% rbx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 8589934592)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x49; 0xf7; 0xd8;        (* NEG (% r8) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xcb;        (* ADD (% rbx) (% r9) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xc8;        (* ADD (% rax) (% r9) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc9;              (* ADC (% ecx) (% ecx) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xcc;        (* SBB (% r12) (% rcx) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xdf;        (* ADD (% r15) (% rbx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rbx) (Imm64 (word 18446744065119617024)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x4c; 0x89; 0xd3;        (* MOV (% rbx) (% r10) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd3;        (* ADD (% rbx) (% r10) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc9;              (* ADC (% ecx) (% ecx) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x49; 0x19; 0xcd;        (* SBB (% r13) (% rcx) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd8;        (* ADD (% r8) (% rbx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 8589934592)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x49; 0xf7; 0xda;        (* NEG (% r10) *)
  0x4c; 0x89; 0xdb;        (* MOV (% rbx) (% r11) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xdb;        (* ADD (% rbx) (% r11) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc9;              (* ADC (% ecx) (% ecx) *)
  0x49; 0x29; 0xc4;        (* SUB (% r12) (% rax) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x49; 0x19; 0xce;        (* SBB (% r14) (% rcx) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd9;        (* ADD (% r9) (% rbx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4c; 0x03; 0x26;        (* ADD (% r12) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x13; 0x6e; 0x08;  (* ADC (% r13) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x13; 0x76; 0x10;  (* ADC (% r14) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x13; 0x7e; 0x18;  (* ADC (% r15) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x13; 0x46; 0x20;  (* ADC (% r8) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x13; 0x4e; 0x28;  (* ADC (% r9) (Memop Quadword (%% (rsi,40))) *)
  0x4d; 0x11; 0xda;        (* ADC (% r10) (% r11) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe3;        (* ADD (% rbx) (% r12) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xe0;        (* ADD (% rax) (% r12) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc9;              (* ADC (% ecx) (% ecx) *)
  0x49; 0x29; 0xc5;        (* SUB (% r13) (% rax) *)
  0x49; 0x19; 0xd6;        (* SBB (% r14) (% rdx) *)
  0x49; 0x19; 0xcf;        (* SBB (% r15) (% rcx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xda;        (* ADD (% r10) (% rbx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xeb;        (* ADD (% rbx) (% r13) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xe8;        (* ADD (% rax) (% r13) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc9;              (* ADC (% ecx) (% ecx) *)
  0x49; 0x29; 0xc6;        (* SUB (% r14) (% rax) *)
  0x49; 0x19; 0xd7;        (* SBB (% r15) (% rdx) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xdb;        (* ADD (% r11) (% rbx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xbe; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 1)) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0x11; 0xc8;        (* ADC (% rax) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x11; 0xf0;        (* ADC (% rax) (% rsi) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0xf7; 0xdc;        (* NEG (% r12) *)
  0x4c; 0x21; 0xe2;        (* AND (% rdx) (% r12) *)
  0x4c; 0x21; 0xe1;        (* AND (% rcx) (% r12) *)
  0x4c; 0x21; 0xe6;        (* AND (% rsi) (% r12) *)
  0x49; 0x01; 0xd6;        (* ADD (% r14) (% rdx) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x49; 0x11; 0xf0;        (* ADC (% r8) (% rsi) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x37;        (* MOV (Memop Quadword (%% (rdi,0))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r15) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x4c; 0x89; 0x57; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r11) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_tomont_p384_alt_tmc = define_trimmed "bignum_tomont_p384_alt_tmc" bignum_tomont_p384_alt_mc;;

let BIGNUM_TOMONT_P384_ALT_EXEC = X86_MK_CORE_EXEC_RULE bignum_tomont_p384_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let swlemma = WORD_RULE
  `word_add (word_shl x 32) x:int64 = word(4294967297 * val x)`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &18446744069414584321 * &(val(word(4294967297 * val x):int64))
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &18446744069414584321 * &(val(word(4294967297 * val x):int64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> (a * (b * x) == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_TOMONT_P384_ALT_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x455) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_tomont_p384_alt_tmc) /\
                  read RIP s = word(pc + 0x09) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = word (pc + 0x44b) /\
                  bignum_from_memory (z,6) s = (2 EXP 384 * a) MOD p_384)
             (MAYCHANGE [RIP; RSI; RAX; RBX; RCX; RDX;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  (*** Simulate the main 6-fold multiply-and-Montgomery-reduce block ***)

  MAP_EVERY (fun s ->
    X86_SINGLE_STEP_TAC BIGNUM_TOMONT_P384_ALT_EXEC s THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC s) THEN CLARIFY_TAC)
   (statenames "s" (1--272)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_NEG]) THEN

  (*** Do the congruential reasoning on the chosen multipliers ***)

  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Derive the main property of the pre-reduced form, which we call t ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
      [sum_s265; sum_s266; sum_s267; sum_s268;
       sum_s269; sum_s271; word(bitval carry_s271)]` THEN
  ABBREV_TAC `r = (2 EXP 384 EXP 2) MOD p_384` THEN
  POP_ASSUM(ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[p_384]) THEN

  SUBGOAL_THEN
   `t < 2 * p_384 /\ (2 EXP 384 * t == a * r) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
        `!ab. ab <= 2 EXP 384 * p /\
              2 EXP 384 * t < ab + 2 EXP 384 * p
              ==> t < 2 * p`) THEN
      EXISTS_TAC `a * r:num` THEN
      MAP_EVERY EXPAND_TAC ["a"; "r"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "r"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final comparison ****)

  X86_ACCSTEPS_TAC BIGNUM_TOMONT_P384_ALT_EXEC (273--289) (273--289) THEN
  SUBGOAL_THEN
   `sum_s288:int64 = word(bitval(p_384 <= t))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC WORD_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THENL
     [UNDISCH_TAC `t < 2 * p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      EXPAND_TAC "t" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      REWRITE_TAC[VAL_WORD_BITVAL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Corrective masked subtraction ***)

  X86_ACCSTEPS_TAC BIGNUM_TOMONT_P384_ALT_EXEC (290--304) (290--304) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_384` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t:num == a * r) (mod p)
        ==> coprime(p,e) /\ (e * e == r) (mod p)
            ==> (t == e * a) (mod p)`)) THEN
    REWRITE_TAC[COPRIME_REXP; COPRIME_2; CONG] THEN EXPAND_TAC "r" THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  ASM_SIMP_TAC[MOD_CASES] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `t < 2 * p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_TOMONT_P384_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_tomont_p384_alt_tmc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p384_alt_tmc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p384_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,6) s = (2 EXP 384 * a) MOD p_384)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 40),40)])`,
  X86_PROMOTE_RETURN_STACK_TAC
   bignum_tomont_p384_alt_tmc BIGNUM_TOMONT_P384_ALT_CORRECT
   `[RBX; R12; R13; R14; R15]` 40);;

let BIGNUM_TOMONT_P384_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_tomont_p384_alt_mc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p384_alt_mc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p384_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,6) s = (2 EXP 384 * a) MOD p_384)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 40),40)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOMONT_P384_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_tomont_p384_alt_windows_mc = define_from_elf
   "bignum_tomont_p384_alt_windows_mc" "x86/p384/bignum_tomont_p384_alt.obj";;

let bignum_tomont_p384_alt_windows_tmc = define_trimmed "bignum_tomont_p384_alt_windows_tmc" bignum_tomont_p384_alt_windows_mc;;

let BIGNUM_TOMONT_P384_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_tomont_p384_alt_windows_tmc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p384_alt_windows_tmc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p384_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,6) s = (2 EXP 384 * a) MOD p_384)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 56),56)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   bignum_tomont_p384_alt_windows_tmc bignum_tomont_p384_alt_tmc
   BIGNUM_TOMONT_P384_ALT_CORRECT `[RBX; R12; R13; R14; R15]` 40);;

let BIGNUM_TOMONT_P384_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_tomont_p384_alt_windows_mc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p384_alt_windows_mc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p384_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,6) s = (2 EXP 384 * a) MOD p_384)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 56),56)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOMONT_P384_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

