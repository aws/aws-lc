(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiply-add mod n_25519, basepoint order for curve25519/edwards25519.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/curve25519/bignum_madd_n25519_alt.o";;
 ****)

let bignum_madd_n25519_alt_mc =
  define_assert_from_elf "bignum_madd_n25519_alt_mc" "x86/curve25519/bignum_madd_n25519_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x89; 0xd5;        (* MOV (% rbp) (% rdx) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x65; 0x00;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x03; 0x01;        (* ADD (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x65; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x03; 0x41; 0x08;  (* ADD (% rax) (Memop Quadword (%% (rcx,8))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x65; 0x00;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,0))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x65; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x03; 0x41; 0x10;  (* ADD (% rax) (Memop Quadword (%% (rcx,16))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x65; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,8))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x65; 0x00;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,0))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x65; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x03; 0x41; 0x18;  (* ADD (% rax) (Memop Quadword (%% (rcx,24))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x65; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,16))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x65; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,8))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x65; 0x00;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,0))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x65; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,24))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x65; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,16))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x65; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,8))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x65; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,24))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x65; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,16))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x65; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,24))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4c; 0x89; 0xfb;        (* MOV (% rbx) (% r15) *)
  0x48; 0xc1; 0xeb; 0x3c;  (* SHR (% rbx) (Imm8 (word 60)) *)
  0x49; 0xc1; 0xe7; 0x04;  (* SHL (% r15) (Imm8 (word 4)) *)
  0x49; 0xc1; 0xef; 0x04;  (* SHR (% r15) (Imm8 (word 4)) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xb8; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rax) (Imm64 (word 1503914060200516822)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xec;        (* SUB (% r12) (% rbp) *)
  0x49; 0x19; 0xcd;        (* SBB (% r13) (% rcx) *)
  0x49; 0x19; 0xd6;        (* SBB (% r14) (% rdx) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0x21; 0xd8;        (* AND (% rax) (% rbx) *)
  0x48; 0xba; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rdx) (Imm64 (word 1503914060200516822)) *)
  0x48; 0x21; 0xda;        (* AND (% rdx) (% rbx) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x10;
                           (* MOV (% rbx) (Imm64 (word 1152921504606846976)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x4c; 0x89; 0xfb;        (* MOV (% rbx) (% r15) *)
  0x4c; 0x0f; 0xa4; 0xf3; 0x04;
                           (* SHLD (% rbx) (% r14) (Imm8 (word 4)) *)
  0x49; 0xc1; 0xef; 0x3c;  (* SHR (% r15) (Imm8 (word 60)) *)
  0x4c; 0x29; 0xfb;        (* SUB (% rbx) (% r15) *)
  0x49; 0xc1; 0xe6; 0x04;  (* SHL (% r14) (Imm8 (word 4)) *)
  0x4d; 0x0f; 0xac; 0xfe; 0x04;
                           (* SHRD (% r14) (% r15) (Imm8 (word 4)) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xb8; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rax) (Imm64 (word 1503914060200516822)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xeb;        (* SUB (% r11) (% rbp) *)
  0x49; 0x19; 0xcc;        (* SBB (% r12) (% rcx) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0x21; 0xd8;        (* AND (% rax) (% rbx) *)
  0x48; 0xba; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rdx) (Imm64 (word 1503914060200516822)) *)
  0x48; 0x21; 0xda;        (* AND (% rdx) (% rbx) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x10;
                           (* MOV (% rbx) (Imm64 (word 1152921504606846976)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x4c; 0x89; 0xf3;        (* MOV (% rbx) (% r14) *)
  0x4c; 0x0f; 0xa4; 0xeb; 0x04;
                           (* SHLD (% rbx) (% r13) (Imm8 (word 4)) *)
  0x49; 0xc1; 0xee; 0x3c;  (* SHR (% r14) (Imm8 (word 60)) *)
  0x4c; 0x29; 0xf3;        (* SUB (% rbx) (% r14) *)
  0x49; 0xc1; 0xe5; 0x04;  (* SHL (% r13) (Imm8 (word 4)) *)
  0x4d; 0x0f; 0xac; 0xf5; 0x04;
                           (* SHRD (% r13) (% r14) (Imm8 (word 4)) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xb8; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rax) (Imm64 (word 1503914060200516822)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xea;        (* SUB (% r10) (% rbp) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0x21; 0xd8;        (* AND (% rax) (% rbx) *)
  0x48; 0xba; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rdx) (Imm64 (word 1503914060200516822)) *)
  0x48; 0x21; 0xda;        (* AND (% rdx) (% rbx) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x10;
                           (* MOV (% rbx) (Imm64 (word 1152921504606846976)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x11; 0xdd;        (* ADC (% r13) (% rbx) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x4c; 0x0f; 0xa4; 0xe3; 0x04;
                           (* SHLD (% rbx) (% r12) (Imm8 (word 4)) *)
  0x49; 0xc1; 0xed; 0x3c;  (* SHR (% r13) (Imm8 (word 60)) *)
  0x4c; 0x29; 0xeb;        (* SUB (% rbx) (% r13) *)
  0x49; 0xc1; 0xe4; 0x04;  (* SHL (% r12) (Imm8 (word 4)) *)
  0x4d; 0x0f; 0xac; 0xec; 0x04;
                           (* SHRD (% r12) (% r13) (Imm8 (word 4)) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xb8; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rax) (Imm64 (word 1503914060200516822)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xe9;        (* SUB (% r9) (% rbp) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0x21; 0xd8;        (* AND (% rax) (% rbx) *)
  0x48; 0xba; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rdx) (Imm64 (word 1503914060200516822)) *)
  0x48; 0x21; 0xda;        (* AND (% rdx) (% rbx) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x10;
                           (* MOV (% rbx) (Imm64 (word 1152921504606846976)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x11; 0xdc;        (* ADC (% r12) (% rbx) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x4c; 0x0f; 0xa4; 0xdb; 0x04;
                           (* SHLD (% rbx) (% r11) (Imm8 (word 4)) *)
  0x49; 0xc1; 0xec; 0x3c;  (* SHR (% r12) (Imm8 (word 60)) *)
  0x4c; 0x29; 0xe3;        (* SUB (% rbx) (% r12) *)
  0x49; 0xc1; 0xe3; 0x04;  (* SHL (% r11) (Imm8 (word 4)) *)
  0x4d; 0x0f; 0xac; 0xe3; 0x04;
                           (* SHRD (% r11) (% r12) (Imm8 (word 4)) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xb8; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rax) (Imm64 (word 1503914060200516822)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xe8;        (* SUB (% r8) (% rbp) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0x21; 0xd8;        (* AND (% rax) (% rbx) *)
  0x48; 0xba; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rdx) (Imm64 (word 1503914060200516822)) *)
  0x48; 0x21; 0xda;        (* AND (% rdx) (% rbx) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x10;
                           (* MOV (% rbx) (Imm64 (word 1152921504606846976)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_madd_n25519_alt_tmc = define_trimmed "bignum_madd_n25519_alt_tmc" bignum_madd_n25519_alt_mc;;

let BIGNUM_MADD_N25519_ALT_EXEC = X86_MK_CORE_EXEC_RULE bignum_madd_n25519_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_25519 = new_definition `n_25519 = 7237005577332262213973186563042994240857116359379907606001950938285454250989`;;

let BIGNUM_MADD_N25519_ALT_CORRECT = time prove
 (`!z x m y n c r pc.
      nonoverlapping (word pc,0x3ea) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_madd_n25519_alt_tmc) /\
                read RIP s = word (pc + 0xa) /\
                C_ARGUMENTS [z; x; y; c] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n /\
                bignum_from_memory (c,4) s = r)
           (\s. read RIP s = word (pc + 0x3df) /\
                bignum_from_memory (z,4) s = (m * n + r) MOD n_25519)
         (MAYCHANGE [RIP; RAX; RDX; RCX; RBX; RBP;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `m:num`; `y:int64`; `n:num`;
    `c:int64`; `r:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Initial schoolbook multiply-add block ***)

  ENSURES_SEQUENCE_TAC `pc + 0x14a`
   `\s. read RDI s = z /\
        bignum_of_wordlist
         [read R8 s; read R9 s; read R10 s; read R11 s;
          read R12 s; read R13 s; read R14 s; read R15 s] = m * n + r` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_" `read(memory :> bytes(x,8 * 4)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "y_" `read(memory :> bytes(y,8 * 4)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "c_" `read(memory :> bytes(c,8 * 4)) s0` THEN
    X86_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC (1--92) (1--92) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"; "r"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    SPEC_TAC(`m * n + r:num`,`mnr:num`) THEN GEN_TAC THEN
    GHOST_INTRO_TAC `d0:int64` `read R8` THEN
    GHOST_INTRO_TAC `d1:int64` `read R9` THEN
    GHOST_INTRO_TAC `d2:int64` `read R10` THEN
    GHOST_INTRO_TAC `d3:int64` `read R11` THEN
    GHOST_INTRO_TAC `d4:int64` `read R12` THEN
    GHOST_INTRO_TAC `d5:int64` `read R13` THEN
    GHOST_INTRO_TAC `d6:int64` `read R14` THEN
    GHOST_INTRO_TAC `d7:int64` `read R15` THEN
    GLOBALIZE_PRECONDITION_TAC] THEN

  (*** Toplevel breakdown ****)

  MAP_EVERY ABBREV_TAC
   [`r0 = bignum_of_wordlist [d4; d5; d6; d7] MOD n_25519`;
    `r1 = (val(d3:int64) + 2 EXP 64 * r0) MOD n_25519`;
    `r2 = (val(d2:int64) + 2 EXP 64 * r1) MOD n_25519`;
    `r3 = (val(d1:int64) + 2 EXP 64 * r2) MOD n_25519`;
    `r4 = (val(d0:int64) + 2 EXP 64 * r3) MOD n_25519`] THEN
  SUBGOAL_THEN
   `r0 < n_25519 /\ r1 < n_25519 /\ r2 < n_25519 /\
    r3 < n_25519 /\ r4 < n_25519`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r0"; "r1"; "r2"; "r3"; "r4"] THEN
    REWRITE_TAC[MOD_LT_EQ; n_25519; ARITH_EQ];
    ALL_TAC] THEN

  SUBGOAL_THEN `mnr MOD n_25519 = r4:num` SUBST1_TAC THEN
  UNDISCH_TAC `bignum_of_wordlist [d0; d1; d2; d3; d4; d5; d6; d7] = mnr` THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXPAND_TAC ["r4"; "r3"; "r2"; "r1"; "r0"] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC MOD_DOWN_CONV THEN
    REFL_TAC;
    DISCH_THEN(K ALL_TAC)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  (*** Zeroth reduction ***)

  X86_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC
   [6;10;11;12;13;14;15;16;24;25;26;27] (1--27) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s24;sum_s25;sum_s26;sum_s27] = r0`
  ASSUME_TAC THENL
   [ABBREV_TAC `m = bignum_of_wordlist [d4; d5; d6; d7]` THEN
    SUBGOAL_THEN `m < 2 EXP 256` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `q:int64 = word_ushr d7 60` THEN
    SUBGOAL_THEN
     `&(val (word_ushr (word_shl (d7:int64) 4) 4)):real =
      &(val d7) - &2 pow 60 * &(val(q:int64))`
    SUBST_ALL_TAC THENL [EXPAND_TAC "q" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    EXPAND_TAC "r0" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    EXISTS_TAC `256` THEN
    EXISTS_TAC
     `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
           &n_25519:real` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `m < val(q:int64) * n_25519 <=> carry_s16`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
        EXPAND_TAC "m" THEN REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        EXPAND_TAC "m" THEN
        REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        BOOL_CASES_TAC `carry_s16:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
          filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      SUBGOAL_THEN `val(q:int64) = m DIV 2 EXP 252` SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["m"; "q"] THEN
        CONV_TAC(RAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[VAL_WORD_USHR];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
      REWRITE_TAC[INT_REM_UNIQUE] THEN
      CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
      UNDISCH_TAC `m < 2 EXP 256` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
      COND_CASES_TAC THEN ASM_INT_ARITH_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    UNDISCH_THEN `bignum_of_wordlist [d4; d5; d6; d7] MOD n_25519 = r0`
     (K ALL_TAC)] THEN

  (*** First reduction ***)

  X86_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC
   [35;39;40;41;42;43;44;45;53;54;55;56] (28--56) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s53;sum_s54;sum_s55;sum_s56] = r1`
  ASSUME_TAC THENL
   [ABBREV_TAC `m = val(d3:int64) + 2 EXP 64 * r0` THEN
    SUBGOAL_THEN `m < 2 EXP 64 * n_25519` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN UNDISCH_TAC `r0 < n_25519` THEN
      MP_TAC(ISPEC `d3:int64` VAL_BOUND_64) THEN ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC
     `q:int64 =
      word_sub
       (word_subword((word_join:int64->int64->int128) sum_s27 sum_s26) (60,64))
       (word_ushr sum_s27 60)` THEN
    SUBGOAL_THEN
     `MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64) /\
      val q + m DIV 2 EXP 252 DIV 2 EXP 64 = m DIV 2 EXP 252`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN
      SUBGOAL_THEN
       `word_ushr (sum_s27:int64) 60 = word(m DIV 2 EXP 252 DIV 2 EXP 64) /\
        word_subword
          ((word_join:int64->int64->int128) sum_s27 sum_s26) (60,64):int64 =
        word(m DIV 2 EXP 252)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; word_ushr; word_subword] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        MAP_EVERY EXPAND_TAC ["m"; "r0"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[WORD_EQ] THEN
        REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN] THEN
        REWRITE_TAC[DIMINDEX_128; DIV_MOD; CONG; GSYM EXP_ADD] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        REWRITE_TAC[MOD_MOD_EXP_MIN; ADD_SYM] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `m DIV 2 EXP 252 <= 2 EXP 64` MP_TAC THENL
       [UNDISCH_TAC `m < 2 EXP 64 * n_25519` THEN
        REWRITE_TAC[n_25519] THEN ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `a <= b <=> a = b \/ a < b`]] THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
       [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
        SIMP_TAC[DIV_LT; WORD_SUB_0; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(val(word_subword
           ((word_join:int64->int64->int128)
            (word_ushr sum_s27 60) (word_shl sum_s26 4)) (4,64):int64)):real =
      (&2 pow 64 * &(val(sum_s27:int64)) + &(val(sum_s26:int64))) -
      &2 pow 60 * &(val(q:int64))`
    SUBST_ALL_TAC THENL
     [POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
        `q + x:real = y ==> q = y - x`)) THEN
      REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      MAP_EVERY EXPAND_TAC ["m"; "r0"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
      REWRITE_TAC[ARITH_RULE
       `(a + 2 EXP 64 * q) DIV 2 EXP 60 =
        (2 EXP 60 * (16 * q) + a) DIV 2 EXP 60`] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      CONV_TAC WORD_BLAST;
      POP_ASSUM(K ALL_TAC)] THEN
    EXPAND_TAC "r1" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN EXISTS_TAC `256` THEN
    EXISTS_TAC
     `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
           &n_25519:real` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `m < val(q:int64) * n_25519 <=> carry_s45`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
        MAP_EVERY EXPAND_TAC ["m"; "r0"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        MAP_EVERY EXPAND_TAC ["m"; "r0"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        BOOL_CASES_TAC `carry_s45:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
          filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
      REWRITE_TAC[INT_REM_UNIQUE] THEN
      CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
      MAP_EVERY UNDISCH_TAC
       [`MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64)`;
        `m < 2 EXP 64 * n_25519`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
      COND_CASES_TAC THEN ASM_INT_ARITH_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    UNDISCH_THEN `(val(d3:int64) + 2 EXP 64 * r0) MOD n_25519 = r1`
     (K ALL_TAC)] THEN

  (*** Second reduction ***)

  X86_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC
   [64;68;69;70;71;72;73;74;82;83;84;85] (57--85) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s82;sum_s83;sum_s84;sum_s85] = r2`
  ASSUME_TAC THENL
   [ABBREV_TAC `m = val(d2:int64) + 2 EXP 64 * r1` THEN
    SUBGOAL_THEN `m < 2 EXP 64 * n_25519` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN UNDISCH_TAC `r1 < n_25519` THEN
      MP_TAC(ISPEC `d2:int64` VAL_BOUND_64) THEN ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC
     `q:int64 =
      word_sub
       (word_subword((word_join:int64->int64->int128) sum_s56 sum_s55) (60,64))
       (word_ushr sum_s56 60)` THEN
    SUBGOAL_THEN
     `MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64) /\
      val q + m DIV 2 EXP 252 DIV 2 EXP 64 = m DIV 2 EXP 252`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN
      SUBGOAL_THEN
       `word_ushr (sum_s56:int64) 60 = word(m DIV 2 EXP 252 DIV 2 EXP 64) /\
        word_subword
          ((word_join:int64->int64->int128) sum_s56 sum_s55) (60,64):int64 =
        word(m DIV 2 EXP 252)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; word_ushr; word_subword] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        MAP_EVERY EXPAND_TAC ["m"; "r1"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[WORD_EQ] THEN
        REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN] THEN
        REWRITE_TAC[DIMINDEX_128; DIV_MOD; CONG; GSYM EXP_ADD] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        REWRITE_TAC[MOD_MOD_EXP_MIN; ADD_SYM] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `m DIV 2 EXP 252 <= 2 EXP 64` MP_TAC THENL
       [UNDISCH_TAC `m < 2 EXP 64 * n_25519` THEN
        REWRITE_TAC[n_25519] THEN ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `a <= b <=> a = b \/ a < b`]] THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
       [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
        SIMP_TAC[DIV_LT; WORD_SUB_0; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(val(word_subword
           ((word_join:int64->int64->int128)
            (word_ushr sum_s56 60) (word_shl sum_s55 4)) (4,64):int64)):real =
      (&2 pow 64 * &(val(sum_s56:int64)) + &(val(sum_s55:int64))) -
      &2 pow 60 * &(val(q:int64))`
    SUBST_ALL_TAC THENL
     [POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
        `q + x:real = y ==> q = y - x`)) THEN
      REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      MAP_EVERY EXPAND_TAC ["m"; "r1"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
      REWRITE_TAC[ARITH_RULE
       `(a + 2 EXP 64 * q) DIV 2 EXP 60 =
        (2 EXP 60 * (16 * q) + a) DIV 2 EXP 60`] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      CONV_TAC WORD_BLAST;
      POP_ASSUM(K ALL_TAC)] THEN
    EXPAND_TAC "r2" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN EXISTS_TAC `256` THEN
    EXISTS_TAC
     `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
           &n_25519:real` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `m < val(q:int64) * n_25519 <=> carry_s74`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
        MAP_EVERY EXPAND_TAC ["m"; "r1"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        MAP_EVERY EXPAND_TAC ["m"; "r1"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        BOOL_CASES_TAC `carry_s74:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
          filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
      REWRITE_TAC[INT_REM_UNIQUE] THEN
      CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
      MAP_EVERY UNDISCH_TAC
       [`MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64)`;
        `m < 2 EXP 64 * n_25519`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
      COND_CASES_TAC THEN ASM_INT_ARITH_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    UNDISCH_THEN `(val(d2:int64) + 2 EXP 64 * r1) MOD n_25519 = r2`
     (K ALL_TAC)] THEN

  (*** Third reduction ***)

  X86_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC
   [93;97;98;99;100;101;102;103;111;112;113;114] (86--114) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s111;sum_s112;sum_s113;sum_s114] = r3`
  ASSUME_TAC THENL
   [ABBREV_TAC `m = val(d1:int64) + 2 EXP 64 * r2` THEN
    SUBGOAL_THEN `m < 2 EXP 64 * n_25519` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN UNDISCH_TAC `r2 < n_25519` THEN
      MP_TAC(ISPEC `d1:int64` VAL_BOUND_64) THEN ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC
     `q:int64 =
      word_sub
       (word_subword((word_join:int64->int64->int128) sum_s85 sum_s84) (60,64))
       (word_ushr sum_s85 60)` THEN
    SUBGOAL_THEN
     `MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64) /\
      val q + m DIV 2 EXP 252 DIV 2 EXP 64 = m DIV 2 EXP 252`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN
      SUBGOAL_THEN
       `word_ushr (sum_s85:int64) 60 = word(m DIV 2 EXP 252 DIV 2 EXP 64) /\
        word_subword
          ((word_join:int64->int64->int128) sum_s85 sum_s84) (60,64):int64 =
        word(m DIV 2 EXP 252)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; word_ushr; word_subword] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        MAP_EVERY EXPAND_TAC ["m"; "r2"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[WORD_EQ] THEN
        REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN] THEN
        REWRITE_TAC[DIMINDEX_128; DIV_MOD; CONG; GSYM EXP_ADD] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        REWRITE_TAC[MOD_MOD_EXP_MIN; ADD_SYM] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `m DIV 2 EXP 252 <= 2 EXP 64` MP_TAC THENL
       [UNDISCH_TAC `m < 2 EXP 64 * n_25519` THEN
        REWRITE_TAC[n_25519] THEN ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `a <= b <=> a = b \/ a < b`]] THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
       [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
        SIMP_TAC[DIV_LT; WORD_SUB_0; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(val(word_subword
           ((word_join:int64->int64->int128)
            (word_ushr sum_s85 60) (word_shl sum_s84 4)) (4,64):int64)):real =
      (&2 pow 64 * &(val(sum_s85:int64)) + &(val(sum_s84:int64))) -
      &2 pow 60 * &(val(q:int64))`
    SUBST_ALL_TAC THENL
     [POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
        `q + x:real = y ==> q = y - x`)) THEN
      REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      MAP_EVERY EXPAND_TAC ["m"; "r2"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
      REWRITE_TAC[ARITH_RULE
       `(a + 2 EXP 64 * q) DIV 2 EXP 60 =
        (2 EXP 60 * (16 * q) + a) DIV 2 EXP 60`] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      CONV_TAC WORD_BLAST;
      POP_ASSUM(K ALL_TAC)] THEN
    EXPAND_TAC "r3" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN EXISTS_TAC `256` THEN
    EXISTS_TAC
     `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
           &n_25519:real` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `m < val(q:int64) * n_25519 <=> carry_s103`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
        MAP_EVERY EXPAND_TAC ["m"; "r2"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        MAP_EVERY EXPAND_TAC ["m"; "r2"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        BOOL_CASES_TAC `carry_s103:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
          filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
      REWRITE_TAC[INT_REM_UNIQUE] THEN
      CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
      MAP_EVERY UNDISCH_TAC
       [`MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64)`;
        `m < 2 EXP 64 * n_25519`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
      COND_CASES_TAC THEN ASM_INT_ARITH_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    UNDISCH_THEN `(val(d1:int64) + 2 EXP 64 * r2) MOD n_25519 = r3`
     (K ALL_TAC)] THEN

  (*** Fourth and final reduction ***)

  X86_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC
    [122;126;127;128;129;130;131;132;140;141;142;143] (115--147) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s147" THEN
  ABBREV_TAC `m = val(d0:int64) + 2 EXP 64 * r3` THEN
  SUBGOAL_THEN `m < 2 EXP 64 * n_25519` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN UNDISCH_TAC `r3 < n_25519` THEN
    MP_TAC(ISPEC `d0:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `q:int64 =
    word_sub
     (word_subword((word_join:int64->int64->int128) sum_s114 sum_s113) (60,64))
     (word_ushr sum_s114 60)` THEN
  SUBGOAL_THEN
   `MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64) /\
    val q + m DIV 2 EXP 252 DIV 2 EXP 64 = m DIV 2 EXP 252`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    SUBGOAL_THEN
     `word_ushr (sum_s114:int64) 60 = word(m DIV 2 EXP 252 DIV 2 EXP 64) /\
      word_subword
        ((word_join:int64->int64->int128) sum_s114 sum_s113) (60,64):int64 =
      word(m DIV 2 EXP 252)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; word_ushr; word_subword] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      MAP_EVERY EXPAND_TAC ["m"; "r3"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[WORD_EQ] THEN
      REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN] THEN
      REWRITE_TAC[DIMINDEX_128; DIV_MOD; CONG; GSYM EXP_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN; ADD_SYM] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `m DIV 2 EXP 252 <= 2 EXP 64` MP_TAC THENL
     [UNDISCH_TAC `m < 2 EXP 64 * n_25519` THEN
      REWRITE_TAC[n_25519] THEN ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `a <= b <=> a = b \/ a < b`]] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
     [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      SIMP_TAC[DIV_LT; WORD_SUB_0; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_subword
         ((word_join:int64->int64->int128)
          (word_ushr sum_s114 60) (word_shl sum_s113 4)) (4,64):int64)):real =
    (&2 pow 64 * &(val(sum_s114:int64)) + &(val(sum_s113:int64))) -
    &2 pow 60 * &(val(q:int64))`
  SUBST_ALL_TAC THENL
   [POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
      `q + x:real = y ==> q = y - x`)) THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    MAP_EVERY EXPAND_TAC ["m"; "r3"] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE
     `(a + 2 EXP 64 * q) DIV 2 EXP 60 =
      (2 EXP 60 * (16 * q) + a) DIV 2 EXP 60`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    CONV_TAC WORD_BLAST;
    POP_ASSUM(K ALL_TAC)] THEN
  EXPAND_TAC "r4" THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN EXISTS_TAC `256` THEN
  EXISTS_TAC
   `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
         &n_25519:real` THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `m < val(q:int64) * n_25519 <=> carry_s132`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
      MAP_EVERY EXPAND_TAC ["m"; "r3"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      MAP_EVERY EXPAND_TAC ["m"; "r3"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      BOOL_CASES_TAC `carry_s132:bool` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
    REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
    MAP_EVERY UNDISCH_TAC
     [`MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64)`;
      `m < 2 EXP 64 * n_25519`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
    COND_CASES_TAC THEN ASM_INT_ARITH_TAC]);;

let BIGNUM_MADD_N25519_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x m y n c r pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 48),56) (z,8 * 4) /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,LENGTH bignum_madd_n25519_alt_tmc); (x,8 * 4); (y,8 * 4); (c,8 * 4)] /\
      nonoverlapping (word pc,LENGTH bignum_madd_n25519_alt_tmc) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_madd_n25519_alt_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x; y; c] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n /\
                bignum_from_memory (c,4) s = r)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory (z,4) s = (m * n + r) MOD n_25519)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 48),48)])`,
  X86_PROMOTE_RETURN_STACK_TAC
    bignum_madd_n25519_alt_tmc BIGNUM_MADD_N25519_ALT_CORRECT
    `[RBX;RBP;R12;R13;R14;R15]` 48);;

let BIGNUM_MADD_N25519_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x m y n c r pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 48),56) (z,8 * 4) /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,LENGTH bignum_madd_n25519_alt_mc); (x,8 * 4); (y,8 * 4); (c,8 * 4)] /\
      nonoverlapping (word pc,LENGTH bignum_madd_n25519_alt_mc) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_madd_n25519_alt_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x; y; c] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n /\
                bignum_from_memory (c,4) s = r)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory (z,4) s = (m * n + r) MOD n_25519)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MADD_N25519_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_madd_n25519_alt_windows_mc = define_from_elf
   "bignum_madd_n25519_alt_windows_mc" "x86/curve25519/bignum_madd_n25519_alt.obj";;

let bignum_madd_n25519_alt_windows_tmc = define_trimmed "bignum_madd_n25519_alt_windows_tmc" bignum_madd_n25519_alt_windows_mc;;

let BIGNUM_MADD_N25519_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x m y n c r pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 64),72) (z,8 * 4) /\
      ALL (nonoverlapping (word_sub stackpointer (word 64),64))
          [(word pc,LENGTH bignum_madd_n25519_alt_windows_tmc); (x,8 * 4); (y,8 * 4); (c,8 * 4)] /\
      nonoverlapping (word pc,LENGTH bignum_madd_n25519_alt_windows_tmc) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_madd_n25519_alt_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x; y; c] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n /\
                bignum_from_memory (c,4) s = r)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory (z,4) s = (m * n + r) MOD n_25519)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 64),64)])`,
  WINDOWS_X86_WRAP_STACK_TAC
    bignum_madd_n25519_alt_windows_tmc bignum_madd_n25519_alt_tmc
    BIGNUM_MADD_N25519_ALT_CORRECT `[RBX;RBP;R12;R13;R14;R15]` 48);;

let BIGNUM_MADD_N25519_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x m y n c r pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 64),72) (z,8 * 4) /\
      ALL (nonoverlapping (word_sub stackpointer (word 64),64))
          [(word pc,LENGTH bignum_madd_n25519_alt_windows_mc); (x,8 * 4); (y,8 * 4); (c,8 * 4)] /\
      nonoverlapping (word pc,LENGTH bignum_madd_n25519_alt_windows_mc) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_madd_n25519_alt_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x; y; c] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n /\
                bignum_from_memory (c,4) s = r)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory (z,4) s = (m * n + r) MOD n_25519)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 64),64)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MADD_N25519_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

