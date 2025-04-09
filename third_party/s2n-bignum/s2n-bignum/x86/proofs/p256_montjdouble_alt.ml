(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point doubling in Montgomery-Jacobian coordinates for NIST P-256 curve.   *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp256.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "x86/p256/p256_montjdouble_alt.o";;
 ****)

let p256_montjdouble_alt_mc = define_assert_from_elf
  "p256_montjdouble_alt_mc" "x86/p256/p256_montjdouble_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xc0; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 192)) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd7;        (* MOV (% r15) (% rdx) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x49; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% r13) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0x89; 0xd6;        (* MOV (% r14) (% rdx) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x8b; 0x5e; 0x58;  (* MOV (% rbx) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x4d; 0x01; 0xf9;        (* ADD (% r9) (% r15) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x48; 0x11; 0xca;        (* ADC (% rdx) (% rcx) *)
  0x49; 0x89; 0xd7;        (* MOV (% r15) (% rdx) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xc6;        (* ADC (% r14) (% r8) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0x8d; 0x5b; 0xff;  (* LEA (% rbx) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xeb;        (* ADC (% rbx) (% r13) *)
  0x4d; 0x8d; 0x49; 0xff;  (* LEA (% r9) (%% (r9,18446744073709551615)) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xeb;  (* CMOVB (% r13) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xf1;  (* CMOVB (% r14) (% r9) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x24; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r15) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd7;        (* MOV (% r15) (% rdx) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x49; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% r13) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0x89; 0xd6;        (* MOV (% r14) (% rdx) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x8b; 0x5e; 0x38;  (* MOV (% rbx) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x4d; 0x01; 0xf9;        (* ADD (% r9) (% r15) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x48; 0x11; 0xca;        (* ADC (% rdx) (% rcx) *)
  0x49; 0x89; 0xd7;        (* MOV (% r15) (% rdx) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xc6;        (* ADC (% r14) (% r8) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0x8d; 0x5b; 0xff;  (* LEA (% rbx) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xeb;        (* ADC (% rbx) (% r13) *)
  0x4d; 0x8d; 0x49; 0xff;  (* LEA (% r9) (%% (r9,18446744073709551615)) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xeb;  (* CMOVB (% r13) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xf1;  (* CMOVB (% r14) (% r9) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x2b; 0x04; 0x24;  (* SUB (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x1b; 0x4c; 0x24; 0x08;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x10;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x18;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r9) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x03; 0x04; 0x24;  (* ADD (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x13; 0x4c; 0x24; 0x08;
                           (* ADC (% rcx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x13; 0x44; 0x24; 0x10;
                           (* ADC (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x18;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x4c; 0x19; 0xd1;        (* SBB (% rcx) (% r10) *)
  0x48; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rcx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r8) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x4c; 0x89; 0x4c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r9) *)
  0x48; 0x8b; 0x5c; 0x24; 0x60;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x8b; 0x5c; 0x24; 0x68;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,104))) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xf6;        (* SBB (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xf2;        (* SUB (% rdx) (% r14) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xf6;        (* SBB (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xf2;        (* SUB (% rdx) (% r14) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xf6;        (* SBB (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xf2;        (* SUB (% rdx) (% r14) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xfa;        (* SUB (% rdx) (% r15) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xfa;        (* SUB (% rdx) (% r15) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xfa;        (* SUB (% rdx) (% r15) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x5c; 0x24; 0x70;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,112))) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x5c; 0x24; 0x78;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,120))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xcb;        (* DEC (% rbx) *)
  0x4c; 0x11; 0xeb;        (* ADC (% rbx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xeb;  (* CMOVB (% r13) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xf1;  (* CMOVB (% r14) (% r9) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r15) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x03; 0x46; 0x40;  (* ADD (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x8b; 0x4e; 0x28;  (* MOV (% rcx) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x13; 0x4e; 0x48;  (* ADC (% rcx) (Memop Quadword (%% (rsi,72))) *)
  0x4c; 0x8b; 0x46; 0x30;  (* MOV (% r8) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x13; 0x46; 0x50;  (* ADC (% r8) (Memop Quadword (%% (rsi,80))) *)
  0x4c; 0x8b; 0x4e; 0x38;  (* MOV (% r9) (Memop Quadword (%% (rsi,56))) *)
  0x4c; 0x13; 0x4e; 0x58;  (* ADC (% r9) (Memop Quadword (%% (rsi,88))) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x48; 0x83; 0xe8; 0xff;  (* SUB (% rax) (Imm8 (word 255)) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4c; 0x19; 0xd1;        (* SBB (% rcx) (% r10) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x21; 0xda;        (* AND (% rdx) (% r11) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r9) *)
  0x48; 0x8b; 0x5c; 0x24; 0x20;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,32))) *)
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
  0x48; 0x8b; 0x5c; 0x24; 0x28;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,40))) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xf6;        (* SBB (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xf2;        (* SUB (% rdx) (% r14) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xf6;        (* SBB (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xf2;        (* SUB (% rdx) (% r14) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xf6;        (* SBB (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xf2;        (* SUB (% rdx) (% r14) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xfa;        (* SUB (% rdx) (% r15) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xfa;        (* SUB (% rdx) (% r15) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xfa;        (* SUB (% rdx) (% r15) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x5c; 0x24; 0x30;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,48))) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x5c; 0x24; 0x38;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,56))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xcb;        (* DEC (% rbx) *)
  0x4c; 0x11; 0xeb;        (* ADC (% rbx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xeb;  (* CMOVB (% r13) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xf1;  (* CMOVB (% r14) (% r9) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd7;        (* MOV (% r15) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x49; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% r13) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0x89; 0xd6;        (* MOV (% r14) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x8b; 0x5c; 0x24; 0x78;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x4d; 0x01; 0xf9;        (* ADD (% r9) (% r15) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x48; 0x11; 0xca;        (* ADC (% rdx) (% rcx) *)
  0x49; 0x89; 0xd7;        (* MOV (% r15) (% rdx) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xc6;        (* ADC (% r14) (% r8) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0x8d; 0x5b; 0xff;  (* LEA (% rbx) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xeb;        (* ADC (% rbx) (% r13) *)
  0x4d; 0x8d; 0x49; 0xff;  (* LEA (% r9) (%% (r9,18446744073709551615)) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xeb;  (* CMOVB (% r13) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xf1;  (* CMOVB (% r14) (% r9) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd7;        (* MOV (% r15) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x49; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% r13) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0x89; 0xd6;        (* MOV (% r14) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x8b; 0x5c; 0x24; 0x58;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x4d; 0x01; 0xf9;        (* ADD (% r9) (% r15) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x48; 0x11; 0xca;        (* ADC (% rdx) (% rcx) *)
  0x49; 0x89; 0xd7;        (* MOV (% r15) (% rdx) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xc6;        (* ADC (% r14) (% r8) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0x8d; 0x5b; 0xff;  (* LEA (% rbx) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xeb;        (* ADC (% rbx) (% r13) *)
  0x4d; 0x8d; 0x49; 0xff;  (* LEA (% r9) (%% (r9,18446744073709551615)) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xeb;  (* CMOVB (% r13) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xf1;  (* CMOVB (% r14) (% r9) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r15) *)
  0x49; 0xc7; 0xc1; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r9) (Imm32 (word 4294967295)) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x4c; 0x2b; 0x8c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* SUB (% r9) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0xba; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Imm64 (word 4294967295)) *)
  0x4c; 0x1b; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x1b; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0xbc; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r12) (Imm64 (word 18446744069414584321)) *)
  0x4c; 0x1b; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xc7; 0xc1; 0x09; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Imm32 (word 9)) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0xb9; 0x0c; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 12)) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x8d; 0x4c; 0x24; 0x01;
                           (* LEA (% rcx) (%% (r12,1)) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x49; 0x01; 0xc8;        (* ADD (% r8) (% rcx) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xd9;        (* SUB (% r9) (% rbx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x48; 0x19; 0xd1;        (* SBB (% rcx) (% rdx) *)
  0x48; 0xff; 0xc9;        (* DEC (% rcx) *)
  0xb8; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% eax) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xc8;        (* AND (% rax) (% rcx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x48; 0x29; 0xc2;        (* SUB (% rdx) (% rax) *)
  0x49; 0x01; 0xc8;        (* ADD (% r8) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r8) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0x4c; 0x89; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r9) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r10) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4c; 0x89; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x2b; 0x04; 0x24;  (* SUB (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x1b; 0x4c; 0x24; 0x08;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x10;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x58;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x18;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r9) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd7;        (* MOV (% r15) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x49; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% r13) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0x89; 0xd6;        (* MOV (% r14) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x8b; 0x5c; 0x24; 0x38;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x4d; 0x01; 0xf9;        (* ADD (% r9) (% r15) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x48; 0x11; 0xca;        (* ADC (% rdx) (% rcx) *)
  0x49; 0x89; 0xd7;        (* MOV (% r15) (% rdx) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xc6;        (* ADC (% r14) (% r8) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0x8d; 0x5b; 0xff;  (* LEA (% rbx) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xeb;        (* ADC (% rbx) (% r13) *)
  0x4d; 0x8d; 0x49; 0xff;  (* LEA (% r9) (%% (r9,18446744073709551615)) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xeb;  (* CMOVB (% r13) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xf1;  (* CMOVB (% r14) (% r9) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x24; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r15) *)
  0x48; 0x8b; 0x5c; 0x24; 0x60;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x8b; 0x5c; 0x24; 0x68;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,104))) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xf6;        (* SBB (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xf2;        (* SUB (% rdx) (% r14) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xf6;        (* SBB (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xf2;        (* SUB (% rdx) (% r14) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xf6;        (* SBB (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xf2;        (* SUB (% rdx) (% r14) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xfa;        (* SUB (% rdx) (% r15) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xfa;        (* SUB (% rdx) (% r15) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xfa;        (* SUB (% rdx) (% r15) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x5c; 0x24; 0x70;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,112))) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x5c; 0x24; 0x78;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,120))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967296)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x8d; 0x5b; 0x02;  (* LEA (% rbx) (%% (rbx,2)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xcb;        (* DEC (% rbx) *)
  0x4c; 0x11; 0xeb;        (* ADC (% rbx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xeb;  (* CMOVB (% r13) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xf1;  (* CMOVB (% r14) (% r9) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x2b; 0x44; 0x24; 0x20;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x1b; 0x4c; 0x24; 0x28;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x30;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x58;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x38;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,56))) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x47; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4f; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r9) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x4c; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4d; 0x0f; 0xa4; 0xd3; 0x02;
                           (* SHLD (% r11) (% r10) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4d; 0x0f; 0xa4; 0xca; 0x02;
                           (* SHLD (% r10) (% r9) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x4d; 0x0f; 0xa4; 0xc1; 0x02;
                           (* SHLD (% r9) (% r8) (Imm8 (word 2)) *)
  0x49; 0xc1; 0xe0; 0x02;  (* SHL (% r8) (Imm8 (word 2)) *)
  0x48; 0xc1; 0xe9; 0x3e;  (* SHR (% rcx) (Imm8 (word 62)) *)
  0x48; 0x83; 0xc1; 0x01;  (* ADD (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x2b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x1b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,176))) *)
  0x4c; 0x1b; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x49; 0x01; 0xc8;        (* ADD (% r8) (% rcx) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xd9;        (* SUB (% r9) (% rbx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x48; 0x19; 0xd1;        (* SBB (% rcx) (% rdx) *)
  0x48; 0xff; 0xc9;        (* DEC (% rcx) *)
  0xb8; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% eax) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xc8;        (* AND (% rax) (% rcx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x48; 0x29; 0xc2;        (* SUB (% rdx) (% rax) *)
  0x49; 0x01; 0xc8;        (* ADD (% r8) (% rcx) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x49; 0xc7; 0xc0; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r8) (Imm32 (word 4294967295)) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x4c; 0x2b; 0x04; 0x24;  (* SUB (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0xb9; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Imm64 (word 4294967295)) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x08;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x10;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0xbb; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11) (Imm64 (word 18446744069414584321)) *)
  0x4c; 0x1b; 0x5c; 0x24; 0x18;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x4d; 0x89; 0xdc;        (* MOV (% r12) (% r11) *)
  0x4d; 0x0f; 0xa4; 0xd3; 0x03;
                           (* SHLD (% r11) (% r10) (Imm8 (word 3)) *)
  0x4d; 0x0f; 0xa4; 0xca; 0x03;
                           (* SHLD (% r10) (% r9) (Imm8 (word 3)) *)
  0x4d; 0x0f; 0xa4; 0xc1; 0x03;
                           (* SHLD (% r9) (% r8) (Imm8 (word 3)) *)
  0x49; 0xc1; 0xe0; 0x03;  (* SHL (% r8) (Imm8 (word 3)) *)
  0x49; 0xc1; 0xec; 0x3d;  (* SHR (% r12) (Imm8 (word 61)) *)
  0xb9; 0x03; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 3)) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x8d; 0x4c; 0x24; 0x01;
                           (* LEA (% rcx) (%% (r12,1)) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x49; 0x01; 0xc8;        (* ADD (% r8) (% rcx) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xd9;        (* SUB (% r9) (% rbx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x48; 0x19; 0xd1;        (* SBB (% rcx) (% rdx) *)
  0x48; 0xff; 0xc9;        (* DEC (% rcx) *)
  0xb8; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% eax) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xc8;        (* AND (% rax) (% rcx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x48; 0x29; 0xc2;        (* SUB (% rdx) (% rax) *)
  0x49; 0x01; 0xc8;        (* ADD (% r8) (% rcx) *)
  0x4c; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r8) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0x4c; 0x89; 0x4f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r9) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r10) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4c; 0x89; 0x5f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r11) *)
  0x48; 0x81; 0xc4; 0xc0; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 192)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let p256_montjdouble_alt_tmc = define_trimmed "p256_montjdouble_alt_tmc" p256_montjdouble_alt_mc;;

let P256_MONTJDOUBLE_ALT_EXEC = X86_MK_CORE_EXEC_RULE p256_montjdouble_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

let p256shortishredlemma = prove
 (`!n. n < 24 * 2 EXP 256
       ==> let q = n DIV 2 EXP 256 + 1 in
           q <= 24 /\
           q < 2 EXP 64 /\
           q * p_256 <= n + p_256 /\
           n < q * p_256 + p_256`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256] THEN ARITH_TAC);;

let FORALL_INT_CASES' = prove
 (`!P. (!x:int. P x) <=> (!n. P(&n)) /\ (!n. ~(n = 0) ==> P(-- &n))`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [FORALL_INT_CASES] THEN
  MESON_TAC[INT_NEG_EQ_0; INT_OF_NUM_EQ]);;

let p256shortintredlemma = prove
 (`!n. --(&p_256) <= n /\ n <= &4 * &2 pow 256
       ==> let q = (&2 pow 256 + n) div &2 pow 256 in
           &0 <= q /\ q < &6 /\
           q < &2 pow 64 /\
           q * &p_256 <= n + &p_256 /\
           n < q * &p_256 + &p_256`,
  ONCE_REWRITE_TAC[INT_ARITH `&2 pow 256 + n:int = &1 * &2 pow 256 + n`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[FORALL_INT_CASES'; INT_DIV_LNEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; INT_OF_NUM_REM] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256] THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_LE_NEG2; INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `n < 2 EXP 256` ASSUME_TAC THENL
   [UNDISCH_TAC `n <= p_256` THEN REWRITE_TAC[p_256] THEN ARITH_TAC;
    ASM_SIMP_TAC[DIV_LT; MOD_LT]] THEN
  UNDISCH_TAC `n <= p_256` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[p_256] THEN INT_ARITH_TAC);;

let lvs =
 ["x_1",[`RSI`; `0`];
  "y_1",[`RSI`; `32`];
  "z_1",[`RSI`; `64`];
  "x_3",[`RDI`; `0`];
  "y_3",[`RDI`; `32`];
  "z_3",[`RDI`; `64`];
  "z2",[`RSP`; `0`];
  "y4",[`RSP`; `0`];
  "y2",[`RSP`; `32`];
  "t1",[`RSP`; `64`];
  "t2",[`RSP`; `96`];
  "x2p",[`RSP`; `96`];
  "dx2",[`RSP`; `96`];
  "xy2",[`RSP`; `128`];
  "x4p",[`RSP`; `160`];
  "d",[`RSP`; `160`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of montsqr.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTSQR_P256_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p256_montjdouble_alt_tmc) 137 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    nonoverlapping (word pc,0x14c9) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p256_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a)
             (\s. read RIP s = pcout /\
                  (a EXP 2 <= 2 EXP 256 * p_256
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 4)) s =
                       (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
           (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                       R8; R9; R10; R11; R12; R13; R14; R15] ,,
            MAYCHANGE
             [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
            MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 256 * p_256  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 256 * p_256` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P256_MONTJDOUBLE_ALT_EXEC (1--137)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  MAP_EVERY (fun n ->
    X86_STEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC("s"^string_of_int n)))
   (1--119) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0]) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s102; sum_s110; sum_s117; sum_s118; sum_s119]` THEN
  SUBGOAL_THEN
   `t < 2 * p_256 /\ (2 EXP 256 * t == a EXP 2) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_256; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC
    [121;123;126;128;129] (120--137) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_256` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_256 then &t:real else &t - &p_256`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s129 <=> p_256 <= t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of montmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTMUL_P256_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p256_montjdouble_alt_tmc) 166 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = b
    ==>
    nonoverlapping (word pc,0x14c9) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p256_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              b)
             (\s. read RIP s = pcout /\
                  (a * b <= 2 EXP 256 * p_256
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
             (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
             MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 256 * p_256  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 256 * p_256` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P256_MONTJDOUBLE_ALT_EXEC (1--166)] THEN
  ENSURES_INIT_TAC "s1" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Simulate the core pre-reduced result accumulation ***)

  X86_GEN_ACCSTEPS_TAC
    (fun _ -> RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
                `word_sub x (word_neg y):int64 = word_add x y`]))
    P256_MONTJDOUBLE_ALT_EXEC (2--149) (2--149) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s133; sum_s141; sum_s147; sum_s148; sum_s149]` THEN
  SUBGOAL_THEN
   `t < 2 * p_256 /\ (2 EXP 256 * t == a * b) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_256; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC
   [151;153;156;158;159] (150--167) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_256` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_256 then &t:real else &t - &p_256`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s159 <=> p_256 <= t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_P256_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p256_montjdouble_alt_tmc) 21 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    nonoverlapping (word pc,0x14c9) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p256_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read RIP s = pcout /\
                  (m < p_256 /\ n < p_256
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s) = (&m - &n) rem &p_256))
          (MAYCHANGE [RIP; RAX; RDX; RCX; R8; R9; R10; R11] ,,
           MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (1--8) (1--8) THEN

  SUBGOAL_THEN `carry_s8 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (14--21) (9--21) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV(RAND_CONV BIGNUM_EXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s21" THEN

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
  EXISTS_TAC `--(&(bitval(m < n))):int` THEN REWRITE_TAC[INT_ABS_NUM] THEN
  REWRITE_TAC[INT_ARITH `m - n:int = --b * p + z <=> z = b * p + m - n`] THEN
  REWRITE_TAC[int_eq; int_le; int_lt] THEN
  REWRITE_TAC[int_add_th; int_mul_th; int_of_num_th; int_sub_th] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC(REAL_ARITH
  `!t:real. p < t /\
            (&0 <= a /\ a < p) /\
            (&0 <= z /\ z < t) /\
            ((&0 <= z /\ z < t) /\ (&0 <= a /\ a < t) ==> z = a)
            ==> z = a /\ &0 <= z /\ z < p`) THEN
  EXISTS_TAC `(&2:real) pow 256` THEN

  CONJ_TAC THENL [REWRITE_TAC[p_256] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_256`; `n < p_256`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    ASM_CASES_TAC `&m:real < &n` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[p_256] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; STRIP_TAC] THEN

  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_256] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of weakadd                                                      *)
(* ------------------------------------------------------------------------- *)

let LOCAL_WEAKADD_P256_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p256_montjdouble_alt_tmc) 21 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    nonoverlapping (word pc,0x14c9) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p256_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read RIP s = pcout /\
                  (m + n < 2 EXP 256 + p_256
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s < 2 EXP 256 /\
                       (&(read(memory :> bytes(word_add (read p3 t) (word n3),
                               8 * 4)) s):int == &m + &n) (mod &p_256)))
            (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R9; R10; R11] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [2;4;6;8] (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> 2 EXP 256 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [14;16;18;20] (9--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[]
   `!x. (x < 2 EXP 256 /\ P x) /\ y = x ==> y < 2 EXP 256 /\ P y`) THEN
  EXISTS_TAC `if m + n < 2 EXP 256 then m + n else (m + n) - p_256` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `m + n < 2 EXP 256 + p_256` THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_CONG_REFL] THEN
    MATCH_MP_TAC(INTEGER_RULE `y - p:int = x ==> (x == y) (mod p)`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN MATCH_MP_TAC INT_OF_NUM_SUB THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_REDUCE_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `b <=> 2 EXP 256 <= m + n` THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCARD_STATE_TAC "s21" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; COND_SWAP] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    UNDISCH_TAC `m + n < 2 EXP 256 + p_256` THEN
    EXPAND_TAC "b" THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `&(if b then (m + n) - p_256 else m + n):real =
    if b then (&m + &n) - &p_256 else &m + &n`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
    UNDISCH_TAC `b:bool` THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_256] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_P256_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p256_montjdouble_alt_tmc) 27 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    nonoverlapping (word pc,0x14c9) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p256_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
         (\s. read RIP s = pcout /\
              (m < p_256 /\ n < p_256
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 4)) s = (m + n) MOD p_256))
         (MAYCHANGE [RIP; RAX; RDX; RCX; R8; R9; R10; R11] ,,
          MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
          MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (1--27) (1--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s27" THEN
  ASM_SIMP_TAC[MOD_CASES; ARITH_RULE `m < p /\ n < p ==> m + n < 2 * p`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_256`; `n < p_256`] THEN
    REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN

  SUBGOAL_THEN
   `sum_s17:int64 = word_neg(word(bitval(m + n < p_256))) /\
    (carry_s17 <=> m + n < p_256)`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC FLAG_AND_MASK_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`m < p_256`; `n < p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
      REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    ALL_TAC] THEN

  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_ARITH `p * &0 + &0:real = x - &0 - y <=> x = y`] THEN
    REWRITE_TAC[REAL_EQ_BITVAL] THEN
    ASM_CASES_TAC `carry_s16 <=> carry_s9` THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[p_256; REAL_RAT_REDUCE_CONV `(&2 pow 64 - &1) * &1:real`] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance (12,9) of cmsub (the only one used in this code).                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUBC9_P256_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p256_montjdouble_alt_tmc) 75 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    nonoverlapping (word pc,0x14c9) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p256_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read RIP s = pcout /\
                  (n <= p_256
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s) = (&12 * &m - &9 * &n) rem &p_256))
            (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R8; R9; R10; R11; R12] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_256` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P256_MONTJDOUBLE_ALT_EXEC (1--75)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&12 * &m - &9 * &n) rem &p_256 =
    (&12 * &m + &9 * (&p_256 - &n)) rem &p_256`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [3;5;6;8] (1--8) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist[sum_s3; sum_s5; sum_s6; sum_s8]` THEN
  SUBGOAL_THEN `p_256 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_256` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_256]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Intermediate result from multiply-add block including top +1 ***)

  X86_GEN_ACCSTEPS_TAC
    (fun _ -> RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
                `word_sub x (word_neg y):int64 = word_add x y`]))
    P256_MONTJDOUBLE_ALT_EXEC (9--52) (9--52) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s32; sum_s38; sum_s44; sum_s50; sum_s52] =
    2 EXP 256 + (12 * m + 9 * n')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV  THEN
    MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = (12 * m + 9 * n') DIV 2 EXP 256` THEN
  SUBGOAL_THEN `h < 24` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV  THEN
    MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s52:int64 = word(h + 1)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[ARITH_RULE
     `ca DIV 2 EXP 256 + 1 = (2 EXP 256 + ca) DIV 2 EXP 256`] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `12 * m + 9 * n'` p256shortishredlemma) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXPAND_TAC "h" THEN SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV  THEN
    MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN BOUNDER_TAC[];
    CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Computation of 12 * m + 9 * n' - (h + 1) * p_256 ***)

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC
    [54;56;57;58;59;60;61;62;63] (53--63) THEN
  MP_TAC(SPECL
   [`sum_s63:int64`;
    `&(bignum_of_wordlist[sum_s57; sum_s59; sum_s60; sum_s61]):real`;
    `256`; `12 * m + 9 * n'`; `(h + 1) * p_256`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_256 <= (12 * m + 9 * n') + p_256`;
        `12 * m + 9 * n' < (h + 1) * p_256 + p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `&(12 * m + 9 * n'):real =
      &(bignum_of_wordlist[sum_s32; sum_s38; sum_s44; sum_s50; word(h + 1)]) -
      &2 pow 256`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN

    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `h < 24` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(fun th ->
      (MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) th THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      (MP_TAC o end_itlist CONJ o
       filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) th THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [68;70;72;74] (64--75) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> 12 * m + 9 * n' < (h + 1) * p_256` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &(12 * m + 9 * n') - y + z
    ==> &(12 * m + 9 * n') = x + y - z`)) THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub41_p256 (actually there is only one).                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB41_P256_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p256_montjdouble_alt_tmc) 39 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    nonoverlapping (word pc,0x14c9) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p256_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
         (\s. read RIP s = pcout /\
              (n < p_256
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                          8 * 4)) s) = (&4 * &m - &n) rem &p_256))
         (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R8; R9; R10; R11; R12] ,,
          MAYCHANGE
            [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_256 assumption ***)

  ASM_CASES_TAC `n < p_256` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P256_MONTJDOUBLE_ALT_EXEC (1--39)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Instantiate the (integer) quotient approximation lemma ***)

  MP_TAC(SPEC `&4 * &m - &n:int` p256shortintredlemma) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_LT; INT_ARITH
     `n:int < p ==> --p <= &4 * &m - n`] THEN
    MATCH_MP_TAC(INT_ARITH `x:int <= a ==> x - &n <= a`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN EXPAND_TAC "m" THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Main shift-subtract block ***)

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (11--16) (1--16) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s12; sum_s13; sum_s14; sum_s15; sum_s16]` THEN
  SUBGOAL_THEN `&2 pow 256 + &4 * &m - &n:int = &ca`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [REWRITE_TAC[int_eq; int_add_th; int_sub_th; int_pow_th;
                int_mul_th; int_of_num_th] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`320`; `&0:real`] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n"; "ca"] THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [EXPAND_TAC "ca" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&4 * &m:real =
      &(bignum_of_wordlist
         [word_shl m_0 2;
          word_subword ((word_join:int64->int64->int128) m_1 m_0) (62,64);
          word_subword ((word_join:int64->int64->int128) m_2 m_1) (62,64);
          word_subword ((word_join:int64->int64->int128) m_3 m_2) (62,64);
          word_ushr m_3 62])`
    SUBST1_TAC THENL
     [EXPAND_TAC "m" THEN
      REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
      REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
      REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
      REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR;
                  BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
      ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC NUM_RING;
      MAP_EVERY EXPAND_TAC ["n"; "ca"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s16` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s16:int64` o concl))) THEN
  SUBGOAL_THEN `&ca div &2 pow 256 = &(val(q:int64))` SUBST_ALL_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV] THEN
    EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The subtraction of the provisional quotient estimate ***)

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC
    [18; 20; 21; 22; 23; 24; 25; 26; 27] (17--27) THEN
  MP_TAC(SPECL
   [`sum_s27:int64`;
    `&(bignum_of_wordlist[sum_s21; sum_s23; sum_s24; sum_s25]):real`;
    `256`; `4 * m + (2 EXP 256 - n)`; `2 EXP 256 + val(q:int64) * p_256`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`&(val(q:int64)) * &p_256:int <= &4 * &m - &n + &p_256`;
        `&4 * &m - &n < &(val(q:int64)):int * &p_256 + &p_256`] THEN
      REWRITE_TAC[INT_ARITH `a - b + c:int = (a + c) - b`] THEN
      REWRITE_TAC[INT_LE_SUB_LADD; INT_LT_SUB_RADD] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      SUBGOAL_THEN `n <= 2 EXP 256` MP_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN EXPAND_TAC "n" THEN
        BOUNDER_TAC[];
        SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB]] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(4 * m + 2 EXP 256 - n):real =
      &(bignum_of_wordlist [sum_s12; sum_s13; sum_s14; sum_s15; q])`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      SUBGOAL_THEN `n <= 2 EXP 256` MP_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN EXPAND_TAC "n" THEN
        BOUNDER_TAC[];
        SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB]] THEN
      UNDISCH_TAC `&2 pow 256 + &4 * &m - &n:int = &ca` THEN
      REWRITE_TAC[REAL_ARITH `a + b - c:real = d <=> a + b = c + d`] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBST1_TAC(SYM(ISPEC `q:int64` WORD_VAL)) THEN
    UNDISCH_TAC `&(val(q:int64)):int < &6` THEN
    GEN_REWRITE_TAC LAND_CONV [INT_OF_NUM_LT] THEN
    SPEC_TAC(`val(q:int64)`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(fun th ->
      (MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) th THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      (MP_TAC o end_itlist CONJ o
       filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) th THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  SUBGOAL_THEN `n <= 2 EXP 256` MP_TAC THENL
   [EXPAND_TAC "n" THEN BOUNDER_TAC[]; SIMP_TAC[GSYM REAL_OF_NUM_SUB]] THEN
  REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
   `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[REAL_ARITH `m + e - n:real < e + qp <=> m - n < qp`] THEN
  ABBREV_TAC `topcar <=> &4 * &m - &n:real < &(val(q:int64)) * &p_256` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  REWRITE_TAC[REAL_ARITH `(m + e - n) - (e + qp):real = m - n - qp`] THEN
  DISCH_TAC THEN

  (*** Final corrective masked addition ***)

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [32;34;36;38] (28--39) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(RAND_CONV BIGNUM_EXPAND_CONV)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ_BALANCED_MOD THEN
  MAP_EVERY EXISTS_TAC [`&(val(q:int64)):int`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; p_256] THEN BOUNDER_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[int_lt; int_sub_th; int_of_num_th; int_add_th] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &4 * m - n - q * p + eb
    ==> &4 * m - n = x + q * p - eb`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub38 (there is only one).                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB38_P256_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p256_montjdouble_alt_tmc) 61 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    nonoverlapping (word pc,0x14c9) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p256_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read RIP s = pcout /\
                  (n <= p_256
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s) = (&3 * &m - &8 * &n) rem &p_256))
            (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R8; R9; R10; R11; R12] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_256` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P256_MONTJDOUBLE_ALT_EXEC (1--61)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&3 * &m - &8 * &n) rem &p_256 =
    (&3 * &m + &8 * (&p_256 - &n)) rem &p_256`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [3;5;6;8] (1--8) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist[sum_s3; sum_s5; sum_s6; sum_s8]` THEN
  SUBGOAL_THEN `p_256 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_256` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_256]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Intermediate result from multiply-add block including top +1 ***)

  X86_GEN_ACCSTEPS_TAC
    (fun _ -> RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
                `word_sub x (word_neg y):int64 = word_add x y`]))
    P256_MONTJDOUBLE_ALT_EXEC [17;18;19;22;23;24;25;28;29;30;31;34;35;36;37;38]
    (9--38) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s18; sum_s24; sum_s30; sum_s36; sum_s38] =
    2 EXP 256 + (3 * m + 8 * n')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN BOUNDER_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `8 * n' =
      bignum_of_wordlist
       [word_shl sum_s3 3;
        word_subword ((word_join:int64->int64->int128) sum_s5 sum_s3) (61,64);
        word_subword ((word_join:int64->int64->int128) sum_s6 sum_s5) (61,64);
        word_subword ((word_join:int64->int64->int128) sum_s8 sum_s6) (61,64);
        word_ushr sum_s8 61]`
    SUBST1_TAC THENL
     [EXPAND_TAC "n'" THEN REWRITE_TAC[bignum_of_wordlist] THEN
      REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
      REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
      REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
      REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR;
                  BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
      ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC NUM_RING;
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV  THEN
      MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      ACCUMULATOR_POP_ASSUM_LIST
       (MP_TAC o end_itlist CONJ o
        filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = (3 * m + 8 * n') DIV 2 EXP 256` THEN
  SUBGOAL_THEN `h < 24` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV  THEN
    MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s38:int64 = word(h + 1)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[ARITH_RULE
     `ca DIV 2 EXP 256 + 1 = (2 EXP 256 + ca) DIV 2 EXP 256`] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `3 * m + 8 * n'` p256shortishredlemma) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXPAND_TAC "h" THEN SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV  THEN
    MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN BOUNDER_TAC[];
    CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Computation of 3 * m + 8 * n' - (h + 1) * p_256 ***)

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC
    [40; 42; 43; 44; 45; 46; 47; 48; 49] (39--49) THEN

  MP_TAC(SPECL
   [`sum_s49:int64`;
    `&(bignum_of_wordlist[sum_s43; sum_s45; sum_s46; sum_s47]):real`;
    `256`; `3 * m + 8 * n'`; `(h + 1) * p_256`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_256 <= (3 * m + 8 * n') + p_256`;
        `3 * m + 8 * n' < (h + 1) * p_256 + p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `&(3 * m + 8 * n'):real =
      &(bignum_of_wordlist[sum_s18; sum_s24; sum_s30; sum_s36; word (h + 1)]) -
      &2 pow 256`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN

    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `h < 24` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(fun th ->
      (MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) th THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      (MP_TAC o end_itlist CONJ o
       filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) th THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  X86_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [54;56;58;60] (50--61) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> 3 * m + 8 * n' < (h + 1) * p_256` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &(3 * m + 8 * n') - y + z
    ==> &(3 * m + 8 * n') = x + y - z`)) THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let unilemma0 = prove
 (`x = a MOD p_256 ==> x < p_256 /\ &x = &a rem &p_256`,
  REWRITE_TAC[INT_OF_NUM_REM; p_256] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_256 ==> x < p_256 /\ &x = a rem &p_256`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_256] THEN INT_ARITH_TAC);;

let lemont = prove
 (`(&i * x * y) rem &p_256 = (&i * x rem &p_256 * y rem &p_256) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let demont = prove
 (`(&(NUMERAL n) * &x) rem &p_256 = (&(NUMERAL n) * &x rem &p_256) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let pumont = prove
 (`(&(inverse_mod p_256 (2 EXP 256)) *
    (&2 pow 256 * x) rem &p_256 * (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * x * y) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * t:int == &1) (mod p)
    ==> (i * (t * x) * (t * y) == t * x * y) (mod p)`) THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2; p_256] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let dismont = prove
 (`((&2 pow 256 * x) rem &p_256 + (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * (x + y)) rem &p_256 /\
   ((&2 pow 256 * x) rem &p_256 - (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * (x - y)) rem &p_256 /\
   (&(NUMERAL n) * (&2 pow 256 * x) rem &p_256) rem &p_256 =
   (&2 pow 256 * (&(NUMERAL n) * x)) rem &p_256`,
  REPEAT CONJ_TAC THEN CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let unmont = prove
 (`(&(inverse_mod p_256 (2 EXP 256)) * (&2 pow 256 * x) rem &p_256) rem &p_256 =
   x rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * e:int == &1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent; INVERSE_MOD_LMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let unreplemma = prove
 (`!x. x < p_256
         ==> x =
             (2 EXP 256 * (inverse_mod p_256 (2 EXP 256) * x) MOD p_256) MOD
             p_256`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  ASM_REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(i * e == 1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let weierstrass_of_jacobian_p256_double = prove
 (`!P1 P2 x1 y1 z1 x3 y3 z3.
        jacobian_double_unexceptional nistp256
         (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256) =
        (x3 rem &p_256,y3 rem &p_256,z3 rem &p_256)
        ==> weierstrass_of_jacobian (integer_mod_ring p_256)
                (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256) = P1
            ==> weierstrass_of_jacobian (integer_mod_ring p_256)
                  (x3 rem &p_256,y3 rem &p_256,z3 rem &p_256) =
                group_mul p256_group P1 P1`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[nistp256; P256_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P256] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_256; b_256] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_p256 = new_definition
 `represents_p256 P (x,y,z) <=>
        x < p_256 /\ y < p_256 /\ z < p_256 /\
        weierstrass_of_jacobian (integer_mod_ring p_256)
         (tripled (montgomery_decode (256,p_256)) (x,y,z)) = P`;;

let P256_MONTJDOUBLE_ALT_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        ALL (nonoverlapping (stackpointer,192))
            [(word pc,0x14c9); (p1,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,0x14c9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST p256_montjdouble_alt_tmc) /\
                  read RIP s = word(pc + 0x10) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read RIP s = word (pc + 0x14b8) /\
                  !P. represents_p256 P t1
                      ==> represents_p256 (group_mul p256_group P P)
                            (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,192)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_MONTSQR_P256_TAC 0 ["z2";"z_1"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["y2";"y_1"] THEN
  LOCAL_SUB_P256_TAC 0 ["t2";"x_1";"z2"] THEN
  LOCAL_WEAKADD_P256_TAC 0 ["t1";"x_1";"z2"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["x2p";"t1";"t2"] THEN
  LOCAL_ADD_P256_TAC 0 ["t1";"y_1";"z_1"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["xy2";"x_1";"y2"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["x4p";"x2p"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["t1";"t1"] THEN
  LOCAL_CMSUBC9_P256_TAC 0 ["d";"xy2";"x4p"] THEN
  LOCAL_SUB_P256_TAC 0 ["t1";"t1";"z2"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["y4";"y2"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["dx2";"d";"x2p"] THEN
  LOCAL_SUB_P256_TAC 0 ["z_3";"t1";"y2"] THEN
  LOCAL_CMSUB41_P256_TAC 0 ["x_3";"xy2";"d"] THEN
  LOCAL_CMSUB38_P256_TAC 0 ["y_3";"dx2";"y4"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s16" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  X_GEN_TAC `P:(int#int)option` THEN
  REWRITE_TAC[represents_p256; tripled] THEN
  REWRITE_TAC[montgomery_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_256] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_256]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (MP_TAC o C SPEC unreplemma) [`z1:num`; `y1:num`; `x1:num`] THEN
  MAP_EVERY (fun t -> ABBREV_TAC t THEN POP_ASSUM(K ALL_TAC))
   [`x1d = inverse_mod p_256 (2 EXP 256) * x1`;
    `y1d = inverse_mod p_256 (2 EXP 256) * y1`;
    `z1d = inverse_mod p_256 (2 EXP 256) * z1`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(CONV_RULE INT_REM_DOWN_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_POW_2]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_ADD_REM; GSYM INT_SUB_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[lemont; demont]) THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[INT_REM_REM] THEN
  REWRITE_TAC[pumont; dismont; unmont] THEN
  FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl)) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_p256_double THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_double_unexceptional; nistp256;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let P256_MONTJDOUBLE_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 232),232))
            [(word pc,LENGTH p256_montjdouble_alt_tmc); (p1,96)] /\
        ALL (nonoverlapping (p3,96))
            [(word pc,LENGTH p256_montjdouble_alt_tmc); (word_sub stackpointer (word 232),240)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p256_montjdouble_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p256 P t1
                      ==> represents_p256 (group_mul p256_group P P)
                            (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 232),232)])`,
  X86_PROMOTE_RETURN_STACK_TAC p256_montjdouble_alt_tmc P256_MONTJDOUBLE_ALT_CORRECT
    `[RBX; R12; R13; R14; R15]` 232);;

let P256_MONTJDOUBLE_ALT_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 232),232))
            [(word pc,LENGTH p256_montjdouble_alt_mc); (p1,96)] /\
        ALL (nonoverlapping (p3,96))
            [(word pc,LENGTH p256_montjdouble_alt_mc); (word_sub stackpointer (word 232),240)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p256_montjdouble_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p256 P t1
                      ==> represents_p256 (group_mul p256_group P P)
                            (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 232),232)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE P256_MONTJDOUBLE_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let p256_montjdouble_alt_windows_mc = define_from_elf "p256_montjdouble_alt_windows_mc"
      "x86/p256/p256_montjdouble_alt.obj";;

let p256_montjdouble_alt_windows_tmc = define_trimmed "p256_montjdouble_alt_windows_tmc" p256_montjdouble_alt_windows_mc;;

let P256_MONTJDOUBLE_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 248),248))
            [(word pc,LENGTH p256_montjdouble_alt_windows_tmc); (p1,96)] /\
        ALL (nonoverlapping (p3,96))
            [(word pc,LENGTH p256_montjdouble_alt_windows_tmc); (word_sub stackpointer (word 248),256)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p256_montjdouble_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p256 P t1
                      ==> represents_p256 (group_mul p256_group P P)
                            (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 248),248)])`,
  WINDOWS_X86_WRAP_STACK_TAC
    p256_montjdouble_alt_windows_tmc p256_montjdouble_alt_tmc
    P256_MONTJDOUBLE_ALT_CORRECT
    `[RBX; R12; R13; R14; R15]` 232);;

let P256_MONTJDOUBLE_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 248),248))
            [(word pc,LENGTH p256_montjdouble_alt_windows_mc); (p1,96)] /\
        ALL (nonoverlapping (p3,96))
            [(word pc,LENGTH p256_montjdouble_alt_windows_mc); (word_sub stackpointer (word 248),256)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p256_montjdouble_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p256 P t1
                      ==> represents_p256 (group_mul p256_group P P)
                            (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 248),248)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE P256_MONTJDOUBLE_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

