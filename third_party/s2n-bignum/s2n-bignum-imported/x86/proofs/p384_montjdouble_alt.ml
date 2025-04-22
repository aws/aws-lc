(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point doubling in Montgomery-Jacobian coordinates for NIST P-384 curve.   *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp384.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "x86/p384/p384_montjdouble_alt.o";;
 ****)

let p384_montjdouble_alt_mc = define_assert_from_elf
  "p384_montjdouble_alt_mc" "x86/p384/p384_montjdouble_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0x58; 0x01; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 344)) *)
  0x48; 0x89; 0xbc; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% rdi) *)
  0x48; 0x8b; 0x5e; 0x60;  (* MOV (% rbx) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0x8b; 0x46; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0x8b; 0x86; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,136))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0x89; 0xd6;        (* MOV (% r14) (% rdx) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0xa6; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,128))) *)
  0x49; 0x89; 0xc7;        (* MOV (% r15) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x5e; 0x70;  (* MOV (% rbx) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0x8b; 0x46; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x5e; 0x68;  (* MOV (% rbx) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x86; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,128))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x86; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,136))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9e; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsi,128))) *)
  0x48; 0x8b; 0x46; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x5e; 0x70;  (* MOV (% rbx) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x86; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,128))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x86; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,136))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0xa6; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,136))) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x48; 0x8b; 0x86; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,128))) *)
  0x48; 0xf7; 0xa6; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,136))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x48; 0x11; 0xed;        (* ADC (% rbp) (% rbp) *)
  0x45; 0x11; 0xc0;        (* ADC (% r8d) (% r8d) *)
  0x48; 0x8b; 0x46; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x8b; 0x46; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0x89; 0x6c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rbp) *)
  0x49; 0x01; 0xd1;        (* ADD (% r9) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x86; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,128))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x86; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,136))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x48; 0x13; 0x44; 0x24; 0x08;
                           (* ADC (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x13; 0x14; 0x24;  (* ADC (% rdx) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x89; 0xd7;        (* MOV (% rdi) (% rdx) *)
  0x48; 0x89; 0x1c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rbx) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc3;        (* ADD (% rbx) (% r8) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xc1;        (* SUB (% r9) (% r8) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd8;        (* MOV (% r8) (% rbx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xcb;        (* ADD (% rbx) (% r9) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xca;        (* SUB (% r10) (% r9) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xc4;        (* SBB (% r12) (% rax) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd3;        (* MOV (% rbx) (% r10) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd3;        (* ADD (% rbx) (% r10) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xd3;        (* SUB (% r11) (% r10) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x49; 0x19; 0xc5;        (* SBB (% r13) (% rax) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x89; 0xda;        (* MOV (% r10) (% rbx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xdb;        (* MOV (% rbx) (% r11) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xdb;        (* ADD (% rbx) (% r11) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xdc;        (* SUB (% r12) (% r11) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x49; 0x19; 0xc0;        (* SBB (% r8) (% rax) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdb;        (* MOV (% r11) (% rbx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe3;        (* ADD (% rbx) (% r12) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xe5;        (* SUB (% r13) (% r12) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xc1;        (* SBB (% r9) (% rax) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xeb;        (* ADD (% rbx) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xe8;        (* SUB (% r8) (% r13) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xc2;        (* SBB (% r10) (% rax) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdd;        (* MOV (% r13) (% rbx) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x1c; 0x24;  (* MOV (% rbx) (Memop Quadword (%% (rsp,0))) *)
  0x4d; 0x01; 0xc6;        (* ADD (% r14) (% r8) *)
  0x4d; 0x11; 0xcf;        (* ADC (% r15) (% r9) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x11; 0xdb;        (* ADC (% rbx) (% r11) *)
  0x4c; 0x11; 0xe5;        (* ADC (% rbp) (% r12) *)
  0x4c; 0x11; 0xef;        (* ADC (% rdi) (% r13) *)
  0x41; 0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 0)) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x41; 0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r9d) (Imm32 (word 4294967295)) *)
  0x4d; 0x11; 0xf9;        (* ADC (% r9) (% r15) *)
  0x41; 0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 1)) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x49; 0x11; 0xfd;        (* ADC (% r13) (% rdi) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x0f; 0x45; 0xf0;  (* CMOVNE (% r14) (% rax) *)
  0x4d; 0x0f; 0x45; 0xf9;  (* CMOVNE (% r15) (% r9) *)
  0x49; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% r10) *)
  0x49; 0x0f; 0x45; 0xdb;  (* CMOVNE (% rbx) (% r11) *)
  0x49; 0x0f; 0x45; 0xec;  (* CMOVNE (% rbp) (% r12) *)
  0x49; 0x0f; 0x45; 0xfd;  (* CMOVNE (% rdi) (% r13) *)
  0x4c; 0x89; 0x34; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r15) *)
  0x48; 0x89; 0x4c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rcx) *)
  0x48; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rbx) *)
  0x48; 0x89; 0x6c; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rbp) *)
  0x48; 0x89; 0x7c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rdi) *)
  0x48; 0x8b; 0x5e; 0x30;  (* MOV (% rbx) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0x89; 0xd6;        (* MOV (% r14) (% rdx) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0x66; 0x50;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,80))) *)
  0x49; 0x89; 0xc7;        (* MOV (% r15) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x5e; 0x40;  (* MOV (% rbx) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x5e; 0x38;  (* MOV (% rbx) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5e; 0x50;  (* MOV (% rbx) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x5e; 0x40;  (* MOV (% rbx) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0x66; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0x66; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x48; 0x11; 0xed;        (* ADC (% rbp) (% rbp) *)
  0x45; 0x11; 0xc0;        (* ADC (% r8d) (% r8d) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x4c; 0x89; 0x44; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r8) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x89; 0x6c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rbp) *)
  0x49; 0x01; 0xd1;        (* ADD (% r9) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x48; 0x13; 0x44; 0x24; 0x38;
                           (* ADC (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x13; 0x54; 0x24; 0x30;
                           (* ADC (% rdx) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x89; 0xd7;        (* MOV (% rdi) (% rdx) *)
  0x48; 0x89; 0x5c; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rbx) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc3;        (* ADD (% rbx) (% r8) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xc1;        (* SUB (% r9) (% r8) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd8;        (* MOV (% r8) (% rbx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xcb;        (* ADD (% rbx) (% r9) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xca;        (* SUB (% r10) (% r9) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xc4;        (* SBB (% r12) (% rax) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd3;        (* MOV (% rbx) (% r10) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd3;        (* ADD (% rbx) (% r10) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xd3;        (* SUB (% r11) (% r10) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x49; 0x19; 0xc5;        (* SBB (% r13) (% rax) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x89; 0xda;        (* MOV (% r10) (% rbx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xdb;        (* MOV (% rbx) (% r11) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xdb;        (* ADD (% rbx) (% r11) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xdc;        (* SUB (% r12) (% r11) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x49; 0x19; 0xc0;        (* SBB (% r8) (% rax) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdb;        (* MOV (% r11) (% rbx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe3;        (* ADD (% rbx) (% r12) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xe5;        (* SUB (% r13) (% r12) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xc1;        (* SBB (% r9) (% rax) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xeb;        (* ADD (% rbx) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xe8;        (* SUB (% r8) (% r13) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xc2;        (* SBB (% r10) (% rax) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdd;        (* MOV (% r13) (% rbx) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5c; 0x24; 0x30;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,48))) *)
  0x4d; 0x01; 0xc6;        (* ADD (% r14) (% r8) *)
  0x4d; 0x11; 0xcf;        (* ADC (% r15) (% r9) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x11; 0xdb;        (* ADC (% rbx) (% r11) *)
  0x4c; 0x11; 0xe5;        (* ADC (% rbp) (% r12) *)
  0x4c; 0x11; 0xef;        (* ADC (% rdi) (% r13) *)
  0x41; 0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 0)) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x41; 0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r9d) (Imm32 (word 4294967295)) *)
  0x4d; 0x11; 0xf9;        (* ADC (% r9) (% r15) *)
  0x41; 0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 1)) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x49; 0x11; 0xfd;        (* ADC (% r13) (% rdi) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x0f; 0x45; 0xf0;  (* CMOVNE (% r14) (% rax) *)
  0x4d; 0x0f; 0x45; 0xf9;  (* CMOVNE (% r15) (% r9) *)
  0x49; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% r10) *)
  0x49; 0x0f; 0x45; 0xdb;  (* CMOVNE (% rbx) (% r11) *)
  0x49; 0x0f; 0x45; 0xec;  (* CMOVNE (% rbp) (% r12) *)
  0x49; 0x0f; 0x45; 0xfd;  (* CMOVNE (% rdi) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0x48; 0x89; 0x4c; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rcx) *)
  0x48; 0x89; 0x5c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rbx) *)
  0x48; 0x89; 0x6c; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rbp) *)
  0x48; 0x89; 0x7c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rdi) *)
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
  0x4c; 0x8b; 0x56; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x13; 0x54; 0x24; 0x20;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x5e; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x28;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x19; 0xd2;        (* SBB (% rdx) (% rdx) *)
  0xbb; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 1)) *)
  0x48; 0x21; 0xd3;        (* AND (% rbx) (% rdx) *)
  0xbd; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebp) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xea;        (* AND (% rdx) (% rbp) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x48; 0x29; 0xd5;        (* SUB (% rbp) (% rdx) *)
  0x48; 0x01; 0xe8;        (* ADD (% rax) (% rbp) *)
  0x48; 0x89; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x89; 0x8c; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% rcx) *)
  0x49; 0x11; 0xd8;        (* ADC (% r8) (% rbx) *)
  0x4c; 0x89; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r8) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r9) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r10) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x2b; 0x04; 0x24;  (* SUB (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x1b; 0x54; 0x24; 0x08;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x10;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x18;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x8b; 0x56; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x20;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x5e; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x1b; 0x5c; 0x24; 0x28;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x48; 0x29; 0xcb;        (* SUB (% rbx) (% rcx) *)
  0x48; 0x29; 0xd8;        (* SUB (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rax) *)
  0x48; 0x19; 0xca;        (* SBB (% rdx) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% rdx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% r11) *)
  0x48; 0x8b; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,192))) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc3;        (* ADD (% rbx) (% r8) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xeb;        (* SBB (% r11) (% rbp) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xde;        (* ADD (% r14) (% rbx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x49; 0xf7; 0xd8;        (* NEG (% r8) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xcb;        (* ADD (% rbx) (% r9) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xc8;        (* ADD (% rax) (% r9) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xec;        (* SBB (% r12) (% rbp) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xdf;        (* ADD (% r15) (% rbx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x4c; 0x89; 0xd3;        (* MOV (% rbx) (% r10) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd3;        (* ADD (% rbx) (% r10) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x49; 0x19; 0xed;        (* SBB (% r13) (% rbp) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd8;        (* ADD (% r8) (% rbx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x49; 0xf7; 0xda;        (* NEG (% r10) *)
  0x4c; 0x89; 0xdb;        (* MOV (% rbx) (% r11) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xdb;        (* ADD (% rbx) (% r11) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc4;        (* SUB (% r12) (% rax) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x49; 0x19; 0xee;        (* SBB (% r14) (% rbp) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd9;        (* ADD (% r9) (% rbx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,224))) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x49; 0xf7; 0xdb;        (* NEG (% r11) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe3;        (* ADD (% rbx) (% r12) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xe0;        (* ADD (% rax) (% r12) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc5;        (* SUB (% r13) (% rax) *)
  0x49; 0x19; 0xd6;        (* SBB (% r14) (% rdx) *)
  0x49; 0x19; 0xef;        (* SBB (% r15) (% rbp) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xda;        (* ADD (% r10) (% rbx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,232))) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x49; 0xf7; 0xdc;        (* NEG (% r12) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xeb;        (* ADD (% rbx) (% r13) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xe8;        (* ADD (% rax) (% r13) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc6;        (* SUB (% r14) (% rax) *)
  0x49; 0x19; 0xd7;        (* SBB (% r15) (% rdx) *)
  0x49; 0x19; 0xe8;        (* SBB (% r8) (% rbp) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xdb;        (* ADD (% r11) (% rbx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0x4c; 0x11; 0xfb;        (* ADC (% rbx) (% r15) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x11; 0xc1;        (* ADC (% rcx) (% r8) *)
  0x4c; 0x11; 0xca;        (* ADC (% rdx) (% r9) *)
  0x4c; 0x11; 0xd5;        (* ADC (% rbp) (% r10) *)
  0x4d; 0x11; 0xdd;        (* ADC (% r13) (% r11) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4c; 0x0f; 0x45; 0xf0;  (* CMOVNE (% r14) (% rax) *)
  0x4c; 0x0f; 0x45; 0xfb;  (* CMOVNE (% r15) (% rbx) *)
  0x4c; 0x0f; 0x45; 0xc1;  (* CMOVNE (% r8) (% rcx) *)
  0x4c; 0x0f; 0x45; 0xca;  (* CMOVNE (% r9) (% rdx) *)
  0x4c; 0x0f; 0x45; 0xd5;  (* CMOVNE (% r10) (% rbp) *)
  0x4d; 0x0f; 0x45; 0xdd;  (* CMOVNE (% r11) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r15) *)
  0x4c; 0x89; 0x44; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r11) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x03; 0x46; 0x60;  (* ADD (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0x8b; 0x4e; 0x38;  (* MOV (% rcx) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x13; 0x4e; 0x68;  (* ADC (% rcx) (Memop Quadword (%% (rsi,104))) *)
  0x4c; 0x8b; 0x46; 0x40;  (* MOV (% r8) (Memop Quadword (%% (rsi,64))) *)
  0x4c; 0x13; 0x46; 0x70;  (* ADC (% r8) (Memop Quadword (%% (rsi,112))) *)
  0x4c; 0x8b; 0x4e; 0x48;  (* MOV (% r9) (Memop Quadword (%% (rsi,72))) *)
  0x4c; 0x13; 0x4e; 0x78;  (* ADC (% r9) (Memop Quadword (%% (rsi,120))) *)
  0x4c; 0x8b; 0x56; 0x50;  (* MOV (% r10) (Memop Quadword (%% (rsi,80))) *)
  0x4c; 0x13; 0x96; 0x80; 0x00; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsi,128))) *)
  0x4c; 0x8b; 0x5e; 0x58;  (* MOV (% r11) (Memop Quadword (%% (rsi,88))) *)
  0x4c; 0x13; 0x9e; 0x88; 0x00; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsi,136))) *)
  0xba; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 0)) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x48; 0xbd; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rbp) (Imm64 (word 18446744069414584321)) *)
  0x48; 0x01; 0xe8;        (* ADD (% rax) (% rbp) *)
  0xbd; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebp) (Imm32 (word 4294967295)) *)
  0x48; 0x11; 0xe9;        (* ADC (% rcx) (% rbp) *)
  0x49; 0x83; 0xd0; 0x01;  (* ADC (% r8) (Imm8 (word 1)) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd2; 0xff;  (* ADC (% rdx) (Imm8 (word 255)) *)
  0xbb; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 1)) *)
  0x48; 0x21; 0xd3;        (* AND (% rbx) (% rdx) *)
  0x48; 0x21; 0xea;        (* AND (% rdx) (% rbp) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x48; 0x29; 0xd5;        (* SUB (% rbp) (% rdx) *)
  0x48; 0x29; 0xe8;        (* SUB (% rax) (% rbp) *)
  0x48; 0x89; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% rax) *)
  0x48; 0x19; 0xd1;        (* SBB (% rcx) (% rdx) *)
  0x48; 0x89; 0x8c; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% rcx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% r11) *)
  0x48; 0x8b; 0x5c; 0x24; 0x60;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0x89; 0xd6;        (* MOV (% r14) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x89; 0xc7;        (* MOV (% r15) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x5c; 0x24; 0x70;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x5c; 0x24; 0x68;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x5c; 0x24; 0x70;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x48; 0x11; 0xed;        (* ADC (% rbp) (% rbp) *)
  0x45; 0x11; 0xc0;        (* ADC (% r8d) (% r8d) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x4c; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% r8) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0x89; 0xac; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% rbp) *)
  0x49; 0x01; 0xd1;        (* ADD (% r9) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x48; 0x13; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* ADC (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0x13; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* ADC (% rdx) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x89; 0xd7;        (* MOV (% rdi) (% rdx) *)
  0x48; 0x89; 0x9c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% rbx) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc3;        (* ADD (% rbx) (% r8) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xc1;        (* SUB (% r9) (% r8) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd8;        (* MOV (% r8) (% rbx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xcb;        (* ADD (% rbx) (% r9) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xca;        (* SUB (% r10) (% r9) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xc4;        (* SBB (% r12) (% rax) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd3;        (* MOV (% rbx) (% r10) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd3;        (* ADD (% rbx) (% r10) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xd3;        (* SUB (% r11) (% r10) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x49; 0x19; 0xc5;        (* SBB (% r13) (% rax) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x89; 0xda;        (* MOV (% r10) (% rbx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xdb;        (* MOV (% rbx) (% r11) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xdb;        (* ADD (% rbx) (% r11) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xdc;        (* SUB (% r12) (% r11) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x49; 0x19; 0xc0;        (* SBB (% r8) (% rax) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdb;        (* MOV (% r11) (% rbx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe3;        (* ADD (% rbx) (% r12) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xe5;        (* SUB (% r13) (% r12) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xc1;        (* SBB (% r9) (% rax) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xeb;        (* ADD (% rbx) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xe8;        (* SUB (% r8) (% r13) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xc2;        (* SBB (% r10) (% rax) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdd;        (* MOV (% r13) (% rbx) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,288))) *)
  0x4d; 0x01; 0xc6;        (* ADD (% r14) (% r8) *)
  0x4d; 0x11; 0xcf;        (* ADC (% r15) (% r9) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x11; 0xdb;        (* ADC (% rbx) (% r11) *)
  0x4c; 0x11; 0xe5;        (* ADC (% rbp) (% r12) *)
  0x4c; 0x11; 0xef;        (* ADC (% rdi) (% r13) *)
  0x41; 0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 0)) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x41; 0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r9d) (Imm32 (word 4294967295)) *)
  0x4d; 0x11; 0xf9;        (* ADC (% r9) (% r15) *)
  0x41; 0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 1)) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x49; 0x11; 0xfd;        (* ADC (% r13) (% rdi) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x0f; 0x45; 0xf0;  (* CMOVNE (% r14) (% rax) *)
  0x4d; 0x0f; 0x45; 0xf9;  (* CMOVNE (% r15) (% r9) *)
  0x49; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% r10) *)
  0x49; 0x0f; 0x45; 0xdb;  (* CMOVNE (% rbx) (% r11) *)
  0x49; 0x0f; 0x45; 0xec;  (* CMOVNE (% rbp) (% r12) *)
  0x49; 0x0f; 0x45; 0xfd;  (* CMOVNE (% rdi) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% r15) *)
  0x48; 0x89; 0x8c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% rcx) *)
  0x48; 0x89; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% rbx) *)
  0x48; 0x89; 0xac; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% rbp) *)
  0x48; 0x89; 0xbc; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% rdi) *)
  0x48; 0x8b; 0x5c; 0x24; 0x30;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,48))) *)
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
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xeb;        (* SBB (% r11) (% rbp) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xde;        (* ADD (% r14) (% rbx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5c; 0x24; 0x38;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,56))) *)
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
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xc8;        (* ADD (% rax) (% r9) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xec;        (* SBB (% r12) (% rbp) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xdf;        (* ADD (% r15) (% rbx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5c; 0x24; 0x40;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,64))) *)
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
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x49; 0x19; 0xed;        (* SBB (% r13) (% rbp) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd8;        (* ADD (% r8) (% rbx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5c; 0x24; 0x48;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,72))) *)
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
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc4;        (* SUB (% r12) (% rax) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x49; 0x19; 0xee;        (* SBB (% r14) (% rbp) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd9;        (* ADD (% r9) (% rbx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5c; 0x24; 0x50;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x49; 0xf7; 0xdb;        (* NEG (% r11) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe3;        (* ADD (% rbx) (% r12) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xe0;        (* ADD (% rax) (% r12) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc5;        (* SUB (% r13) (% rax) *)
  0x49; 0x19; 0xd6;        (* SBB (% r14) (% rdx) *)
  0x49; 0x19; 0xef;        (* SBB (% r15) (% rbp) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xda;        (* ADD (% r10) (% rbx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5c; 0x24; 0x58;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x49; 0xf7; 0xdc;        (* NEG (% r12) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xeb;        (* ADD (% rbx) (% r13) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xe8;        (* ADD (% rax) (% r13) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc6;        (* SUB (% r14) (% rax) *)
  0x49; 0x19; 0xd7;        (* SBB (% r15) (% rdx) *)
  0x49; 0x19; 0xe8;        (* SBB (% r8) (% rbp) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xdb;        (* ADD (% r11) (% rbx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0x4c; 0x11; 0xfb;        (* ADC (% rbx) (% r15) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x11; 0xc1;        (* ADC (% rcx) (% r8) *)
  0x4c; 0x11; 0xca;        (* ADC (% rdx) (% r9) *)
  0x4c; 0x11; 0xd5;        (* ADC (% rbp) (% r10) *)
  0x4d; 0x11; 0xdd;        (* ADC (% r13) (% r11) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4c; 0x0f; 0x45; 0xf0;  (* CMOVNE (% r14) (% rax) *)
  0x4c; 0x0f; 0x45; 0xfb;  (* CMOVNE (% r15) (% rbx) *)
  0x4c; 0x0f; 0x45; 0xc1;  (* CMOVNE (% r8) (% rcx) *)
  0x4c; 0x0f; 0x45; 0xca;  (* CMOVNE (% r9) (% rdx) *)
  0x4c; 0x0f; 0x45; 0xd5;  (* CMOVNE (% r10) (% rbp) *)
  0x4d; 0x0f; 0x45; 0xdd;  (* CMOVNE (% r11) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r15) *)
  0x4c; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r11) *)
  0x48; 0x8b; 0x9c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0x89; 0xd6;        (* MOV (% r14) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,272))) *)
  0x49; 0x89; 0xc7;        (* MOV (% r15) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x9c; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x48; 0x11; 0xed;        (* ADC (% rbp) (% rbp) *)
  0x45; 0x11; 0xc0;        (* ADC (% r8d) (% r8d) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x4c; 0x89; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% r8) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0x89; 0xac; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% rbp) *)
  0x49; 0x01; 0xd1;        (* ADD (% r9) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x48; 0x13; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* ADC (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0x13; 0x94; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* ADC (% rdx) (Memop Quadword (%% (rsp,192))) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x89; 0xd7;        (* MOV (% rdi) (% rdx) *)
  0x48; 0x89; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rbx) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc3;        (* ADD (% rbx) (% r8) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xc1;        (* SUB (% r9) (% r8) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd8;        (* MOV (% r8) (% rbx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xcb;        (* ADD (% rbx) (% r9) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xca;        (* SUB (% r10) (% r9) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xc4;        (* SBB (% r12) (% rax) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd3;        (* MOV (% rbx) (% r10) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd3;        (* ADD (% rbx) (% r10) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xd3;        (* SUB (% r11) (% r10) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x49; 0x19; 0xc5;        (* SBB (% r13) (% rax) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x89; 0xda;        (* MOV (% r10) (% rbx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xdb;        (* MOV (% rbx) (% r11) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xdb;        (* ADD (% rbx) (% r11) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xdc;        (* SUB (% r12) (% r11) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x49; 0x19; 0xc0;        (* SBB (% r8) (% rax) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdb;        (* MOV (% r11) (% rbx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe3;        (* ADD (% rbx) (% r12) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xe5;        (* SUB (% r13) (% r12) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xc1;        (* SBB (% r9) (% rax) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xeb;        (* ADD (% rbx) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xe8;        (* SUB (% r8) (% r13) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xc2;        (* SBB (% r10) (% rax) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdd;        (* MOV (% r13) (% rbx) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,192))) *)
  0x4d; 0x01; 0xc6;        (* ADD (% r14) (% r8) *)
  0x4d; 0x11; 0xcf;        (* ADC (% r15) (% r9) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x11; 0xdb;        (* ADC (% rbx) (% r11) *)
  0x4c; 0x11; 0xe5;        (* ADC (% rbp) (% r12) *)
  0x4c; 0x11; 0xef;        (* ADC (% rdi) (% r13) *)
  0x41; 0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 0)) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x41; 0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r9d) (Imm32 (word 4294967295)) *)
  0x4d; 0x11; 0xf9;        (* ADC (% r9) (% r15) *)
  0x41; 0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 1)) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x49; 0x11; 0xfd;        (* ADC (% r13) (% rdi) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x0f; 0x45; 0xf0;  (* CMOVNE (% r14) (% rax) *)
  0x4d; 0x0f; 0x45; 0xf9;  (* CMOVNE (% r15) (% r9) *)
  0x49; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% r10) *)
  0x49; 0x0f; 0x45; 0xdb;  (* CMOVNE (% rbx) (% r11) *)
  0x49; 0x0f; 0x45; 0xec;  (* CMOVNE (% rbp) (% r12) *)
  0x49; 0x0f; 0x45; 0xfd;  (* CMOVNE (% rdi) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r15) *)
  0x48; 0x89; 0x8c; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% rcx) *)
  0x48; 0x89; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% rbx) *)
  0x48; 0x89; 0xac; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% rbp) *)
  0x48; 0x89; 0xbc; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% rdi) *)
  0x49; 0xb9; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Imm64 (word 4294967295)) *)
  0x4c; 0x2b; 0x8c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* SUB (% r9) (Memop Quadword (%% (rsp,288))) *)
  0x49; 0xba; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10) (Imm64 (word 18446744069414584320)) *)
  0x4c; 0x1b; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,296))) *)
  0x49; 0xc7; 0xc3; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11) (Imm32 (word 4294967294)) *)
  0x4c; 0x1b; 0x9c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,304))) *)
  0x49; 0xc7; 0xc4; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r12) (Imm32 (word 4294967295)) *)
  0x4c; 0x1b; 0xa4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,312))) *)
  0x49; 0xc7; 0xc5; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r13) (Imm32 (word 4294967295)) *)
  0x4c; 0x1b; 0xac; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,320))) *)
  0x49; 0xc7; 0xc6; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r14) (Imm32 (word 4294967295)) *)
  0x4c; 0x1b; 0xb4; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,328))) *)
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
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x41; 0xbe; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r14d) (Imm32 (word 1)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0xb9; 0x0c; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 12)) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x11; 0xf2;        (* ADC (% r10) (% r14) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x48; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% rdx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd1;        (* NOT (% rcx) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x21; 0xca;        (* AND (% rdx) (% rcx) *)
  0x48; 0x29; 0xd0;        (* SUB (% rax) (% rdx) *)
  0x48; 0x83; 0xe1; 0x01;  (* AND (% rcx) (Imm8 (word 1)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x4c; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% r8) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x4c; 0x89; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% r9) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x4c; 0x89; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x48; 0x2b; 0x04; 0x24;  (* SUB (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x94; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0x1b; 0x54; 0x24; 0x08;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,208))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x10;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,216))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x18;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x8b; 0x94; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,224))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x20;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,232))) *)
  0x4c; 0x1b; 0x5c; 0x24; 0x28;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x48; 0x29; 0xcb;        (* SUB (% rbx) (% rcx) *)
  0x48; 0x29; 0xd8;        (* SUB (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% rax) *)
  0x48; 0x19; 0xca;        (* SBB (% rdx) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% rdx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% r11) *)
  0x48; 0x8b; 0x5c; 0x24; 0x30;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0x89; 0xd6;        (* MOV (% r14) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x89; 0xc7;        (* MOV (% r15) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x5c; 0x24; 0x40;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x5c; 0x24; 0x38;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5c; 0x24; 0x50;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x5c; 0x24; 0x40;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x4d; 0x01; 0xc9;        (* ADD (% r9) (% r9) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x48; 0x11; 0xed;        (* ADC (% rbp) (% rbp) *)
  0x45; 0x11; 0xc0;        (* ADC (% r8d) (% r8d) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x4c; 0x89; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% r8) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x89; 0xac; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% rbp) *)
  0x49; 0x01; 0xd1;        (* ADD (% r9) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x48; 0x13; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* ADC (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0x13; 0x94; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* ADC (% rdx) (Memop Quadword (%% (rsp,192))) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x89; 0xd7;        (* MOV (% rdi) (% rdx) *)
  0x48; 0x89; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rbx) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc3;        (* ADD (% rbx) (% r8) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xc1;        (* SUB (% r9) (% r8) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd8;        (* MOV (% r8) (% rbx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xcb;        (* ADD (% rbx) (% r9) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xca;        (* SUB (% r10) (% r9) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xc4;        (* SBB (% r12) (% rax) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd3;        (* MOV (% rbx) (% r10) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd3;        (* ADD (% rbx) (% r10) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xd3;        (* SUB (% r11) (% r10) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x49; 0x19; 0xc5;        (* SBB (% r13) (% rax) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x89; 0xda;        (* MOV (% r10) (% rbx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xdb;        (* MOV (% rbx) (% r11) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xdb;        (* ADD (% rbx) (% r11) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xdc;        (* SUB (% r12) (% r11) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x49; 0x19; 0xc0;        (* SBB (% r8) (% rax) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdb;        (* MOV (% r11) (% rbx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe3;        (* ADD (% rbx) (% r12) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xe5;        (* SUB (% r13) (% r12) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xc1;        (* SBB (% r9) (% rax) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xeb;        (* ADD (% rbx) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xc0;              (* ADC (% eax) (% eax) *)
  0x4d; 0x29; 0xe8;        (* SUB (% r8) (% r13) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xc2;        (* SBB (% r10) (% rax) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x89; 0xdd;        (* MOV (% r13) (% rbx) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,192))) *)
  0x4d; 0x01; 0xc6;        (* ADD (% r14) (% r8) *)
  0x4d; 0x11; 0xcf;        (* ADC (% r15) (% r9) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x11; 0xdb;        (* ADC (% rbx) (% r11) *)
  0x4c; 0x11; 0xe5;        (* ADC (% rbp) (% r12) *)
  0x4c; 0x11; 0xef;        (* ADC (% rdi) (% r13) *)
  0x41; 0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 0)) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x41; 0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r9d) (Imm32 (word 4294967295)) *)
  0x4d; 0x11; 0xf9;        (* ADC (% r9) (% r15) *)
  0x41; 0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 1)) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x49; 0x11; 0xfd;        (* ADC (% r13) (% rdi) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x0f; 0x45; 0xf0;  (* CMOVNE (% r14) (% rax) *)
  0x4d; 0x0f; 0x45; 0xf9;  (* CMOVNE (% r15) (% r9) *)
  0x49; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% r10) *)
  0x49; 0x0f; 0x45; 0xdb;  (* CMOVNE (% rbx) (% r11) *)
  0x49; 0x0f; 0x45; 0xec;  (* CMOVNE (% rbp) (% r12) *)
  0x49; 0x0f; 0x45; 0xfd;  (* CMOVNE (% rdi) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r15) *)
  0x48; 0x89; 0x8c; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% rcx) *)
  0x48; 0x89; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% rbx) *)
  0x48; 0x89; 0xac; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% rbp) *)
  0x48; 0x89; 0xbc; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% rdi) *)
  0x48; 0x8b; 0xbc; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,336))) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0x2b; 0x44; 0x24; 0x30;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x8b; 0x94; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0x1b; 0x54; 0x24; 0x38;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,256))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x40;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,264))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x48;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,272))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x50;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,280))) *)
  0x4c; 0x1b; 0x5c; 0x24; 0x58;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x48; 0x29; 0xcb;        (* SUB (% rbx) (% rcx) *)
  0x48; 0x29; 0xd8;        (* SUB (% rax) (% rbx) *)
  0x48; 0x89; 0x47; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% rax) *)
  0x48; 0x19; 0xca;        (* SBB (% rdx) (% rcx) *)
  0x48; 0x89; 0x57; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% rdx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x4c; 0x89; 0x47; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4f; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x97; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,128))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,136))) (% r11) *)
  0x48; 0x8b; 0x5c; 0x24; 0x60;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc3;        (* ADD (% rbx) (% r8) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xeb;        (* SBB (% r11) (% rbp) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xde;        (* ADD (% r14) (% rbx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5c; 0x24; 0x68;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x49; 0xf7; 0xd8;        (* NEG (% r8) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xcb;        (* ADD (% rbx) (% r9) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xc8;        (* ADD (% rax) (% r9) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xec;        (* SBB (% r12) (% rbp) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xdf;        (* ADD (% r15) (% rbx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5c; 0x24; 0x70;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xca;        (* SUB (% rdx) (% r9) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x4c; 0x89; 0xd3;        (* MOV (% rbx) (% r10) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd3;        (* ADD (% rbx) (% r10) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x49; 0x19; 0xed;        (* SBB (% r13) (% rbp) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd8;        (* ADD (% r8) (% rbx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5c; 0x24; 0x78;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x49; 0xf7; 0xda;        (* NEG (% r10) *)
  0x4c; 0x89; 0xdb;        (* MOV (% rbx) (% r11) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xdb;        (* ADD (% rbx) (% r11) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc4;        (* SUB (% r12) (% rax) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x49; 0x19; 0xee;        (* SBB (% r14) (% rbp) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd9;        (* ADD (% r9) (% rbx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x49; 0xf7; 0xdb;        (* NEG (% r11) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe3;        (* ADD (% rbx) (% r12) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xe0;        (* ADD (% rax) (% r12) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc5;        (* SUB (% r13) (% rax) *)
  0x49; 0x19; 0xd6;        (* SBB (% r14) (% rdx) *)
  0x49; 0x19; 0xef;        (* SBB (% r15) (% rbp) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xda;        (* ADD (% r10) (% rbx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x9c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x49; 0xf7; 0xdc;        (* NEG (% r12) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xeb;        (* ADD (% rbx) (% r13) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967295)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x01; 0xe8;        (* ADD (% rax) (% r13) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc6;        (* SUB (% r14) (% rax) *)
  0x49; 0x19; 0xd7;        (* SBB (% r15) (% rdx) *)
  0x49; 0x19; 0xe8;        (* SBB (% r8) (% rbp) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xdb;        (* ADD (% r11) (% rbx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0x4c; 0x11; 0xfb;        (* ADC (% rbx) (% r15) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x11; 0xc1;        (* ADC (% rcx) (% r8) *)
  0x4c; 0x11; 0xca;        (* ADC (% rdx) (% r9) *)
  0x4c; 0x11; 0xd5;        (* ADC (% rbp) (% r10) *)
  0x4d; 0x11; 0xdd;        (* ADC (% r13) (% r11) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4c; 0x0f; 0x45; 0xf0;  (* CMOVNE (% r14) (% rax) *)
  0x4c; 0x0f; 0x45; 0xfb;  (* CMOVNE (% r15) (% rbx) *)
  0x4c; 0x0f; 0x45; 0xc1;  (* CMOVNE (% r8) (% rcx) *)
  0x4c; 0x0f; 0x45; 0xca;  (* CMOVNE (% r9) (% rdx) *)
  0x4c; 0x0f; 0x45; 0xd5;  (* CMOVNE (% r10) (% rbp) *)
  0x4d; 0x0f; 0x45; 0xdd;  (* CMOVNE (% r11) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% r15) *)
  0x4c; 0x89; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% r11) *)
  0x48; 0x8b; 0x8c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x89; 0xcd;        (* MOV (% r13) (% rcx) *)
  0x48; 0xc1; 0xe9; 0x3e;  (* SHR (% rcx) (Imm8 (word 62)) *)
  0x4c; 0x8b; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,176))) *)
  0x4d; 0x0f; 0xa4; 0xe5; 0x02;
                           (* SHLD (% r13) (% r12) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,168))) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x02;
                           (* SHLD (% r12) (% r11) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,160))) *)
  0x4d; 0x0f; 0xa4; 0xd3; 0x02;
                           (* SHLD (% r11) (% r10) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,152))) *)
  0x4d; 0x0f; 0xa4; 0xca; 0x02;
                           (* SHLD (% r10) (% r9) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,144))) *)
  0x4d; 0x0f; 0xa4; 0xc1; 0x02;
                           (* SHLD (% r9) (% r8) (Imm8 (word 2)) *)
  0x49; 0xc1; 0xe0; 0x02;  (* SHL (% r8) (Imm8 (word 2)) *)
  0x48; 0x83; 0xc1; 0x01;  (* ADD (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x2b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,288))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,296))) *)
  0x4c; 0x1b; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,304))) *)
  0x4c; 0x1b; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,312))) *)
  0x4c; 0x1b; 0xa4; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,320))) *)
  0x4c; 0x1b; 0xac; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x48; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% rdx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd1;        (* NOT (% rcx) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x21; 0xca;        (* AND (% rdx) (% rcx) *)
  0x48; 0x29; 0xd0;        (* SUB (% rax) (% rdx) *)
  0x48; 0x83; 0xe1; 0x01;  (* AND (% rcx) (Imm8 (word 1)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0x49; 0xb8; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Imm64 (word 4294967295)) *)
  0x4c; 0x2b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,192))) *)
  0x49; 0xb9; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r9) (Imm64 (word 18446744069414584320)) *)
  0x4c; 0x1b; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,200))) *)
  0x49; 0xc7; 0xc2; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r10) (Imm32 (word 4294967294)) *)
  0x4c; 0x1b; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,208))) *)
  0x49; 0xc7; 0xc3; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11) (Imm32 (word 4294967295)) *)
  0x4c; 0x1b; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,216))) *)
  0x49; 0xc7; 0xc4; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r12) (Imm32 (word 4294967295)) *)
  0x4c; 0x1b; 0xa4; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,224))) *)
  0x49; 0xc7; 0xc5; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r13) (Imm32 (word 4294967295)) *)
  0x4c; 0x1b; 0xac; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,232))) *)
  0x4d; 0x89; 0xee;        (* MOV (% r14) (% r13) *)
  0x49; 0xc1; 0xee; 0x3d;  (* SHR (% r14) (Imm8 (word 61)) *)
  0x4d; 0x0f; 0xa4; 0xe5; 0x03;
                           (* SHLD (% r13) (% r12) (Imm8 (word 3)) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x03;
                           (* SHLD (% r12) (% r11) (Imm8 (word 3)) *)
  0x4d; 0x0f; 0xa4; 0xd3; 0x03;
                           (* SHLD (% r11) (% r10) (Imm8 (word 3)) *)
  0x4d; 0x0f; 0xa4; 0xca; 0x03;
                           (* SHLD (% r10) (% r9) (Imm8 (word 3)) *)
  0x4d; 0x0f; 0xa4; 0xc1; 0x03;
                           (* SHLD (% r9) (% r8) (Imm8 (word 3)) *)
  0x49; 0xc1; 0xe0; 0x03;  (* SHL (% r8) (Imm8 (word 3)) *)
  0x49; 0x83; 0xc6; 0x01;  (* ADD (% r14) (Imm8 (word 1)) *)
  0xb9; 0x03; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 3)) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x11; 0xf2;        (* ADC (% r10) (% r14) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x48; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% rdx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd1;        (* NOT (% rcx) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x21; 0xca;        (* AND (% rdx) (% rcx) *)
  0x48; 0x29; 0xd0;        (* SUB (% rax) (% rdx) *)
  0x48; 0x83; 0xe1; 0x01;  (* AND (% rcx) (Imm8 (word 1)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x4c; 0x89; 0x47; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r8) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x4c; 0x89; 0x4f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r9) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x4c; 0x89; 0x57; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x67; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6f; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r13) *)
  0x48; 0x81; 0xc4; 0x58; 0x01; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 344)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let p384_montjdouble_alt_tmc = define_trimmed "p384_montjdouble_alt_tmc" p384_montjdouble_alt_mc;;

let P384_MONTJDOUBLE_ALT_EXEC = X86_MK_CORE_EXEC_RULE p384_montjdouble_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

let p384shortishredlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_384 - 1)
       ==> let q = n DIV 2 EXP 384 + 1 in
           q < 2 EXP 64 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

let FORALL_INT_CASES' = prove
 (`!P. (!x:int. P x) <=> (!n. P(&n)) /\ (!n. ~(n = 0) ==> P(-- &n))`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [FORALL_INT_CASES] THEN
  MESON_TAC[INT_NEG_EQ_0; INT_OF_NUM_EQ]);;

let p384shortintredlemma = prove
 (`!n. --(&p_384) <= n /\ n <= &5 * &p_384
       ==> let q = (&2 pow 384 + n) div &2 pow 384 in
           &0 <= q /\ q < &25 /\
           q < &2 pow 64 /\
           q * &p_384 <= n + &p_384 /\
           n < q * &p_384 + &p_384`,
  ONCE_REWRITE_TAC[INT_ARITH `&2 pow 384 + n:int = &1 * &2 pow 384 + n`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[FORALL_INT_CASES'; INT_DIV_LNEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; INT_OF_NUM_REM] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_LE_NEG2; INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `n < 2 EXP 384` ASSUME_TAC THENL
   [UNDISCH_TAC `n <= p_384` THEN REWRITE_TAC[p_384] THEN ARITH_TAC;
    ASM_SIMP_TAC[DIV_LT; MOD_LT]] THEN
  UNDISCH_TAC `n <= p_384` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[p_384] THEN INT_ARITH_TAC);;

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

let lvs =
 ["x_1",[`RSI`; `0`];
  "y_1",[`RSI`; `48`];
  "z_1",[`RSI`; `96`];
  "x_3",[`RDI`; `0`];
  "y_3",[`RDI`; `48`];
  "z_3",[`RDI`; `96`];
  "z2",[`RSP`; `0`];
  "y2",[`RSP`; `48`];
  "x2p",[`RSP`; `96`];
  "xy2",[`RSP`; `144`];
  "y4",[`RSP`; `192`];
  "t2",[`RSP`; `192`];
  "dx2",[`RSP`; `240`];
  "t1",[`RSP`; `240`];
  "d",[`RSP`; `288`];
  "x4p",[`RSP`; `288`]];;

let DESUM_RULE' = cache DESUM_RULE and DECARRY_RULE' = cache DECARRY_RULE;;

(* ------------------------------------------------------------------------- *)
(* Instances of montsqr.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTSQR_P384_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p384_montjdouble_alt_tmc) 284 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = a
    ==>
    nonoverlapping (word pc,0x2da1) (word_add (read p3 t) (word n3),48) /\
    nonoverlapping (word_add (read p1 t) (word n1),48)
                   (word_add (read p3 t) (word n3),48)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p384_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              a)
             (\s. read RIP s = pcout /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 6)) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [RIP; RDI; RAX; RBX; RBP; RCX; RDX;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P384_MONTJDOUBLE_ALT_EXEC (1--284)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Simulate the main squaring and 6-fold Montgomery reduction ***)

  MAP_EVERY (fun s ->
    X86_SINGLE_STEP_TAC P384_MONTJDOUBLE_ALT_EXEC s THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC s) THEN CLARIFY_TAC)
   (statenames "s" (1--259)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_NEG]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0]) THEN

  (*** Do the congruential reasoning on the chosen multipliers ***)

  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Derive the main property of the pre-reduced form, which we call t ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s252; sum_s253; sum_s254; sum_s255; sum_s256; sum_s257;
          word (bitval carry_s257)]` THEN

  SUBGOAL_THEN
   `t < 2 * p_384 /\ (2 EXP 384 * t == a EXP 2) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 384 * p
         ==> 2 EXP 384 * t < ab + 2 EXP 384 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
   [264;266;268;269;270;271] (260--284) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_384` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`384`; `if t < p_384 then &t:real else &t - &p_384`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN
   `~(val(word_add (word(bitval carry_s257))
                   (word(bitval carry_s271)):int64) = 0) <=>
    p_384 <= t`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
    ASM_CASES_TAC `carry_s257:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM NOT_LE] THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of montmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTMUL_P384_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p384_montjdouble_alt_tmc) 361 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = b
    ==>
    nonoverlapping (word pc,0x2da1) (word_add (read p3 t) (word n3),48)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p384_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              a /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              b)
             (\s. read RIP s = pcout /\
                  (a * b <= 2 EXP 384 * p_384
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s =
                       (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
            (MAYCHANGE [RIP; RAX; RBP; RBX; RCX; RDX;
                        R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P384_MONTJDOUBLE_ALT_EXEC (1--361)] THEN
  ENSURES_INIT_TAC "s1" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Simulate the main 6-fold multiply-and-Montgomery-reduce block ***)

  MAP_EVERY (fun s ->
    X86_SINGLE_STEP_TAC P384_MONTJDOUBLE_ALT_EXEC s THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC s) THEN CLARIFY_TAC)
   (statenames "s" (2--337)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_NEG]) THEN

  (*** Do the congruential reasoning on the chosen multipliers ***)

  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Derive the main property of the pre-reduced form, which we call t ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s330; sum_s331; sum_s332; sum_s333; sum_s334; sum_s336;
          sum_s337]` THEN
  SUBGOAL_THEN
   `t < 2 * p_384 /\ (2 EXP 384 * t == a * b) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 384 * p
         ==> 2 EXP 384 * t < ab + 2 EXP 384 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** To make bounds reasoning more transparent, recast top as a bit ***)

  MP_TAC(fst(EQ_IMP_RULE(SPEC `val(sum_s337:int64)` NUM_AS_BITVAL_ALT))) THEN
  REWRITE_TAC[VAL_EQ_BITVAL] THEN ANTS_TAC THENL
   [UNDISCH_TAC `t < 2 * p_384` THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `topc:bool` SUBST_ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
   [342;344;346;347;348;349] (338--362) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_384` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`384`; `if t < p_384 then &t:real else &t - &p_384`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN
   `~(val(word_add (word(bitval topc))
                   (word(bitval carry_s349)):int64) = 0) <=>
    p_384 <= t`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
    ASM_CASES_TAC `topc:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM NOT_LE] THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_P384_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p384_montjdouble_alt_tmc) 32 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    nonoverlapping (word pc,0x2da1) (word_add (read p3 t) (word n3),48)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p384_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
             (\s. read RIP s = pcout /\
                  (m < p_384 /\ n < p_384
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s) = (&m - &n) rem &p_384))
            (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R8; R9; R10; R11] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--12) (1--12) THEN

  SUBGOAL_THEN `carry_s12 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `384` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC [18;20;25;27;29;31] (13--32) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV(RAND_CONV BIGNUM_EXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s32" THEN

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
  EXISTS_TAC `(&2:real) pow 384` THEN

  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_384`; `n < p_384`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    ASM_CASES_TAC `&m:real < &n` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[p_384] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; STRIP_TAC] THEN

  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[WORD_AND_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_BITVAL_EQ_0; WORD_NEG_EQ_0] THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_384] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of weakadd                                                      *)
(* ------------------------------------------------------------------------- *)

let LOCAL_WEAKADD_P384_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p384_montjdouble_alt_tmc) 31 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    nonoverlapping (word pc,0x2da1) (word_add (read p3 t) (word n3),48)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p384_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
             (\s. read RIP s = pcout /\
                  (m + n < 2 EXP 384 + p_384
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s < 2 EXP 384 /\
                       (&(read(memory :> bytes(word_add (read p3 t) (word n3),
                               8 * 6)) s):int == &m + &n) (mod &p_384)))
            (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R8; R9; R10; R11; RBP] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--12) (1--12) THEN
  SUBGOAL_THEN `carry_s12 <=> 2 EXP 384 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC [20;22;24;26;28;30] (13--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[]
   `!x. (x < 2 EXP 384 /\ P x) /\ y = x ==> y < 2 EXP 384 /\ P y`) THEN
  EXISTS_TAC `if m + n < 2 EXP 384 then m + n else (m + n) - p_384` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `m + n < 2 EXP 384 + p_384` THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_CONG_REFL] THEN
    MATCH_MP_TAC(INTEGER_RULE `y - p:int = x ==> (x == y) (mod p)`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN MATCH_MP_TAC INT_OF_NUM_SUB THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_REDUCE_CONV `2 EXP 384`)]) THEN
  ABBREV_TAC `b <=> 2 EXP 384 <= m + n` THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCARD_STATE_TAC "s27" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; COND_SWAP] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    UNDISCH_TAC `m + n < 2 EXP 384 + p_384` THEN
    EXPAND_TAC "b" THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `&(if b then (m + n) - p_384 else m + n):real =
    if b then (&m + &n) - &p_384 else &m + &n`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
    UNDISCH_TAC `b:bool` THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_384] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_P384_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p384_montjdouble_alt_tmc) 40 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    nonoverlapping (word pc,0x2da1) (word_add (read p3 t) (word n3),48)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p384_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
         (\s. read RIP s = pcout /\
              (m < p_384 /\ n < p_384
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 6)) s = (m + n) MOD p_384))
            (MAYCHANGE [RIP; RAX; RBX; RBP; RCX; RDX; R8; R9; R10; R11] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--23) (1--23) THEN
  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC [29;31;33;35;37;39] (24--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  SUBGOAL_THEN
   `sum_s23:int64 = word_neg(word(bitval(m + n < p_384))) /\
    (carry_s23 <=> ~(m + n < p_384))`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ONCE_REWRITE_TAC[TAUT `(p <=> ~q) <=> (~p <=> q)`] THEN
    MATCH_MP_TAC FLAG_AND_MASK_FROM_CARRY_LT THEN
    EXISTS_TAC `384` THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`m < p_384`; `n < p_384`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
      REWRITE_TAC[p_384; REAL_BITVAL_NOT; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL; REAL_BITVAL_NOT]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    ALL_TAC] THEN

  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s40" THEN
  ASM_SIMP_TAC[MOD_CASES; ARITH_RULE `m < p /\ n < p ==> m + n < 2 * p`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_384`; `n < p_384`] THEN
    REWRITE_TAC[p_384; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN

  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[WORD_BITVAL_EQ_0; WORD_NEG_EQ_0] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_CLAUSES; REAL_BITVAL_NOT] THEN
  CONV_TAC WORD_REDUCE_CONV THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_ARITH
     `&2 pow 64 * (&1 - &0) + &0:real = b + &18446744073709551615 + c <=>
      c = &1 - b`] THEN
    ASM_CASES_TAC `&(bitval carry_s22):real = &1 - &(bitval carry_s12)` THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[p_384] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance (12,9) of cmsub (the only one used in this code).                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUBC9_P384_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p384_montjdouble_alt_tmc) 111 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    nonoverlapping (word pc,0x2da1) (word_add (read p3 t) (word n3),48)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p384_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
         (\s. read RIP s = pcout /\
              (n <= p_384
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                     8 * 6)) s) = (&12 * &m - &9 * &n) rem &p_384))
            (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R8; R9;
                        R10; R11; R12; R13; R14] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P384_MONTJDOUBLE_ALT_EXEC (1--111)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&12 * &m - &9 * &n) rem &p_384 =
    (&12 * &m + &9 * (&p_384 - &n)) rem &p_384`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--12) (1--12) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
           [sum_s2; sum_s4; sum_s6; sum_s8; sum_s10; sum_s12]` THEN
  SUBGOAL_THEN `p_384 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `12 * m + 9 * n'` p384shortishredlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN REWRITE_TAC[p_384] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
   `x DIV 2 EXP 384 + 1 = (2 EXP 384 + x) DIV 2 EXP 384`]) THEN

  (*** Main sum of products computation +1 ***)

  X86_GEN_ACCSTEPS_TAC
    (fun _ -> RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
                `word_sub x (word_neg y):int64 = word_add x y`]))
    P384_MONTJDOUBLE_ALT_EXEC (13--77) (13--77) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s46; sum_s52; sum_s58; sum_s64; sum_s70; sum_s76; sum_s77]` THEN
  SUBGOAL_THEN `2 EXP 384 + 12 * m + 9 * n'= ca` MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN
       SUBST_ALL_TAC th THEN ASSUME_TAC th THEN DISCH_TAC) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s77` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s77:int64` o concl))) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 384 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
    [79;80;81;82; 87;88;89;90;91;92; 100;102;104;106;108;110]
    (78--111) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_NEG; VAL_WORD_BITVAL]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `384`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `12 * m + 9 * n' < val(q:int64) * p_384 <=> ~carry_s92`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `a < b <=> 2 EXP 384 + a < b + 2 EXP 384`] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `384` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH
     `&(12 * m + 9 * n'):real =
      (&2 pow 384 + &(12 * m + 9 * n')) - &2 pow 384`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s92:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub41_p384 (actually there is only one).                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB41_P384_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p384_montjdouble_alt_tmc) 56 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    nonoverlapping (word pc,0x2da1) (word_add (read p3 t) (word n3),48)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p384_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
         (\s. read RIP s = pcout /\
              (n <= p_384
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                          8 * 6)) s) = (&4 * &m - &n) rem &p_384))
         (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R8; R9;
                     R10; R11; R12; R13; R14] ,,
          MAYCHANGE
            [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
           MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n <= p_384 assumption ***)

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P384_MONTJDOUBLE_ALT_EXEC (1--56)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Instantiate the (integer) quotient approximation lemma ***)

  MP_TAC(SPEC `&4 * &m - &n:int` p384shortintredlemma) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_384` THEN REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      INT_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[p_384] THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Main shift-subtract block ***)

  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (15--22) (1--22) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s16; sum_s17; sum_s18; sum_s19; sum_s20; sum_s21; sum_s22]` THEN
  SUBGOAL_THEN `&2 pow 384 + &4 * &m - &n:int = &ca`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [REWRITE_TAC[int_eq; int_add_th; int_sub_th; int_pow_th;
                int_mul_th; int_of_num_th] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`448`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["m"; "n"; "ca"] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&4 * &m:real =
      &(bignum_of_wordlist
         [word_shl m_0 2;
          word_subword ((word_join:int64->int64->int128) m_1 m_0) (62,64);
          word_subword ((word_join:int64->int64->int128) m_2 m_1) (62,64);
          word_subword ((word_join:int64->int64->int128) m_3 m_2) (62,64);
          word_subword ((word_join:int64->int64->int128) m_4 m_3) (62,64);
          word_subword ((word_join:int64->int64->int128) m_5 m_4) (62,64);
          word_ushr m_5 62])`
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
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s22` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s22:int64` o concl))) THEN
  SUBGOAL_THEN `&ca div &2 pow 384 = &(val(q:int64))` SUBST_ALL_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV] THEN
    EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_GEN_ACCSTEPS_TAC
    (fun _ -> RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
                `word_sub x (word_neg y):int64 = word_add x y`]))
    P384_MONTJDOUBLE_ALT_EXEC
     [24;25;26;27; 32;33;34;35;36;37; 45;47;49;51;53;55] (23--56) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_NEG; VAL_WORD_BITVAL]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ_BALANCED_MOD THEN
  MAP_EVERY EXISTS_TAC [`&(val(q:int64)):int`; `384`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; p_384] THEN BOUNDER_TAC[]; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `&4 * m - n:int = (&2 pow 384 + &4 * m - n) - &2 pow 384`] THEN
  ASM_REWRITE_TAC[] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN
    `(&ca - &2 pow 384):int < &(val(q:int64)) * &p_384 <=> ~carry_s37`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_LT_SUB_RADD; INT_OF_NUM_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `384` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_RULE
     `(a:int == b + c - p) (mod p) <=> (a == b + c) (mod p)`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "ca" THEN REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s37:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub38 (there is only one).                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB38_P384_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p384_montjdouble_alt_tmc) 90 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    nonoverlapping (word pc,0x2da1) (word_add (read p3 t) (word n3),48)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p384_montjdouble_alt_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
             (\s. read RIP s = pcout /\
                  (n <= p_384
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s) = (&3 * &m - &8 * &n) rem &p_384))
            (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R8; R9;
                        R10; R11; R12; R13; R14] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P384_MONTJDOUBLE_ALT_EXEC (1--90)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&3 * &m - &8 * &n) rem &p_384 =
    (&3 * &m + &8 * (&p_384 - &n)) rem &p_384`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--12) (1--12) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
           [sum_s2; sum_s4; sum_s6; sum_s8; sum_s10; sum_s12]` THEN
  SUBGOAL_THEN `p_384 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `3 * m + 8 * n'` p384shortishredlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN REWRITE_TAC[p_384] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
   `x DIV 2 EXP 384 + 1 = (2 EXP 384 + x) DIV 2 EXP 384`]) THEN

  (*** Main sum of products computation +1 ***)

  X86_GEN_ACCSTEPS_TAC
    (fun _ -> RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
                `word_sub x (word_neg y):int64 = word_add x y`]))
    P384_MONTJDOUBLE_ALT_EXEC
     [21;24;25;26; 29;30;31;32; 35;36;37;38;
      41;42;43;44; 47;48;49;50; 53;54;55;56] (13--56) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s25; sum_s31; sum_s37; sum_s43; sum_s49; sum_s55; sum_s56]` THEN
  SUBGOAL_THEN `2 EXP 384 + 3 * m + 8 * n'= ca` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`448`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["m"; "n'"; "ca"] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&8 * &n':real =
      &(bignum_of_wordlist
      [word_shl sum_s2 3;
       word_subword ((word_join:int64->int64->int128) sum_s4 sum_s2) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s6 sum_s4) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s8 sum_s6) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s10 sum_s8) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s12 sum_s10) (61,64);
       word_ushr sum_s12 61])`
    SUBST1_TAC THENL
     [EXPAND_TAC "n'" THEN
      REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC WORD_BLAST;
      MAP_EVERY EXPAND_TAC ["m"; "ca"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN
      SUBST_ALL_TAC th THEN ASSUME_TAC th THEN DISCH_TAC) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s56` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s56:int64` o concl))) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 384 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
    [58; 59; 60; 61; 66; 67; 68; 69; 70; 71; 79; 81; 83; 85; 87; 89]
    (57--90) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_NEG; VAL_WORD_BITVAL]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `384`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `3 * m + 8 * n' < val(q:int64) * p_384 <=> ~carry_s71`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `a < b <=> 2 EXP 384 + a < b + 2 EXP 384`] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `384` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH
     `&(3 * m + 8 * n'):real =
      (&2 pow 384 + &(3 * m + 8 * n')) - &2 pow 384`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s71:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let unilemma0 = prove
 (`x = a MOD p_384 ==> x < p_384 /\ &x = &a rem &p_384`,
  REWRITE_TAC[INT_OF_NUM_REM; p_384] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_384 ==> x < p_384 /\ &x = a rem &p_384`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_384] THEN INT_ARITH_TAC);;

let lemont = prove
 (`(&i * x * y) rem &p_384 = (&i * x rem &p_384 * y rem &p_384) rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let demont = prove
 (`(&(NUMERAL n) * &x) rem &p_384 = (&(NUMERAL n) * &x rem &p_384) rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let pumont = prove
 (`(&(inverse_mod p_384 (2 EXP 384)) *
    (&2 pow 384 * x) rem &p_384 * (&2 pow 384 * y) rem &p_384) rem &p_384 =
   (&2 pow 384 * x * y) rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * t:int == &1) (mod p)
    ==> (i * (t * x) * (t * y) == t * x * y) (mod p)`) THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2; p_384] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let dismont = prove
 (`((&2 pow 384 * x) rem &p_384 + (&2 pow 384 * y) rem &p_384) rem &p_384 =
   (&2 pow 384 * (x + y)) rem &p_384 /\
   ((&2 pow 384 * x) rem &p_384 - (&2 pow 384 * y) rem &p_384) rem &p_384 =
   (&2 pow 384 * (x - y)) rem &p_384 /\
  (&(NUMERAL n) * (&2 pow 384 * x) rem &p_384) rem &p_384 =
   (&2 pow 384 * (&(NUMERAL n) * x)) rem &p_384`,
  REPEAT CONJ_TAC THEN CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let unmont = prove
 (`(&(inverse_mod p_384 (2 EXP 384)) * (&2 pow 384 * x) rem &p_384) rem &p_384 =
   x rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * e:int == &1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent; INVERSE_MOD_LMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_384] THEN CONV_TAC NUM_REDUCE_CONV);;

let unreplemma = prove
 (`!x. x < p_384
         ==> x =
             (2 EXP 384 * (inverse_mod p_384 (2 EXP 384) * x) MOD p_384) MOD
             p_384`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  ASM_REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(i * e == 1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_384] THEN CONV_TAC NUM_REDUCE_CONV);;

let weierstrass_of_jacobian_p384_double = prove
 (`!P1 P2 x1 y1 z1 x3 y3 z3.
        jacobian_double_unexceptional nistp384
         (x1 rem &p_384,y1 rem &p_384,z1 rem &p_384) =
        (x3 rem &p_384,y3 rem &p_384,z3 rem &p_384)
       ==> weierstrass_of_jacobian (integer_mod_ring p_384)
                (x1 rem &p_384,y1 rem &p_384,z1 rem &p_384) = P1
            ==> weierstrass_of_jacobian (integer_mod_ring p_384)
                  (x3 rem &p_384,y3 rem &p_384,z3 rem &p_384) =
                group_mul p384_group P1 P1`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[nistp384; P384_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P384] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_384; b_384] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_p384 = new_definition
 `represents_p384 P (x,y,z) <=>
        x < p_384 /\ y < p_384 /\ z < p_384 /\
        weierstrass_of_jacobian (integer_mod_ring p_384)
         (tripled (montgomery_decode (384,p_384)) (x,y,z)) = P`;;

let P384_MONTJDOUBLE_ALT_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        ALL (nonoverlapping (stackpointer,344))
            [(word pc,0x2da1); (p1,144); (p3,144)] /\
        nonoverlapping (p3,144) (word pc,0x2da1)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST p384_montjdouble_alt_tmc) /\
                  read RIP s = word(pc + 0x11) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read RIP s = word (pc + 0x2d8f) /\
                  !P. represents_p384 P t1
                      ==> represents_p384 (group_mul p384_group P P)
                            (bignum_triple_from_memory(p3,6) s))
          (MAYCHANGE [RIP; RDI; RSI; RAX; RDX; RCX; R8; R9; R10; R11;
                      RBX; RBP; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,144);
                      memory :> bytes(stackpointer,344)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_MONTSQR_P384_TAC 1 ["z2";"z_1"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["y2";"y_1"] THEN
  LOCAL_WEAKADD_P384_TAC 0 ["t1";"x_1";"z2"] THEN
  LOCAL_SUB_P384_TAC 0 ["t2";"x_1";"z2"] THEN
  LOCAL_MONTMUL_P384_TAC 0 ["x2p";"t1";"t2"] THEN
  LOCAL_ADD_P384_TAC 0 ["t1";"y_1";"z_1"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["x4p";"x2p"] THEN
  LOCAL_MONTMUL_P384_TAC 0 ["xy2";"x_1";"y2"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["t2";"t1"] THEN
  LOCAL_CMSUBC9_P384_TAC 0 ["d";"xy2";"x4p"] THEN
  LOCAL_SUB_P384_TAC 0 ["t1";"t2";"z2"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["y4";"y2"] THEN
  LOCAL_SUB_P384_TAC 1 ["z_3";"t1";"y2"] THEN
  LOCAL_MONTMUL_P384_TAC 0 ["dx2";"d";"x2p"] THEN
  LOCAL_CMSUB41_P384_TAC 0 ["x_3";"xy2";"d"] THEN
  LOCAL_CMSUB38_P384_TAC 0 ["y_3";"dx2";"y4"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s18" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  X_GEN_TAC `P:(int#int)option` THEN
  REWRITE_TAC[represents_p384; tripled] THEN
  REWRITE_TAC[montgomery_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_384] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_384]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (MP_TAC o C SPEC unreplemma) [`z1:num`; `y1:num`; `x1:num`] THEN
  MAP_EVERY (fun t -> ABBREV_TAC t THEN POP_ASSUM(K ALL_TAC))
   [`x1d = inverse_mod p_384 (2 EXP 384) * x1`;
    `y1d = inverse_mod p_384 (2 EXP 384) * y1`;
    `z1d = inverse_mod p_384 (2 EXP 384) * z1`] THEN
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
  MATCH_MP_TAC weierstrass_of_jacobian_p384_double THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_double_unexceptional; nistp384;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let P384_MONTJDOUBLE_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 392),392))
            [(word pc,LENGTH p384_montjdouble_alt_tmc); (p1,144)] /\
        ALL (nonoverlapping (p3,144))
            [(word pc,LENGTH p384_montjdouble_alt_tmc); (word_sub stackpointer (word 392),400)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p384_montjdouble_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p384 P t1
                      ==> represents_p384 (group_mul p384_group P P)
                            (bignum_triple_from_memory(p3,6) s))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,144);
                      memory :> bytes(word_sub stackpointer (word 392),392)])`,
  X86_PROMOTE_RETURN_STACK_TAC p384_montjdouble_alt_tmc P384_MONTJDOUBLE_ALT_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 392);;

let P384_MONTJDOUBLE_ALT_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 392),392))
            [(word pc,LENGTH p384_montjdouble_alt_mc); (p1,144)] /\
        ALL (nonoverlapping (p3,144))
            [(word pc,LENGTH p384_montjdouble_alt_mc); (word_sub stackpointer (word 392),400)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p384_montjdouble_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p384 P t1
                      ==> represents_p384 (group_mul p384_group P P)
                            (bignum_triple_from_memory(p3,6) s))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,144);
                      memory :> bytes(word_sub stackpointer (word 392),392)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE P384_MONTJDOUBLE_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let p384_montjdouble_alt_windows_mc = define_from_elf "p384_montjdouble_alt_windows_mc"
      "x86/p384/p384_montjdouble_alt.obj";;

let p384_montjdouble_alt_windows_tmc = define_trimmed "p384_montjdouble_alt_windows_tmc" p384_montjdouble_alt_windows_mc;;

let P384_MONTJDOUBLE_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 408),408))
            [(word pc,LENGTH p384_montjdouble_alt_windows_tmc); (p1,144)] /\
        ALL (nonoverlapping (p3,144))
            [(word pc,LENGTH p384_montjdouble_alt_windows_tmc); (word_sub stackpointer (word 408),416)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p384_montjdouble_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p384 P t1
                      ==> represents_p384 (group_mul p384_group P P)
                            (bignum_triple_from_memory(p3,6) s))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,144);
                      memory :> bytes(word_sub stackpointer (word 408),408)])`,
  WINDOWS_X86_WRAP_STACK_TAC
    p384_montjdouble_alt_windows_tmc p384_montjdouble_alt_tmc
    P384_MONTJDOUBLE_ALT_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 392);;

let P384_MONTJDOUBLE_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 408),408))
            [(word pc,LENGTH p384_montjdouble_alt_windows_mc); (p1,144)] /\
        ALL (nonoverlapping (p3,144))
            [(word pc,LENGTH p384_montjdouble_alt_windows_mc); (word_sub stackpointer (word 408),416)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p384_montjdouble_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p384 P t1
                      ==> represents_p384 (group_mul p384_group P P)
                            (bignum_triple_from_memory(p3,6) s))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,144);
                      memory :> bytes(word_sub stackpointer (word 408),408)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE P384_MONTJDOUBLE_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

