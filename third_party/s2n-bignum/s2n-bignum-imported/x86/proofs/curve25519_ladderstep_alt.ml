(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery ladder step in (X,Z)-projective coordinates for curve25519.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/ecencoding.ml";;

needs "EC/curve25519.ml";;
needs "EC/formulary_xzprojective.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "x86/curve25519/curve25519_ladderstep_alt.o";;
 ****)

let curve25519_ladderstep_alt_mc = define_assert_from_elf
  "curve25519_ladderstep_alt_mc" "x86/curve25519/curve25519_ladderstep_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xa0; 0x01; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 416)) *)
  0x48; 0x89; 0xbc; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,384))) (% rdi) *)
  0x48; 0x89; 0xb4; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,392))) (% rsi) *)
  0x48; 0x89; 0x8c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,408))) (% rcx) *)
  0x4c; 0x8b; 0x42; 0x40;  (* MOV (% r8) (Memop Quadword (%% (rdx,64))) *)
  0x4c; 0x2b; 0x42; 0x60;  (* SUB (% r8) (Memop Quadword (%% (rdx,96))) *)
  0x4c; 0x8b; 0x4a; 0x48;  (* MOV (% r9) (Memop Quadword (%% (rdx,72))) *)
  0x4c; 0x1b; 0x4a; 0x68;  (* SBB (% r9) (Memop Quadword (%% (rdx,104))) *)
  0x4c; 0x8b; 0x52; 0x50;  (* MOV (% r10) (Memop Quadword (%% (rdx,80))) *)
  0x4c; 0x1b; 0x52; 0x70;  (* SBB (% r10) (Memop Quadword (%% (rdx,112))) *)
  0x48; 0x8b; 0x42; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rdx,88))) *)
  0x48; 0x1b; 0x42; 0x78;  (* SBB (% rax) (Memop Quadword (%% (rdx,120))) *)
  0x49; 0x83; 0xe8; 0x13;  (* SUB (% r8) (Imm8 (word 19)) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x0f; 0xba; 0xf8; 0x3f;
                           (* BTC (% rax) (Imm8 (word 63)) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x48; 0x8b; 0x02;        (* MOV (% rax) (Memop Quadword (%% (rdx,0))) *)
  0x48; 0x03; 0x42; 0x20;  (* ADD (% rax) (Memop Quadword (%% (rdx,32))) *)
  0x48; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rax) *)
  0x48; 0x8b; 0x42; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rdx,8))) *)
  0x48; 0x13; 0x42; 0x28;  (* ADC (% rax) (Memop Quadword (%% (rdx,40))) *)
  0x48; 0x89; 0x44; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rax) *)
  0x48; 0x8b; 0x42; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rdx,16))) *)
  0x48; 0x13; 0x42; 0x30;  (* ADC (% rax) (Memop Quadword (%% (rdx,48))) *)
  0x48; 0x89; 0x44; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rax) *)
  0x48; 0x8b; 0x42; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rdx,24))) *)
  0x48; 0x13; 0x42; 0x38;  (* ADC (% rax) (Memop Quadword (%% (rdx,56))) *)
  0x48; 0x89; 0x44; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rax) *)
  0x4c; 0x8b; 0x02;        (* MOV (% r8) (Memop Quadword (%% (rdx,0))) *)
  0x4c; 0x2b; 0x42; 0x20;  (* SUB (% r8) (Memop Quadword (%% (rdx,32))) *)
  0x4c; 0x8b; 0x4a; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rdx,8))) *)
  0x4c; 0x1b; 0x4a; 0x28;  (* SBB (% r9) (Memop Quadword (%% (rdx,40))) *)
  0x4c; 0x8b; 0x52; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rdx,16))) *)
  0x4c; 0x1b; 0x52; 0x30;  (* SBB (% r10) (Memop Quadword (%% (rdx,48))) *)
  0x48; 0x8b; 0x42; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rdx,24))) *)
  0x48; 0x1b; 0x42; 0x38;  (* SBB (% rax) (Memop Quadword (%% (rdx,56))) *)
  0x49; 0x83; 0xe8; 0x13;  (* SUB (% r8) (Imm8 (word 19)) *)
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r10) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x0f; 0xba; 0xf8; 0x3f;
                           (* BTC (% rax) (Imm8 (word 63)) *)
  0x48; 0x89; 0x44; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rax) *)
  0x48; 0x8b; 0x42; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rdx,64))) *)
  0x48; 0x03; 0x42; 0x60;  (* ADD (% rax) (Memop Quadword (%% (rdx,96))) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x48; 0x8b; 0x42; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rdx,72))) *)
  0x48; 0x13; 0x42; 0x68;  (* ADC (% rax) (Memop Quadword (%% (rdx,104))) *)
  0x48; 0x89; 0x44; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rax) *)
  0x48; 0x8b; 0x42; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rdx,80))) *)
  0x48; 0x13; 0x42; 0x70;  (* ADC (% rax) (Memop Quadword (%% (rdx,112))) *)
  0x48; 0x89; 0x44; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rax) *)
  0x48; 0x8b; 0x42; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rdx,88))) *)
  0x48; 0x13; 0x42; 0x78;  (* ADC (% rax) (Memop Quadword (%% (rdx,120))) *)
  0x48; 0x89; 0x44; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbe; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,408))) *)
  0x48; 0x85; 0xc0;        (* TEST (% rax) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x60;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x68;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x70;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x78;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% rax) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x20;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x28;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x30;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x38;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% rax) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbe; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbe; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% r11) *)
  0x4c; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x2b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,192))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,200))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x1b; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,208))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x1b; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,216))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x1b; 0xa4; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,224))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x49; 0x81; 0xe8; 0x38; 0x4a; 0x00; 0x00;
                           (* SUB (% r8) (Imm32 (word 19000)) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x49; 0x19; 0xdc;        (* SBB (% r12) (% rbx) *)
  0x49; 0x81; 0xc4; 0xf4; 0x01; 0x00; 0x00;
                           (* ADD (% r12) (Imm32 (word 500)) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4c; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbe; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% r11) *)
  0x4c; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x03; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,192))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x13; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,200))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x13; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,208))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x13; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,216))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x13; 0xa4; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,224))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4c; 0x89; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbe; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r11) *)
  0x4c; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,256))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,288))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,264))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,296))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,272))) *)
  0x4c; 0x1b; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0x1b; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% r10) *)
  0x48; 0x89; 0x84; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,344))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbe; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x8d; 0x44; 0x24; 0x01;
                           (* LEA (% rax) (%% (r12,1)) *)
  0xbe; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xba; 0xeb; 0x3f;
                           (* BTS (% r11) (Imm8 (word 63)) *)
  0x48; 0x0f; 0xaf; 0xc6;  (* IMUL (% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x48; 0xc7; 0xc6; 0x42; 0xdb; 0x01; 0x00;
                           (* MOV (% rsi) (Imm32 (word 121666)) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,336))) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,344))) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x48; 0x11; 0xf2;        (* ADC (% rdx) (% rsi) *)
  0x4c; 0x03; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,288))) *)
  0x4c; 0x13; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,296))) *)
  0x4c; 0x13; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,304))) *)
  0x4c; 0x13; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0x11; 0xf2;        (* ADC (% rdx) (% rsi) *)
  0x4c; 0x0f; 0xa4; 0xda; 0x01;
                           (* SHLD (% rdx) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xbb; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 19)) *)
  0x48; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% rbx) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xf1;        (* ADC (% r9) (% rsi) *)
  0x49; 0x11; 0xf2;        (* ADC (% r10) (% rsi) *)
  0x49; 0x11; 0xf3;        (* ADC (% r11) (% rsi) *)
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,288))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,296))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,288))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,304))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,296))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,288))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,312))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,304))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,296))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,288))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,312))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,304))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,296))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,312))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,304))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,312))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbe; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x8d; 0x44; 0x24; 0x01;
                           (* LEA (% rax) (%% (r12,1)) *)
  0xbe; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xba; 0xeb; 0x3f;
                           (* BTS (% r11) (Imm8 (word 63)) *)
  0x48; 0x0f; 0xaf; 0xc6;  (* IMUL (% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r11) *)
  0x48; 0x8b; 0xac; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,392))) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x65; 0x00;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,0))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x65; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,8))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x65; 0x00;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,0))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x65; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,16))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x65; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,8))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x65; 0x00;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,0))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x65; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,24))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x65; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,16))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x65; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,8))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x65; 0x00;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,0))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x65; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,24))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x65; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,16))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x65; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,8))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x65; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,24))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x65; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,16))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x65; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,24))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbe; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x8d; 0x44; 0x24; 0x01;
                           (* LEA (% rax) (%% (r12,1)) *)
  0xbe; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xba; 0xeb; 0x3f;
                           (* BTS (% r11) (Imm8 (word 63)) *)
  0x48; 0x0f; 0xaf; 0xc6;  (* IMUL (% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0x4c; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,336))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,336))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,344))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,336))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,344))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,336))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,344))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,344))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbe; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x8d; 0x44; 0x24; 0x01;
                           (* LEA (% rax) (%% (r12,1)) *)
  0xbe; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xba; 0xeb; 0x3f;
                           (* BTS (% r11) (Imm8 (word 63)) *)
  0x48; 0x0f; 0xaf; 0xc6;  (* IMUL (% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,408))) *)
  0x48; 0x8b; 0xac; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,384))) *)
  0x48; 0x85; 0xc0;        (* TEST (% rax) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x0c; 0x24;  (* MOV (% rcx) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% rdx) *)
  0x48; 0x89; 0x45; 0x00;  (* MOV (Memop Quadword (%% (rbp,0))) (% rax) *)
  0x48; 0x89; 0x4d; 0x40;  (* MOV (Memop Quadword (%% (rbp,64))) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% rdx) *)
  0x48; 0x89; 0x45; 0x08;  (* MOV (Memop Quadword (%% (rbp,8))) (% rax) *)
  0x48; 0x89; 0x4d; 0x48;  (* MOV (Memop Quadword (%% (rbp,72))) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x10;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% rdx) *)
  0x48; 0x89; 0x45; 0x10;  (* MOV (Memop Quadword (%% (rbp,16))) (% rax) *)
  0x48; 0x89; 0x4d; 0x50;  (* MOV (Memop Quadword (%% (rbp,80))) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x18;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% rdx) *)
  0x48; 0x89; 0x45; 0x18;  (* MOV (Memop Quadword (%% (rbp,24))) (% rax) *)
  0x48; 0x89; 0x4d; 0x58;  (* MOV (Memop Quadword (%% (rbp,88))) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x20;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% rdx) *)
  0x48; 0x89; 0x45; 0x20;  (* MOV (Memop Quadword (%% (rbp,32))) (% rax) *)
  0x48; 0x89; 0x4d; 0x60;  (* MOV (Memop Quadword (%% (rbp,96))) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x28;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% rdx) *)
  0x48; 0x89; 0x45; 0x28;  (* MOV (Memop Quadword (%% (rbp,40))) (% rax) *)
  0x48; 0x89; 0x4d; 0x68;  (* MOV (Memop Quadword (%% (rbp,104))) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x30;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% rdx) *)
  0x48; 0x89; 0x45; 0x30;  (* MOV (Memop Quadword (%% (rbp,48))) (% rax) *)
  0x48; 0x89; 0x4d; 0x70;  (* MOV (Memop Quadword (%% (rbp,112))) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x38;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% rdx) *)
  0x48; 0x89; 0x45; 0x38;  (* MOV (Memop Quadword (%% (rbp,56))) (% rax) *)
  0x48; 0x89; 0x4d; 0x78;  (* MOV (Memop Quadword (%% (rbp,120))) (% rcx) *)
  0x48; 0x81; 0xc4; 0xa0; 0x01; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 416)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let curve25519_ladderstep_alt_tmc = define_trimmed "curve25519_ladderstep_alt_tmc" curve25519_ladderstep_alt_mc;;

let CURVE25519_LADDERSTEP_ALT_EXEC =
  X86_MK_CORE_EXEC_RULE curve25519_ladderstep_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Abbreviations used to state the specification.                            *)
(* ------------------------------------------------------------------------- *)

let p_25519 = define `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let curve25519 = define
 `curve25519 = (integer_mod_ring p_25519,&A_25519:int,&1:int)`;;

let curve25519_encode = new_definition
  `curve25519_encode = modular_encode(256,p_25519)`;;

let montgomery_ladderstep = new_definition
 `montgomery_ladderstep cparams b Q Qm Qn =
        if b then (montgomery_xzdiffadd cparams Q Qm Qn,
                   montgomery_xzdouble cparams Qn)
        else (montgomery_xzdouble cparams Qm,
              montgomery_xzdiffadd cparams Q Qm Qn)`;;

(* ------------------------------------------------------------------------- *)
(* Common lemmas and tactics for the component proofs.                       *)
(* ------------------------------------------------------------------------- *)

let p25519redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_25519 - 1)
       ==> let q = n DIV 2 EXP 255 + 1 in
           q < 2 EXP 64 /\
           q * p_25519 <= n + p_25519 /\
           n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let p25519weakredlemma = prove
 (`!n. n <= 2 EXP 62 * 2 EXP 256
       ==> let q = n DIV 2 EXP 255 in
           q < 2 EXP 64 /\
           q * p_25519 <= n /\
           n < q * p_25519 + 2 * p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let lvs =
 ["x",[`RBP`;`0`];
  "xn",[`RDX`;`0`];
  "zn",[`RDX`;`32`];
  "xm",[`RDX`;`64`];
  "zm",[`RDX`;`96`];
  "sm",[`RSP`;`0`];
  "sumx",[`RSP`;`0`];
  "sn",[`RSP`;`32`];
  "sumz",[`RSP`;`32`];
  "dpro",[`RSP`;`32`];
  "dm",[`RSP`;`64`];
  "dubx",[`RSP`;`64`];
  "dn",[`RSP`;`96`];
  "dubz",[`RSP`;`96`];
  "e",[`RSP`;`96`];
  "dmsn",[`RSP`;`128`];
  "dnsm",[`RSP`;`192`];
  "spro",[`RSP`;`192`];
  "s",[`RSP`;`256`];
  "d",[`RSP`;`288`];
  "p",[`RSP`;`320`];
  "res0",[`RBP`;`0`];
  "res1",[`RBP`;`32`];
  "res2",[`RBP`;`64`];
  "res3",[`RBP`;`96`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_p25519.                                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P25519_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 129 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x15aa) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDX s = read RDX t /\
                read RBP s = read RBP t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (m * n) MOD p_25519)
         (MAYCHANGE [RIP; RSI; RAX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s1" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiplication block, similar to bignum_mul_4_8_alt ***)

  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (2--84) (2--84) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s14; sum_s30; sum_s51]`;
    `h = bignum_of_wordlist[sum_s67; sum_s78; sum_s83; sum_s84]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  MAP_EVERY (fun n ->
    X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC("s"^string_of_int n)))
   (85--109) THEN
  ABBREV_TAC
   `ca =
    bignum_of_wordlist[sum_s88; sum_s94; sum_s100; sum_s107; sum_s109]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (110--114) THEN
  ABBREV_TAC `t = bignum_of_wordlist
   [sum_s88; sum_s94; sum_s100;
    word_or sum_s107 (word 9223372036854775808)]` THEN
  SUBGOAL_THEN `&ca = &t + &2 pow 255 * (&(ca DIV 2 EXP 255) - &1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `c = t + e * (d - &1):real <=> c + e = t + e * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
    `c + d = t + 2 EXP 255 * c DIV 2 EXP 255 <=> c MOD 2 EXP 255 + d = t`] THEN
    MAP_EVERY EXPAND_TAC ["ca"; "t"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `2 EXP 256 * n = 2 EXP 255 * 2 * n`] THEN
    REWRITE_TAC[MOD_MULT_MOD; ARITH_RULE
     `2 EXP 255 = 2 EXP 192 * 2 EXP 63`] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(3,1)] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `bignum_of_wordlist [sum_s88; sum_s94; sum_s100] < 2 EXP 192`
    (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE
     `(e * x + a) + e * y:num = a + e * z <=> e * (x + y) = e * z`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or (word_and x (word_not m)) m`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and (word_and x (word_not m)) m = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s109 sum_s107) (63,64)` THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(hw:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    EXPAND_TAC "hw" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[CONG; ADD_SYM; MULT_SYM] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  REABBREV_TAC `qm = read RAX s114` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * (&(val(hw:int64)) + &1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_MUL; DIMINDEX_64] THEN
    REWRITE_TAC[ REAL_OF_NUM_CLAUSES] THEN CONV_TAC MOD_DOWN_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[MULT_SYM] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(hw:int64) + 1 <= 78` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC
   [115;116;117;118;122;123;124;125] (115--130) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(hw:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (val(hw:int64) + 1) * p_25519 <=> ~carry_s118`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
    REWRITE_TAC[REAL_BITVAL_NOT] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s118:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instances of sqr_p25519 (actually there is only one).                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_P25519_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 118 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1.
      !n. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
        nonoverlapping (word pc,0x15aa) (word_add (read p3 t) (word n3),8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                  read RIP s = pcin /\
                  read RSP s = read RSP t /\
                  read RDX s = read RDX t /\
                  read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = n)
             (\s. read RIP s = pcout /\
                  read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s = (n EXP 2) MOD p_25519)
          (MAYCHANGE [RIP; RSI; RAX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8_alt ***)

  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (1--72) (1--72) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s2; sum_s12; sum_s26; sum_s43]`;
    `h = bignum_of_wordlist[sum_s57; sum_s66; sum_s71; sum_s72]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  MAP_EVERY (fun n ->
    X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC("s"^string_of_int n)))
   (73--97) THEN
  ABBREV_TAC
   `ca =
    bignum_of_wordlist[sum_s76; sum_s82; sum_s88; sum_s95; sum_s97]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (98--102) THEN
  ABBREV_TAC `t = bignum_of_wordlist
   [sum_s76; sum_s82; sum_s88;
    word_or sum_s95 (word 9223372036854775808)]` THEN
  SUBGOAL_THEN `&ca = &t + &2 pow 255 * (&(ca DIV 2 EXP 255) - &1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `c = t + e * (d - &1):real <=> c + e = t + e * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
    `c + d = t + 2 EXP 255 * c DIV 2 EXP 255 <=> c MOD 2 EXP 255 + d = t`] THEN
    MAP_EVERY EXPAND_TAC ["ca"; "t"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `2 EXP 256 * n = 2 EXP 255 * 2 * n`] THEN
    REWRITE_TAC[MOD_MULT_MOD; ARITH_RULE
     `2 EXP 255 = 2 EXP 192 * 2 EXP 63`] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(3,1)] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `bignum_of_wordlist [sum_s76; sum_s82; sum_s88] < 2 EXP 192`
    (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE
     `(e * x + a) + e * y:num = a + e * z <=> e * (x + y) = e * z`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or (word_and x (word_not m)) m`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and (word_and x (word_not m)) m = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s97 sum_s95) (63,64)` THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(hw:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    EXPAND_TAC "hw" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[CONG; ADD_SYM; MULT_SYM] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  REABBREV_TAC `qm = read RAX s102` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * (&(val(hw:int64)) + &1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_MUL; DIMINDEX_64] THEN
    REWRITE_TAC[ REAL_OF_NUM_CLAUSES] THEN CONV_TAC MOD_DOWN_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[MULT_SYM] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(hw:int64) + 1 <= 78` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC
   [103;104;105;106;110;111;112;113] (103--118) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(hw:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (val(hw:int64) + 1) * p_25519 <=> ~carry_s106`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
    REWRITE_TAC[REAL_BITVAL_NOT] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s106:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instance of mul_5                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_5_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 113 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x15aa) (word_add (read p3 t) (word n3),8 * 5)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDX s = read RDX t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 5)) s
                < 39 * 2 EXP 256 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 5)) s ==
                 m * n) (mod p_25519))
        (MAYCHANGE [RIP; RSI; RAX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 5)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s1" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiplication block, similar to bignum_mul_4_8_alt ***)

  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (2--84) (2--84) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s14; sum_s30; sum_s51]`;
    `h = bignum_of_wordlist[sum_s67; sum_s78; sum_s83; sum_s84]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY (fun n ->
    X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC("s"^string_of_int n)))
   (85--109) THEN
  X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (110--114) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  MATCH_MP_TAC(MESON[] `y < n /\ x = y ==> x < n /\ x MOD p = y MOD p`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sqr_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_4_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 109 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1.
      !n.
      read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x15aa) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDX s = read RDX t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                < 2 * p_25519 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                 n EXP 2)
                (mod p_25519))
          (MAYCHANGE [RIP; RSI; RAX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8_alt ***)

  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (1--72) (1--72) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s2; sum_s12; sum_s26; sum_s43]`;
    `h = bignum_of_wordlist[sum_s57; sum_s66; sum_s71; sum_s72]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  MAP_EVERY (fun n ->
    X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC("s"^string_of_int n)))
   (73--97) THEN
  ABBREV_TAC
   `ca =
    bignum_of_wordlist[sum_s76; sum_s82; sum_s88; sum_s95; sum_s97]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (98--101) THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s97 sum_s95) (63,64)` THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(hw:int64)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    EXPAND_TAC "hw" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[CONG; ADD_SYM; MULT_SYM] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `qm:int64 = word_mul (word 19:int64) hw` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * &(val(hw:int64))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD_MUL; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(hw:int64) + 1 <= 78` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (102--105) (102--109) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(hw:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `x - y:int < z <=> x < y + z`] THEN
    REWRITE_TAC[INT_ARITH `h * p + &2 * p:int = (h + &1) * p + p`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES; LE_0] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `h * p <= ca <=> (h + 1) * p <= ca + p`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - z) (mod p) <=> (x + z == y) (mod p)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[REAL_CONGRUENCE; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  EXPAND_TAC "ca" THEN
  REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  UNDISCH_THEN `ca DIV 2 EXP 255 = val(hw:int64)` (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "ca" THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; ARITH_RULE
   `(l + 2 EXP 64 * h) DIV 2 EXP 63 = l DIV 2 EXP 63 + 2 * h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
  REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_4_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 12 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x15aa) (word_add (read p3 t) (word n3),8 * 4) /\
      nonoverlapping (pp,128) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDX s = read RDX t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                (m < p_25519 /\ n < p_25519
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                     m + n))
        (MAYCHANGE [RIP; RAX] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC [2;5;8;11] (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add5_4 (actually there is only one).                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD5_4_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 23 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) t = n
      ==>
      nonoverlapping (word pc,0x15aa) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDX s = read RDX t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) s = n)
           (\s. read RIP s = pcout /\
                (m + n < 2 EXP 58 * 2 EXP 256
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                     < 2 * p_25519 /\
                     (bignum_from_memory
                       (word_add (read p3 t) (word n3),4) s ==
                      m + n) (mod p_25519)))
        (MAYCHANGE [RIP; RBX; RDX; R8; R9; R10; R11; R12] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `m + n < 2 EXP 58 * 2 EXP 256` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC CURVE25519_LADDERSTEP_ALT_EXEC (1--23)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC [2;4;6;8;10] (1--10) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s2; sum_s4; sum_s6; sum_s8; sum_s10]` THEN
  SUBGOAL_THEN `m + n = ca` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN MATCH_MP_TAC CONG_IMP_EQ THEN
    EXISTS_TAC `2 EXP 320` THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `m + n < 2 EXP 58 * 2 EXP 256` THEN ARITH_TAC;
      BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `ca:num` p25519weakredlemma) THEN ANTS_TAC THENL
   [UNDISCH_TAC `ca < 2 EXP 58 * 2 EXP 256` THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (11--15) THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s10 sum_s8) (63,64)` THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(hw:int64)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `ca < 2 EXP 58 * 2 EXP 256
      ==> ca DIV 2 EXP 192 DIV 2 EXP 63 < 2 EXP 59`)) THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    EXPAND_TAC "hw" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[CONG; ADD_SYM; MULT_SYM] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `qm:int64 = word_mul (word 19:int64) hw` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * &(val(hw:int64))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD_MUL; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    MATCH_MP_TAC MOD_LT THEN MAP_EVERY UNDISCH_TAC
     [`val(hw:int64) * p_25519 <= ca`;
      `ca < 2 EXP 58 * 2 EXP 256`] THEN
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (16--19) (16--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(hw:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `x - y:int < z <=> x < y + z`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES; LE_0] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `h * p <= ca <=> (h + 1) * p <= ca + p`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - z) (mod p) <=> (x + z == y) (mod p)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[REAL_CONGRUENCE; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  EXPAND_TAC "ca" THEN
  REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  UNDISCH_THEN `ca DIV 2 EXP 255 = val(hw:int64)` (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "ca" THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; ARITH_RULE
   `(l + 2 EXP 64 * h) DIV 2 EXP 63 = l DIV 2 EXP 63 + 2 * h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
  REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_4_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 17 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x15aa) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDX s = read RDX t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                (m < p_25519 /\ n < p_25519
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                     < 2 * p_25519 /\
                     (&(bignum_from_memory
                         (word_add (read p3 t) (word n3),4) s):int ==
                      &m - &n) (mod (&p_25519))))
        (MAYCHANGE [RIP; RAX; R8; R9; R10] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC
   [2;4;6;8;9;11;13;15] (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x' < &e /\ &x = x'
             ==> x < e /\ (&x:int == a) (mod p)`) THEN
  EXISTS_TAC `(&m - &n) + &p_25519:int` THEN REPEAT CONJ_TAC THENL
   [CONV_TAC INTEGER_RULE;
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x:int < e /\ &0 <= y /\ y < e ==> abs(x - y) < e`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    REWRITE_TAC[INTEGER_RULE
     `(x:int == m - n + c) (mod e) <=> (n + x == m + c) (mod e)`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
  REWRITE_TAC[REAL_VAL_WORD_XOR] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63`); VAL_WORD_AND_POW2] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub_twice4 (actually there is only one).                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_TWICE4_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 19 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x15aa) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDX s = read RDX t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                (m < 2 * p_25519 /\ n < 2 * p_25519
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                     < 2 * p_25519 /\
                     (&(bignum_from_memory
                         (word_add (read p3 t) (word n3),4) s):int ==
                      &m - &n) (mod (&p_25519))))
        (MAYCHANGE [RIP; RAX; RBX; RCX; R8; R9; R10] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (1--10) (1--10) THEN
  SUBGOAL_THEN `carry_s10 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (12--15) (11--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x' < &e /\ &x = x'
             ==> x < e /\ (&x:int == a) (mod p)`) THEN
  EXISTS_TAC `if m < n then &m - &n + &2 * &p_25519:int else &m - &n` THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC INTEGER_RULE;
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NOT_LT]) THEN
  ABBREV_TAC `bb <=> m:num < n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub5_4 (actually there is only one).                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB5_4_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 29 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) t = n
      ==>
      nonoverlapping (word pc,0x15aa) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDX s = read RDX t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) s = n)
           (\s. read RIP s = pcout /\
                (m < 39 * 2 EXP 256 /\ n < 39 * 2 EXP 256
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                     < 2 * p_25519 /\
                     (&(bignum_from_memory
                       (word_add (read p3 t) (word n3),4) s):int ==
                      &m - &n) (mod (&p_25519))))
        (MAYCHANGE [RIP; RBX; RDX; R8; R9; R10; R11; R12] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `m < 39 * 2 EXP 256 /\ n < 39 * 2 EXP 256` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC CURVE25519_LADDERSTEP_ALT_EXEC (1--29)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC
   [2;4;6;8;10;12;13;14;15;16;17] (1--17) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s12; sum_s13; sum_s14; sum_s15; sum_s17]` THEN
  SUBGOAL_THEN `&ca:int = &m - &n + &1000 * &p_25519` ASSUME_TAC THENL
   [EXPAND_TAC "ca" THEN MATCH_MP_TAC INT_CONG_IMP_EQ THEN
    EXISTS_TAC `(&2:int) pow 320` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `&0 <= x /\ x:int < e /\ &0 <= y /\ y < e ==> abs(x - y) < e`) THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
      REWRITE_TAC[INTEGER_RULE
       `(x:int == m - n + c) (mod e) <=> (n + x == m + c) (mod e)`] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  REWRITE_TAC[GSYM INT_REM_EQ] THEN
  SUBGOAL_THEN `(&m - &n) rem &p_25519 = &ca rem &p_25519` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[INT_REM_MUL_ADD];
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    REWRITE_TAC[GSYM CONG]] THEN
  SUBGOAL_THEN `ca < 600 * 2 EXP 256` ASSUME_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    ASM_REWRITE_TAC[p_25519; GSYM INT_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `&ca:int = &m - &n + &1000 * &p_25519` (K ALL_TAC) THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `ca:num` p25519weakredlemma) THEN ANTS_TAC THENL
   [UNDISCH_TAC `ca < 600 * 2 EXP 256` THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (18--21) THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s17 sum_s15) (63,64)` THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(hw:int64)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `ca < 600 * 2 EXP 256
      ==> ca DIV 2 EXP 192 DIV 2 EXP 63 < 2 EXP 59`)) THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    EXPAND_TAC "hw" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[CONG; ADD_SYM; MULT_SYM] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `qm:int64 = word_mul (word 19:int64) hw` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * &(val(hw:int64))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD_MUL; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    MATCH_MP_TAC MOD_LT THEN MAP_EVERY UNDISCH_TAC
     [`val(hw:int64) * p_25519 <= ca`;
      `ca < 600 * 2 EXP 256`] THEN
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (22--25) (22--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(hw:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `x - y:int < z <=> x < y + z`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES; LE_0] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `h * p <= ca <=> (h + 1) * p <= ca + p`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - z) (mod p) <=> (x + z == y) (mod p)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[REAL_CONGRUENCE; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  EXPAND_TAC "ca" THEN
  REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  UNDISCH_THEN `ca DIV 2 EXP 255 = val(hw:int64)` (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "ca" THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; ARITH_RULE
   `(l + 2 EXP 64 * h) DIV 2 EXP 63 = l DIV 2 EXP 63 + 2 * h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
  REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of cmadd_4 (actually there is only one, specific constant).     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMADD_4_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 37 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
     ==>
      nonoverlapping (word pc,0x15aa) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDX s = read RDX t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s <
                2 * p_25519 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                 121666 * m + n) (mod p_25519))
        (MAYCHANGE [RIP; RSI; RAX; RBX; RDX; R8; R9; R10; R11] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (1--25) (1--25) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s21; sum_s22; sum_s23; sum_s24; sum_s25]` THEN
  SUBGOAL_THEN `121666 * m + n < 2 EXP 17 * 2 EXP 256` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `121666 * m + n = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `ca:num` p25519weakredlemma) THEN ANTS_TAC THENL
   [UNDISCH_TAC `ca < 2 EXP 17 * 2 EXP 256` THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (26--29) THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s25 sum_s24) (63,64)` THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(hw:int64)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `ca < 2 EXP 17 * 2 EXP 256
      ==> ca DIV 2 EXP 192 DIV 2 EXP 63 < 2 EXP 59`)) THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    EXPAND_TAC "hw" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[CONG; ADD_SYM; MULT_SYM] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `qm:int64 = word_mul hw (word 19:int64)` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * &(val(hw:int64))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD_MUL; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[MULT_SYM] THEN
    MATCH_MP_TAC MOD_LT THEN MAP_EVERY UNDISCH_TAC
     [`val(hw:int64) * p_25519 <= ca`;
      `ca < 2 EXP 17 * 2 EXP 256`] THEN
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (30--33) (30--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(hw:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `x - y:int < z <=> x < y + z`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES; LE_0] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `h * p <= ca <=> (h + 1) * p <= ca + p`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - z) (mod p) <=> (x + z == y) (mod p)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[REAL_CONGRUENCE; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  EXPAND_TAC "ca" THEN
  REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  UNDISCH_THEN `ca DIV 2 EXP 255 = val(hw:int64)` (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "ca" THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; ARITH_RULE
   `(l + 2 EXP 64 * h) DIV 2 EXP 63 = l DIV 2 EXP 63 + 2 * h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
  REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of mux_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUX_4_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 16 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
     !b. read ZF t = b
     ==>
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
     ==>
      nonoverlapping (word pc,0x15aa) (word_add (read p3 t) (word n3),8 * 4) /\
      nonoverlapping (pp,128) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDX s = read RDX t /\
                read ZF s = b /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (if b then n else m))
        (MAYCHANGE [RIP; RAX; RCX] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Instances of muxpair_4.                                                   *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUXPAIR_4_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE curve25519_ladderstep_alt_tmc) 28 lvs
   `!(t:x86state) pcin pcout p3 n3 p4 n4 p1 n1 p2 n2.
     !b. read ZF t = b
     ==>
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x15aa) (rr:int64,8 * 16) /\
      nonoverlapping (stackpointer,416) (rr,8 * 16)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RBP s = read RBP t /\
                read RDX s = read RDX t /\
                read ZF s = b /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (if b then m else n) /\
                read(memory :> bytes(word_add (read p4 t) (word n4),8 * 4)) s =
                (if b then n else m))
        (MAYCHANGE [RIP; RAX; RCX; RDX] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4);
                    memory :> bytes(word_add (read p4 t) (word n4),8 * 4)])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_STEPS_TAC CURVE25519_LADDERSTEP_ALT_EXEC (1--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINOP_CONV(LAND_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let curve25519_params = define
 `curve25519_params = (integer_mod_ring p_25519,&A_25519:int,&1:int)`;;

let nintlemma = prove
 (`&(num_of_int(x rem &p_25519)) = x rem &p_25519`,
  MATCH_MP_TAC INT_OF_NUM_OF_INT THEN MATCH_MP_TAC INT_REM_POS THEN
  REWRITE_TAC[INT_OF_NUM_EQ; p_25519] THEN CONV_TAC NUM_REDUCE_CONV);;

let lemma = prove
 (`X = num_of_int(x rem &p_25519) ==> X < p_25519 /\ &X = x rem &p_25519`,
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; nintlemma; INT_LT_REM_EQ] THEN
  REWRITE_TAC[INT_OF_NUM_LT; p_25519] THEN CONV_TAC NUM_REDUCE_CONV);;

let CURVE25519_LADDERSTEP_ALT_CORRECT = time prove
 (`!rr point P pp Pm Pn b pc stackpointer.
    ALLPAIRS nonoverlapping
     [(rr,128); (stackpointer,416)]
     [(word pc,0x15aa); (point,64); (pp,128)] /\
    nonoverlapping (rr,128) (stackpointer,416)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST curve25519_ladderstep_alt_tmc) /\
              read RIP s = word(pc + 0x11) /\
              read RSP s = stackpointer /\
              C_ARGUMENTS [rr; point; pp; b] s /\
              bignum_pair_from_memory (point,4) s = P /\
              bignum_pairpair_from_memory (pp,4) s = (Pm,Pn))
         (\s. read RIP s = word (pc + 0x1598) /\
              !Q Qm Qn.
               P = paired curve25519_encode Q /\ SND Q = &1 /\
               (Pm,Pn) = pairpaired curve25519_encode (Qm,Qn)
               ==> bignum_pairpair_from_memory(rr,4) s =
                   pairpaired curve25519_encode
                    (montgomery_ladderstep curve25519 (~(b = word 0)) Q Qm Qn))
      (MAYCHANGE [RIP; RDI; RSI; RAX; RBX; RCX; RDX; RBP;
                  R8; R9; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [memory :> bytes(rr,128);
                  memory :> bytes(stackpointer,416)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`rr:int64`; `point:int64`; `X:num`; `Z:num`;
    `pp:int64`; `Xn:num`; `Zn:num`; `Xm:num`; `Zm:num`;
    `b:int64`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ;
     bignum_pair_from_memory; bignum_pairpair_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_SUB_4_TAC 3 ["dm"; "xm"; "zm"] THEN
  LOCAL_ADD_4_TAC 0 ["sn"; "xn"; "zn"] THEN
  LOCAL_SUB_4_TAC 0 ["dn"; "xn"; "zn"] THEN
  LOCAL_ADD_4_TAC 0 ["sm"; "xm"; "zm"] THEN

  LOCAL_MUL_5_TAC 0 ["dmsn"; "dm"; "sn"] THEN

  LOCAL_MUX_4_TAC 2 ["d"; "dm"; "dn"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0]) THEN
  LOCAL_MUX_4_TAC 0 ["s"; "sm"; "sn"] THEN

  LOCAL_MUL_5_TAC 0 ["dnsm"; "sm"; "dn"] THEN
  LOCAL_SQR_4_TAC 0 ["d"; "d"] THEN

  LOCAL_SUB5_4_TAC 0 ["dpro"; "dmsn"; "dnsm"] THEN
  LOCAL_SQR_4_TAC 0 ["s"; "s"] THEN
  LOCAL_ADD5_4_TAC 0 ["spro"; "dmsn"; "dnsm"] THEN
  LOCAL_SQR_4_TAC 0 ["dpro"; "dpro"] THEN

  LOCAL_SUB_TWICE4_TAC 0 ["p"; "s"; "d"] THEN
  LOCAL_SQR_P25519_TAC 0 ["sumx"; "spro"] THEN
  LOCAL_CMADD_4_TAC 0 ["e"; "p"; "d"] THEN

  LOCAL_MUL_P25519_TAC 0 ["dubx"; "s"; "d"] THEN
  LOCAL_MUL_P25519_TAC 1 ["sumz"; "dpro"; "x"] THEN
  LOCAL_MUL_P25519_TAC 0 ["dubz"; "p"; "e"] THEN

  LOCAL_MUXPAIR_4_TAC 3 ["res0"; "res2"; "dubx"; "sumx"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0]) THEN
  ABBREV_TAC
   `ares0 = read (memory :> bytes(rr,8 * 4)) s29` THEN
  LOCAL_MUXPAIR_4_TAC 0 ["res1"; "res3"; "dubz"; "sumz"] THEN
  ABBREV_TAC
   `ares1 = read (memory :> bytes(word_add rr (word 32),8 * 4)) s30` THEN

  (*** Clean up the final statement ***)

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[pairpaired; paired; PAIR_EQ] THEN
  REWRITE_TAC[curve25519_encode; modular_encode] THEN
  MAP_EVERY X_GEN_TAC
   [`x:int`; `z:int`; `xm:int`; `zm:int`; `xn:int`; `zn:int`] THEN
  ASM_CASES_TAC `z:int = &1` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
    (STRIP_ASSUME_TAC o MATCH_MP lemma)) THEN
  DISCARD_STATE_TAC "s29" THEN
  DISCARD_MATCHING_ASSUMPTIONS
   [`aligned a b`; `nonoverlapping_modulo a b c`] THEN

  (*** Eliminate range side-conditions ***)

  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN

  (*** Case split over b = 0 ***)

  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[pairpaired; paired; montgomery_ladderstep; modular_encode;
   montgomery_xzdouble; montgomery_xzdiffadd; curve25519; PAIR_EQ] THEN
  STRIP_TAC THEN REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; modular_encode] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[PAIR_EQ; GSYM INT_OF_NUM_EQ; nintlemma] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  ONCE_REWRITE_TAC[GSYM INT_POW_REM; GSYM INT_MUL_REM] THEN

  (*** Systematize equational assumptions ***)

  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN

  (*** Do the algebra ***)

  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[A_25519] THEN INT_ARITH_TAC);;

let CURVE25519_LADDERSTEP_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!rr point P pp Pm Pn b pc stackpointer returnaddress.
    ALLPAIRS nonoverlapping
     [(rr,128); (word_sub stackpointer (word 464),464)]
     [(word pc,LENGTH curve25519_ladderstep_alt_tmc); (point,64); (pp,128)] /\
    nonoverlapping (rr,128) (word_sub stackpointer (word 464),472)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) curve25519_ladderstep_alt_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [rr; point; pp; b] s /\
              bignum_pair_from_memory (point,4) s = P /\
              bignum_pairpair_from_memory (pp,4) s = (Pm,Pn))
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              !Q Qm Qn.
               P = paired curve25519_encode Q /\ SND Q = &1 /\
               (Pm,Pn) = pairpaired curve25519_encode (Qm,Qn)
               ==> bignum_pairpair_from_memory(rr,4) s =
                   pairpaired curve25519_encode
                    (montgomery_ladderstep curve25519 (~(b = word 0)) Q Qm Qn))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(rr,128);
                      memory :> bytes(word_sub stackpointer (word 464),464)])`,
  X86_PROMOTE_RETURN_STACK_TAC
    curve25519_ladderstep_alt_tmc CURVE25519_LADDERSTEP_ALT_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 464);;

let CURVE25519_LADDERSTEP_ALT_SUBROUTINE_CORRECT = time prove
 (`!rr point P pp Pm Pn b pc stackpointer returnaddress.
    ALLPAIRS nonoverlapping
     [(rr,128); (word_sub stackpointer (word 464),464)]
     [(word pc,LENGTH curve25519_ladderstep_alt_mc); (point,64); (pp,128)] /\
    nonoverlapping (rr,128) (word_sub stackpointer (word 464),472)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) curve25519_ladderstep_alt_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [rr; point; pp; b] s /\
              bignum_pair_from_memory (point,4) s = P /\
              bignum_pairpair_from_memory (pp,4) s = (Pm,Pn))
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              !Q Qm Qn.
               P = paired curve25519_encode Q /\ SND Q = &1 /\
               (Pm,Pn) = pairpaired curve25519_encode (Qm,Qn)
               ==> bignum_pairpair_from_memory(rr,4) s =
                   pairpaired curve25519_encode
                    (montgomery_ladderstep curve25519 (~(b = word 0)) Q Qm Qn))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(rr,128);
                      memory :> bytes(word_sub stackpointer (word 464),464)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE CURVE25519_LADDERSTEP_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let curve25519_ladderstep_alt_windows_mc = define_from_elf
   "curve25519_ladderstep_alt_windows_mc"
"x86/curve25519/curve25519_ladderstep_alt.obj";;

let curve25519_ladderstep_alt_windows_tmc = define_trimmed "curve25519_ladderstep_alt_windows_tmc" curve25519_ladderstep_alt_windows_mc;;

let CURVE25519_LADDERSTEP_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!rr point P pp Pm Pn b pc stackpointer returnaddress.
    ALLPAIRS nonoverlapping
     [(rr,128); (word_sub stackpointer (word 480),480)]
     [(word pc,LENGTH curve25519_ladderstep_alt_windows_tmc); (point,64); (pp,128)] /\
    nonoverlapping (rr,128) (word_sub stackpointer (word 480),488)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) curve25519_ladderstep_alt_windows_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [rr; point; pp; b] s /\
              bignum_pair_from_memory (point,4) s = P /\
              bignum_pairpair_from_memory (pp,4) s = (Pm,Pn))
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              !Q Qm Qn.
               P = paired curve25519_encode Q /\ SND Q = &1 /\
               (Pm,Pn) = pairpaired curve25519_encode (Qm,Qn)
               ==> bignum_pairpair_from_memory(rr,4) s =
                   pairpaired curve25519_encode
                    (montgomery_ladderstep curve25519 (~(b = word 0)) Q Qm Qn))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(rr,128);
                      memory :> bytes(word_sub stackpointer (word 480),480)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   curve25519_ladderstep_alt_windows_tmc curve25519_ladderstep_alt_tmc
   CURVE25519_LADDERSTEP_ALT_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 464);;

let CURVE25519_LADDERSTEP_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!rr point P pp Pm Pn b pc stackpointer returnaddress.
    ALLPAIRS nonoverlapping
     [(rr,128); (word_sub stackpointer (word 480),480)]
     [(word pc,LENGTH curve25519_ladderstep_alt_windows_mc); (point,64); (pp,128)] /\
    nonoverlapping (rr,128) (word_sub stackpointer (word 480),488)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) curve25519_ladderstep_alt_windows_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [rr; point; pp; b] s /\
              bignum_pair_from_memory (point,4) s = P /\
              bignum_pairpair_from_memory (pp,4) s = (Pm,Pn))
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              !Q Qm Qn.
               P = paired curve25519_encode Q /\ SND Q = &1 /\
               (Pm,Pn) = pairpaired curve25519_encode (Qm,Qn)
               ==> bignum_pairpair_from_memory(rr,4) s =
                   pairpaired curve25519_encode
                    (montgomery_ladderstep curve25519 (~(b = word 0)) Q Qm Qn))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(rr,128);
                      memory :> bytes(word_sub stackpointer (word 480),480)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE CURVE25519_LADDERSTEP_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

