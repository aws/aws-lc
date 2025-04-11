(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Square roots modulo p_25519, the field characteristic for curve25519.     *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "x86/proofs/base.ml";;

(* ------------------------------------------------------------------------- *)
(* The code.                                                                 *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "x86/curve25519/bignum_sqrt_p25519.o";;
 ****)

let bignum_sqrt_p25519_mc = define_assert_from_elf "bignum_sqrt_p25519_mc" "x86/curve25519/bignum_sqrt_p25519.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xb0; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 176)) *)
  0x48; 0x89; 0xbc; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rdi) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x49; 0x0f; 0xba; 0xe9; 0x3f;
                           (* BTS (% r9) (Imm8 (word 63)) *)
  0x4c; 0x11; 0xd0;        (* ADC (% rax) (% r10) *)
  0x48; 0x6b; 0xc0; 0x13;  (* IMUL3 (% rax) (% rax,Imm8 (word 19)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4d; 0x11; 0xd0;        (* ADC (% r8) (% r10) *)
  0x4d; 0x11; 0xd1;        (* ADC (% r9) (% r10) *)
  0xb8; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 19)) *)
  0x49; 0x0f; 0x42; 0xc2;  (* CMOVB (% rax) (% r10) *)
  0x48; 0x29; 0xc2;        (* SUB (% rdx) (% rax) *)
  0x4c; 0x19; 0xd1;        (* SBB (% rcx) (% r10) *)
  0x4d; 0x19; 0xd0;        (* SBB (% r8) (% r10) *)
  0x4d; 0x19; 0xd1;        (* SBB (% r9) (% r10) *)
  0x49; 0x0f; 0xba; 0xf1; 0x3f;
                           (* BTR (% r9) (Imm8 (word 63)) *)
  0x48; 0x89; 0x14; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rdx) *)
  0x48; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r9) *)
  0x48; 0x8d; 0x7c; 0x24; 0x60;
                           (* LEA (% rdi) (%% (rsp,96)) *)
  0x48; 0xc7; 0xc6; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 1)) *)
  0x48; 0x8d; 0x14; 0x24;  (* LEA (% rdx) (%% (rsp,0)) *)
  0xe8; 0x07; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1287)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x60;
                           (* LEA (% rdi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x74; 0x24; 0x60;
                           (* LEA (% rsi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x14; 0x24;  (* LEA (% rdx) (%% (rsp,0)) *)
  0xe8; 0x45; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 837)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 2)) *)
  0x48; 0x8d; 0x54; 0x24; 0x60;
                           (* LEA (% rdx) (%% (rsp,96)) *)
  0xe8; 0xde; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1246)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x60;
                           (* LEA (% rdi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x54; 0x24; 0x60;
                           (* LEA (% rdx) (%% (rsp,96)) *)
  0xe8; 0x1b; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 795)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 1)) *)
  0x48; 0x8d; 0x54; 0x24; 0x60;
                           (* LEA (% rdx) (%% (rsp,96)) *)
  0xe8; 0xb4; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1204)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x14; 0x24;  (* LEA (% rdx) (%% (rsp,0)) *)
  0xe8; 0xf2; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 754)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x05; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 5)) *)
  0x48; 0x8d; 0x54; 0x24; 0x20;
                           (* LEA (% rdx) (%% (rsp,32)) *)
  0xe8; 0x8b; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1163)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x60;
                           (* LEA (% rdi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x54; 0x24; 0x20;
                           (* LEA (% rdx) (%% (rsp,32)) *)
  0xe8; 0xc8; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 712)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x0a; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 10)) *)
  0x48; 0x8d; 0x54; 0x24; 0x60;
                           (* LEA (% rdx) (%% (rsp,96)) *)
  0xe8; 0x61; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1121)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x60;
                           (* LEA (% rdi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x54; 0x24; 0x60;
                           (* LEA (% rdx) (%% (rsp,96)) *)
  0xe8; 0x9e; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 670)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x05; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 5)) *)
  0x48; 0x8d; 0x54; 0x24; 0x60;
                           (* LEA (% rdx) (%% (rsp,96)) *)
  0xe8; 0x37; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1079)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x54; 0x24; 0x20;
                           (* LEA (% rdx) (%% (rsp,32)) *)
  0xe8; 0x74; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 628)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x19; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 25)) *)
  0x48; 0x8d; 0x54; 0x24; 0x20;
                           (* LEA (% rdx) (%% (rsp,32)) *)
  0xe8; 0x0d; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1037)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x60;
                           (* LEA (% rdi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x54; 0x24; 0x20;
                           (* LEA (% rdx) (%% (rsp,32)) *)
  0xe8; 0x4a; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 586)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x32; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 50)) *)
  0x48; 0x8d; 0x54; 0x24; 0x60;
                           (* LEA (% rdx) (%% (rsp,96)) *)
  0xe8; 0xe3; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 995)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x60;
                           (* LEA (% rdi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x54; 0x24; 0x60;
                           (* LEA (% rdx) (%% (rsp,96)) *)
  0xe8; 0x20; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 544)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x19; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 25)) *)
  0x48; 0x8d; 0x54; 0x24; 0x60;
                           (* LEA (% rdx) (%% (rsp,96)) *)
  0xe8; 0xb9; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 953)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x54; 0x24; 0x20;
                           (* LEA (% rdx) (%% (rsp,32)) *)
  0xe8; 0xf6; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 502)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x7d; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 125)) *)
  0x48; 0x8d; 0x54; 0x24; 0x20;
                           (* LEA (% rdx) (%% (rsp,32)) *)
  0xe8; 0x8f; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 911)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x54; 0x24; 0x20;
                           (* LEA (% rdx) (%% (rsp,32)) *)
  0xe8; 0xcc; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 460)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 1)) *)
  0x48; 0x8d; 0x54; 0x24; 0x20;
                           (* LEA (% rdx) (%% (rsp,32)) *)
  0xe8; 0x65; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 869)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x60;
                           (* LEA (% rdi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x14; 0x24;  (* LEA (% rdx) (%% (rsp,0)) *)
  0xe8; 0xa3; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 419)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 1)) *)
  0x48; 0x8d; 0x54; 0x24; 0x60;
                           (* LEA (% rdx) (%% (rsp,96)) *)
  0xe8; 0x3c; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 828)) *)
  0x48; 0xb8; 0xb0; 0xa0; 0x0e; 0x4a; 0x27; 0x1b; 0xee; 0xc4;
                           (* MOV (% rax) (Imm64 (word 14190309331451158704)) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x48; 0xb8; 0x78; 0xe4; 0x2f; 0xad; 0x06; 0x18; 0x43; 0x2f;
                           (* MOV (% rax) (Imm64 (word 3405592160176694392)) *)
  0x48; 0x89; 0x44; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rax) *)
  0x48; 0xb8; 0xa7; 0xd7; 0xfb; 0x3d; 0x99; 0x00; 0x4d; 0x2b;
                           (* MOV (% rax) (Imm64 (word 3120150775007532967)) *)
  0x48; 0x89; 0x44; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rax) *)
  0x48; 0xb8; 0x0b; 0xdf; 0xc1; 0x4f; 0x80; 0x24; 0x83; 0x2b;
                           (* MOV (% rax) (Imm64 (word 3135389899092516619)) *)
  0x48; 0x89; 0x44; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rax) *)
  0x48; 0x8d; 0x7c; 0x24; 0x60;
                           (* LEA (% rdi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x54; 0x24; 0x60;
                           (* LEA (% rdx) (%% (rsp,96)) *)
  0xe8; 0x3d; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 317)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 1)) *)
  0x48; 0x8d; 0x54; 0x24; 0x40;
                           (* LEA (% rdx) (%% (rsp,64)) *)
  0xe8; 0xd6; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 726)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x33; 0x44; 0x24; 0x20;
                           (* XOR (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x8b; 0x5c; 0x24; 0x08;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x33; 0x5c; 0x24; 0x28;
                           (* XOR (% rbx) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x09; 0xd8;        (* OR (% rax) (% rbx) *)
  0x48; 0x8b; 0x4c; 0x24; 0x10;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x33; 0x4c; 0x24; 0x30;
                           (* XOR (% rcx) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x8b; 0x54; 0x24; 0x18;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x33; 0x54; 0x24; 0x38;
                           (* XOR (% rdx) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x09; 0xd1;        (* OR (% rcx) (% rdx) *)
  0x48; 0x09; 0xc8;        (* OR (% rax) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x5c; 0x24; 0x60;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x0f; 0x45; 0xc3;  (* CMOVNE (% rax) (% rbx) *)
  0x48; 0x8b; 0x5c; 0x24; 0x48;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x68;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0x0f; 0x45; 0xd9;  (* CMOVNE (% rbx) (% rcx) *)
  0x48; 0x8b; 0x4c; 0x24; 0x50;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0x8b; 0x54; 0x24; 0x70;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% rdx) *)
  0x48; 0x8b; 0x6c; 0x24; 0x58;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x8b; 0x54; 0x24; 0x78;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x0f; 0x45; 0xea;  (* CMOVNE (% rbp) (% rdx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x4c; 0x8d; 0x42; 0xed;  (* LEA (% r8) (%% (rdx,18446744073709551597)) *)
  0x4c; 0x8d; 0x5a; 0xff;  (* LEA (% r11) (%% (rdx,18446744073709551615)) *)
  0x4d; 0x89; 0xd9;        (* MOV (% r9) (% r11) *)
  0x4d; 0x89; 0xda;        (* MOV (% r10) (% r11) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xeb;        (* SBB (% r11) (% rbp) *)
  0x48; 0x8b; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xa9; 0x01; 0x00; 0x00; 0x00;
                           (* TEST (% rax) (Imm32 (word 1)) *)
  0x49; 0x0f; 0x45; 0xc0;  (* CMOVNE (% rax) (% r8) *)
  0x48; 0x89; 0x02;        (* MOV (Memop Quadword (%% (rdx,0))) (% rax) *)
  0x49; 0x0f; 0x45; 0xd9;  (* CMOVNE (% rbx) (% r9) *)
  0x48; 0x89; 0x5a; 0x08;  (* MOV (Memop Quadword (%% (rdx,8))) (% rbx) *)
  0x49; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% r10) *)
  0x48; 0x89; 0x4a; 0x10;  (* MOV (Memop Quadword (%% (rdx,16))) (% rcx) *)
  0x49; 0x0f; 0x45; 0xeb;  (* CMOVNE (% rbp) (% r11) *)
  0x48; 0x89; 0x6a; 0x18;  (* MOV (Memop Quadword (%% (rdx,24))) (% rbp) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 1)) *)
  0xe8; 0x0f; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 527)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0x33; 0x44; 0x24; 0x20;
                           (* XOR (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x8b; 0x5c; 0x24; 0x08;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x09; 0xdd;        (* OR (% rbp) (% rbx) *)
  0x48; 0x33; 0x5c; 0x24; 0x28;
                           (* XOR (% rbx) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x09; 0xd8;        (* OR (% rax) (% rbx) *)
  0x48; 0x8b; 0x4c; 0x24; 0x10;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x09; 0xcd;        (* OR (% rbp) (% rcx) *)
  0x48; 0x33; 0x4c; 0x24; 0x30;
                           (* XOR (% rcx) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x8b; 0x54; 0x24; 0x18;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x09; 0xd5;        (* OR (% rbp) (% rdx) *)
  0x48; 0x33; 0x54; 0x24; 0x38;
                           (* XOR (% rdx) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x09; 0xd1;        (* OR (% rcx) (% rdx) *)
  0x48; 0x09; 0xc8;        (* OR (% rax) (% rcx) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x8d; 0x44; 0x00; 0x01;
                           (* LEA (% rax) (%%%% (rax,0,rax,&1)) *)
  0x48; 0x85; 0xed;        (* TEST (% rbp) (% rbp) *)
  0x48; 0x0f; 0x44; 0xc5;  (* CMOVE (% rax) (% rbp) *)
  0x48; 0x81; 0xc4; 0xb0; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 176)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x11;        (* MOV (% rdx) (Memop Quadword (%% (rcx,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0e;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x66; 0x18;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x51; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rcx,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6e; 0x18;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADOX (% r13) (% rbp) *)
  0x49; 0x11; 0xed;        (* ADC (% r13) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x51; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rcx,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x76; 0x18;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADOX (% r14) (% rbp) *)
  0x49; 0x11; 0xee;        (* ADC (% r14) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x51; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rcx,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xf3; 0xf6; 0x7e; 0x18;
                           (* MULX4 (% r15,% rcx) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdf;
                           (* MULX4 (% rbx,% rax) (% rdx,% r15) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADOX (% r15) (% rbp) *)
  0x49; 0x11; 0xef;        (* ADC (% r15) (% rbp) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x11; 0xeb;        (* ADC (% rbx) (% rbp) *)
  0x48; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% rax) (Imm8 (word 63)) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x48; 0x8d; 0x4b; 0x01;  (* LEA (% rcx) (%% (rbx,1)) *)
  0x48; 0x6b; 0xc9; 0x13;  (* IMUL3 (% rcx) (% rcx,Imm8 (word 19)) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdc;
                           (* MULX4 (% rbx,% rax) (% rdx,% r12) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdd;
                           (* MULX4 (% rbx,% rax) (% rdx,% r13) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xde;
                           (* MULX4 (% rbx,% rax) (% rdx,% r14) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdf;
                           (* MULX4 (% rbx,% rax) (% rdx,% r15) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x48; 0xc1; 0xe1; 0x3f;  (* SHL (% rcx) (Imm8 (word 63)) *)
  0x49; 0x39; 0xcb;        (* CMP (% r11) (% rcx) *)
  0xb8; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 19)) *)
  0x48; 0x0f; 0x49; 0xc5;  (* CMOVNS (% rax) (% rbp) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xe9;        (* SBB (% r9) (% rbp) *)
  0x49; 0x19; 0xea;        (* SBB (% r10) (% rbp) *)
  0x49; 0x19; 0xeb;        (* SBB (% r11) (% rbp) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3;                    (* RET *)
  0x48; 0x8b; 0x02;        (* MOV (% rax) (Memop Quadword (%% (rdx,0))) *)
  0x48; 0x8b; 0x5a; 0x08;  (* MOV (% rbx) (Memop Quadword (%% (rdx,8))) *)
  0x48; 0x8b; 0x4a; 0x10;  (* MOV (% rcx) (Memop Quadword (%% (rdx,16))) *)
  0x48; 0x8b; 0x52; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rdx,24))) *)
  0x48; 0x89; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rax) *)
  0x48; 0x89; 0x9c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% rbx) *)
  0x48; 0x89; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rdx) *)
  0x48; 0x8b; 0x94; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,136))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% r8) (% rdx,% rdx) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rsp,144))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0xc4; 0x62; 0x93; 0xf6; 0xb4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,136))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,144))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,160))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,144))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADCX (% r13) (% rbx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xcf;
                           (* ADOX (% r9) (% r15) *)
  0x48; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,144))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% r10) (% r10) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% r10) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% r11) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xda;
                           (* ADOX (% r11) (% rdx) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe4;
                           (* ADCX (% r12) (% r12) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADOX (% r12) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% r13) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xea;
                           (* ADOX (% r13) (% rdx) *)
  0x48; 0x8b; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,160))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADCX (% r15) (% rbx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcc;
                           (* MULX4 (% rcx,% rax) (% rdx,% r12) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcd;
                           (* MULX4 (% rcx,% rax) (% rdx,% r13) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xce;
                           (* MULX4 (% rcx,% rax) (% rdx,% r14) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0x42; 0xfb; 0xf6; 0xe7;
                           (* MULX4 (% r12,% rax) (% rdx,% r15) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADCX (% r12) (% rbx) *)
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
  0x4c; 0x89; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r11) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x0f; 0x85; 0x5c; 0xfe; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294966876)) *)
  0xb8; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 19)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x4c; 0x11; 0xcb;        (* ADC (% rbx) (% r9) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x11; 0xda;        (* ADC (% rdx) (% r11) *)
  0x49; 0x0f; 0x49; 0xc0;  (* CMOVNS (% rax) (% r8) *)
  0x49; 0x0f; 0x49; 0xd9;  (* CMOVNS (% rbx) (% r9) *)
  0x49; 0x0f; 0x49; 0xca;  (* CMOVNS (% rcx) (% r10) *)
  0x49; 0x0f; 0x49; 0xd3;  (* CMOVNS (% rdx) (% r11) *)
  0x48; 0x0f; 0xba; 0xf2; 0x3f;
                           (* BTR (% rdx) (Imm8 (word 63)) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x89; 0x5f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rbx) *)
  0x48; 0x89; 0x4f; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rcx) *)
  0x48; 0x89; 0x57; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rdx) *)
  0xc3                     (* RET *)
];;

let bignum_sqrt_p25519_tmc = define_trimmed "bignum_sqrt_p25519_tmc" bignum_sqrt_p25519_mc;;

let BIGNUM_SQRT_P25519_EXEC = X86_MK_EXEC_RULE bignum_sqrt_p25519_tmc;;

(* ------------------------------------------------------------------------- *)
(* Local subroutine correctness.                                             *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let p25519approxredlemma = prove
 (`!m n. n < 40 * 2 EXP 256 /\
         n <= 2 EXP 192 * m + 2 EXP 255 /\
         2 EXP 192 * m <= n
         ==> let q = m DIV 2 EXP 63 + 1 in
             q <= 80 /\
             q < 2 EXP 64 /\
             q * p_25519 <= n + p_25519 /\
             n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let p25519redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_25519 - 1)
       ==> let q = n DIV 2 EXP 255 + 1 in
           q < 2 EXP 64 /\
           q * p_25519 <= n + p_25519 /\
           n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let LOCAL_MUL_P25519_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x7a0) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sqrt_p25519_tmc /\
                  read RIP s = word(pc + 0x3e2) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = word (pc + 0x590) /\
                  bignum_from_memory (z,4) s = (m * n) MOD p_25519)
        (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RBP;
                    R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN

  (*** The initial multiplication block with quotient estimate inside ***)

  X86_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC (1--60) (1--60) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s4; sum_s15; sum_s30; sum_s45]`;
    `h = bignum_of_wordlist[sum_s49; sum_s52; sum_s56; sum_s58]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma --- fiddly proof ***)

  MP_TAC(SPECL [`2 EXP 64 * val(sum_s60:int64) + val(sum_s59:int64)`;
                `38 * h + l`] p25519approxredlemma) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    TRANS_TAC LE_TRANS
     `2 EXP 192 *
      (38 * (val(mulhi_s47:int64) + bitval carry_s56 + bitval carry_s53) +
       val(sum_s45:int64))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
      `x <= 2 EXP 192 * (38 * h + s) ==> x <= 2 EXP 192 * (38 * (h + c) + s)`);
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES;
                REAL_OF_NUM_DIV; p_25519] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN LET_TAC THEN STRIP_TAC] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (61--64) THEN
  ABBREV_TAC `hw:int64 = word_add
         (word_add (word_add sum_s60 sum_s60)
                   (word(bitval(bit 63 (sum_s59:int64)))))
         (word 1)` THEN
  SUBGOAL_THEN `q = val(hw:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `q < 2 EXP 64` THEN MAP_EVERY EXPAND_TAC ["hw"; "q"] THEN
    REWRITE_TAC[VAL_WORD_BITVAL; VAL_WORD_ADD; DIMINDEX_64; VAL_WORD_1] THEN
    CONV_TAC MOD_DOWN_CONV THEN MATCH_MP_TAC(MESON[MOD_LT]
     `y = x ==> x < e ==> x = y MOD e`) THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 63 * 2`] THEN
    SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[ARITH_RULE `((s + s) + b) + 1 = (2 * s + c) + 1 <=> b = c`] THEN
       MP_TAC(ISPEC `sum_s59:int64` MSB_VAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN SIMP_TAC[bitval] THEN
    MP_TAC(SPEC `sum_s59:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Actual accumulation of 38 * h + l + 19 * q ***)

  ABBREV_TAC `q19:int64 = word_mul hw (word 19)` THEN
  X86_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC (66--79) (65--79) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [READ_RVALUE]) THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN

  SUBGOAL_THEN `&(val(q19:int64)):real = &19 * &(val(hw:int64))`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "q19" THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC MOD_DOWN_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(hw:int64) <= 80` THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `val(word_shl (q19:int64) 63) = 2 EXP 63 * val(hw:int64) MOD 2`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_SHL; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_MULT2; ARITH_RULE `2 EXP 64 = 2 EXP 63 * 2`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[VAL_MOD_2; BIT_LSB] THEN
    EXPAND_TAC "q19" THEN AP_TERM_TAC THEN
    REWRITE_TAC[word_mul; modular; ODD_VAL_WORD] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[ODD_MULT; ARITH];
    RULE_ASSUM_TAC(REWRITE_RULE
     [GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; REAL_OF_NUM_MOD])] THEN

  (*** Characterize both mangled and unmangled versions ***)

  SUBGOAL_THEN
   `(&(bignum_of_wordlist[sum_s68; sum_s71; sum_s74; sum_s77]):int ==
     &(38 * h + l) - &p_25519 * &(val(hw:int64))) (mod (&2 pow 255)) /\
    (&(bignum_of_wordlist[sum_s68; sum_s71; sum_s74; sum_s79]):int ==
     &(38 * h + l) - &p_25519 * &(val(hw:int64))) (mod (&2 pow 256))`
  MP_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
    REWRITE_TAC[INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[int_sub_th; int_pow_th; int_of_num_th; int_mul_th] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC] THEN

  (*** The final correction ***)

  X86_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC (82--85) (80--90) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s90" THEN

  SUBGOAL_THEN
   `ival(sum_s79:int64) < &0 <=> 38 * h + l < val(hw:int64) * p_25519`
  SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS
     `2 EXP 255 <= bignum_of_wordlist[sum_s68; sum_s71; sum_s74; sum_s79]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM MSB_IVAL; MSB_VAL; ARITH_RULE
        `2 EXP 255 <= x <=> 2 EXP 63 <= x DIV 2 EXP 192`] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
      REWRITE_TAC[TAUT `(p <=> q) <=> (~q ==> ~p) /\ (q ==> p)`]] THEN
    REWRITE_TAC[INT_NOT_LE; NOT_LE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (can
     (term_match [] `(x:int == y) (mod (&2 pow 256))`) o concl))
    THENL
     [ALL_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
       `(x == y) (mod n) ==> (x:int == y + n) (mod n)`))] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_IMP_EQ)) THEN
    REWRITE_TAC[NOT_IMP] THEN
    (ANTS_TAC THENL
      [MATCH_MP_TAC(INT_ARITH
        `(&0 <= x /\ x < e) /\ (&0 <= y /\ y < e) ==> abs(x - y:int) < e`) THEN
       CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC];
       ALL_TAC] THEN
     POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
     REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN INT_ARITH_TAC);
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT])] THEN

  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 255` THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
  MATCH_MP_TAC INT_CONG_TRANS THEN
  EXISTS_TAC `if val(hw:int64) * p_25519 <= 38 * h + l
              then &(38 * h + l) - &(val(hw:int64)) * &p_25519:int
              else &(38 * h + l) - (&(val(hw:int64)) - &1) * &p_25519` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC INT_EQ_IMP_CONG THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[GSYM int_of_num_th; GSYM INT_OF_NUM_REM] THEN
    REWRITE_TAC[GSYM int_sub_th; GSYM int_mul_th] THEN
    ONCE_REWRITE_TAC[GSYM COND_RAND] THEN REWRITE_TAC[GSYM int_eq] THEN
    REWRITE_TAC[INT_REM_UNIQUE] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`val(hw:int64) * p_25519 <= (38 * h + l) + p_25519`;
        `38 * h + l < val(hw:int64) * p_25519 + p_25519`] THEN
      REWRITE_TAC[p_25519; GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      INTEGER_TAC]] THEN
  MATCH_MP_TAC INT_CONG_TRANS THEN
  EXISTS_TAC
   `if val(hw:int64) * p_25519 <= 38 * h + l
    then &(bignum_of_wordlist [sum_s68; sum_s71; sum_s74; sum_s77]):int
    else &(bignum_of_wordlist [sum_s68; sum_s71; sum_s74; sum_s77]) +
         &p_25519` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_INT_CONGRUENCE; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (can
     (term_match [] `(x:int == y) (mod (&2 pow 255))`) o concl)) THEN
    SPEC_TAC(`(&2:int) pow 255`,`p:int`) THEN INTEGER_TAC] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_add_th; int_mul_th; int_pow_th; int_of_num_th] THEN
  ASM_SIMP_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  ABBREV_TAC `bb <=> val(hw:int64) * p_25519 <= 38 * h + l` THEN
  REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_MOD;
              GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let LOCAL_MUL_TAC =
  X86_SUBROUTINE_SIM_TAC
   (bignum_sqrt_p25519_tmc,BIGNUM_SQRT_P25519_EXEC,
    0x0,bignum_sqrt_p25519_tmc,LOCAL_MUL_P25519_CORRECT)
  [`read RDI s`; `read RSI s`; `read RDX s`;
   `read(memory :> bytes(read RSI s,8 * 4)) s`;
   `read(memory :> bytes(read RDX s,8 * 4)) s`;
   `pc:num`];;

let LOCAL_NSQR_P25519_CORRECT = time prove
 (`!z k x n pc stackpointer.
        nonoverlapping (word pc,0x7a0) (z,8 * 4) /\
        nonoverlapping (stackpointer,184) (word pc,0x7a0) /\
        1 <= val k /\ val k <= 1000
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sqrt_p25519_tmc /\
                  read RIP s = word(pc + 0x591) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [z; k; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = word (pc + 0x79f) /\
                  bignum_from_memory (z,4) s =
                  (n EXP (2 EXP val k)) MOD p_25519)
             (MAYCHANGE [RIP; RSI; RAX; RBX; RCX; RDX; RBP;
                    R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                memory :> bytes(word_add stackpointer (word 136),8*4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  X_GEN_TAC `z:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; ALL; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Top-level squaring loop ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x5c0` `pc + 0x75e`
   `\i s. (read RSP s = stackpointer /\
           read RDI s = z /\
           read RSI s = word(k - i) /\
           (read (memory :> bytes(word_add stackpointer (word 136),8 * 4)) s ==
            n EXP (2 EXP i)) (mod p_25519) /\
           (1 <= i
            ==> read(memory :> bytes(word_add stackpointer (word 136),8 * 4)) s
                < 2 * p_25519 /\
                bignum_of_wordlist
                 [read R8 s; read R9 s; read R10 s; read R11 s] =
                read (memory :> bytes(word_add stackpointer (word 136),8 * 4))
                     s)) /\
          (read ZF s <=> i = k)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LE_1];

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_" `read (memory :> bytes (x,8 * 4)) s0` THEN
    X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP; EXP_1; CONG_REFL; SUB_0] THEN CONV_TAC NUM_REDUCE_CONV;

    ALL_TAC; (*** Main loop invariant ***)

    REPEAT STRIP_TAC THEN X86_SIM_TAC BIGNUM_SQRT_P25519_EXEC [1];

    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_"
     `read (memory :> bytes(word_add stackpointer (word 136),8 * 4)) s0` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BIGNUM_OF_WORDLIST_EQ]) THEN
    ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ] THEN STRIP_TAC THEN
    X86_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC (6--9) (1--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s18" THEN
    REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    ABBREV_TAC `m = bignum_of_wordlist [x_0; x_1; x_2; x_3]` THEN
    MAP_EVERY EXISTS_TAC
     [`255`;
      `if m < p_25519 then &m:real else &m - &p_25519`] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[p_25519] THEN ARITH_TAC;
      REWRITE_TAC[p_25519] THEN ARITH_TAC;
      ALL_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o GEN_REWRITE_RULE I [CONG]) THEN
      ASM_SIMP_TAC[MOD_CASES] THEN
      SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT] THEN MESON_TAC[]] THEN
    REWRITE_TAC[GSYM MSB_IVAL; MSB_VAL] THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [REAL_OF_NUM_ADD]) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`) THEN
    REWRITE_TAC[MOD_MULT_ADD; VAL_WORD_ADD; VAL_WORD] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[GSYM DIMINDEX_64; VAL_MOD_REFL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `(m < p_25519 <=> m + 19 < 2 EXP 255) /\
      (&m - &p_25519:real = &(m + 19) - &2 pow 255)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `2 EXP 256 * bitval carry_s9 +
      bignum_of_wordlist [sum_s6; sum_s7; sum_s8; sum_s9] = m + 19`
    MP_TAC THENL
     [EXPAND_TAC "m" THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `2 EXP 256 * c + s = mm
      ==> mm < 2 EXP 256 /\ (2 EXP 256 * c < 2 EXP 256 * 1 ==> c = 0)
          ==> mm = s`)) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `m < 2 * p_25519` THEN
      REWRITE_TAC[p_25519; LT_MULT_LCANCEL] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[NOT_LE; ARITH_RULE
     `x < 2 EXP 255 <=> x DIV 2 EXP 192 < 2 EXP 63`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    REAL_INTEGER_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[EXP_ADD; GSYM EXP_EXP; EXP_1] THEN
  SPEC_TAC(`n EXP (2 EXP i)`,`n':num`) THEN GEN_TAC THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_"
   `read (memory :> bytes (word_add stackpointer (word 136),8 * 4)) s0` THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_imp o concl)) THEN
  ABBREV_TAC `n = bignum_of_wordlist [n_0; n_1; n_2; n_3]` THEN
   FIRST_ASSUM(fun th ->
     REWRITE_TAC[MATCH_MP
      (NUMBER_RULE `!n a p. (n == a) (mod p)
                            ==> !x. (x == a EXP 2) (mod p) <=>
                                    (x == n EXP 2) (mod p)`) th]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `n':num` o concl))) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8 ***)

  X86_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC (1--41) (1--41) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s2; sum_s23; sum_s27; sum_s29]`;
    `h = bignum_of_wordlist[sum_s33; sum_s35; sum_s39; sum_s41]`] THEN
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

  X86_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC (42--56) (42--56) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s45; sum_s48; sum_s51; sum_s54; sum_s56]` THEN
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

  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (57--60) THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s56 sum_s54) (63,64)` THEN
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

  X86_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC (61--64) (61--69) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k ==> 1 <= k - i`];
    DISCH_THEN SUBST1_TAC] THEN
  VAL_INT64_TAC `k - (i + 1)` THEN
  ASM_SIMP_TAC[SUB_EQ_0; ARITH_RULE
   `i < k ==> (k <= i + 1 <=> i + 1 = k)`] THEN
  REWRITE_TAC[ARITH_RULE `1 <= i + 1`] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> (x == ca) (mod p) /\ x:int < p2`) THEN
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

let LOCAL_NSQR_TAC =
  X86_SUBROUTINE_SIM_TAC
   (bignum_sqrt_p25519_tmc,BIGNUM_SQRT_P25519_EXEC,
    0x0,bignum_sqrt_p25519_tmc,LOCAL_NSQR_P25519_CORRECT)
  [`read RDI s`; `read RSI s`; `read RDX s`;
   `read(memory :> bytes(read RDX s,8 * 4)) s`;
   `pc:num`; `stackpointer:int64`];;

(* ------------------------------------------------------------------------- *)
(* Finding modular square roots in this setting.                             *)
(* ------------------------------------------------------------------------- *)

let MODULAR_SQRT_5MOD8 = prove
 (`!p a i.
        prime p /\ (p == 5) (mod 8) /\ (i EXP 2 + 1 == 0) (mod p)
        ==> let y = a EXP ((p + 3) DIV 8) in
            ((?x. (x EXP 2 == a) (mod p)) <=>
             (y EXP 2 == a) (mod p) \/ ((i * y) EXP 2 == a) (mod p))`,
  REPEAT STRIP_TAC THEN CONV_TAC let_CONV THEN
  EQ_TAC THENL [DISCH_TAC; MESON_TAC[]] THEN
  ASM_SIMP_TAC[NUMBER_RULE
   `(i EXP 2 + 1 == 0) (mod p)
    ==> (((i * y) EXP 2 == a) (mod p) <=> (y EXP 2 + a == 0) (mod p))`] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INT_CONG; INT_SUB_RZERO] THEN
  ASM_SIMP_TAC[GSYM PRIME_INT_DIVPROD_EQ] THEN
  REWRITE_TAC[INTEGER_RULE
   `(p:int) divides ((x - a) * (x + a)) <=> (x pow 2 == a pow 2) (mod p)`] THEN
  REWRITE_TAC[INT_POW_POW] THEN
  SUBGOAL_THEN `(p + 3) DIV 8 * 2 * 2 = 2 + (p - 1) DIV 2` SUBST1_TAC THENL
   [UNDISCH_TAC `(p == 5) (mod 8)` THEN ASM_SIMP_TAC[CONG_CASE; ARITH] THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[ARITH_RULE `(q * 8 + 5) + 3 = 8 * (q + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `(q * 8 + 5) - 1 = 2 * (q * 4 + 2)`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ARITH_TAC;
    REWRITE_TAC[INT_POW_ADD]] THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  MP_TAC(SPECL [`p:num`; `a:num`] EULER_CRITERION) THEN
  ASM_REWRITE_TAC[] THEN NUMBER_TAC);;

let MODULAR_I_5MOD8 = prove
 (`!p. prime p /\ (p == 5) (mod 8)
       ==> ((2 EXP ((p - 1) DIV 4)) EXP 2 + 1 == 0) (mod p)`,
  GEN_TAC THEN ASM_CASES_TAC `p = 2` THENL
   [ASM_REWRITE_TAC[CONG] THEN ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[EXP_EXP] THEN
  SUBGOAL_THEN `(p - 1) DIV 4 * 2 = (p - 1) DIV 2` SUBST1_TAC THENL
   [UNDISCH_TAC `(p == 5) (mod 8)` THEN ASM_SIMP_TAC[CONG_CASE; ARITH] THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[ARITH_RULE `(q * 8 + 5) - 1 = 2 * 2 * (2 * q + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `x DIV 4 = x DIV 2 DIV 2`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!x:int. (x == a) (mod p) /\ (x == --b) (mod p)
            ==> (a + b == &0) (mod p)`) THEN
  EXISTS_TAC `jacobi(2,p)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[JACOBI_EULER_ALT]; ALL_TAC] THEN
  MP_TAC(SPEC `p:num` JACOBI_OF_2_CASES) THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[PRIME_ODD; NOT_ODD]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONG]) THEN
  ASM_REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INTEGER_RULE);;

let MODULAR_SQRT_5MOD8_EXPLICIT = prove
 (`!p a.
        prime p /\ (p == 5) (mod 8)
        ==> let i = 2 EXP ((p - 1) DIV 4) in
            let y = a EXP ((p + 3) DIV 8) in
            ((?x. (x EXP 2 == a) (mod p)) <=>
             (y EXP 2 == a) (mod p) \/ ((i * y) EXP 2 == a) (mod p))`,
  REPEAT STRIP_TAC THEN CONV_TAC let_CONV THEN
  MATCH_MP_TAC MODULAR_SQRT_5MOD8 THEN ASM_SIMP_TAC[MODULAR_I_5MOD8]);;

let P_25519 = prove
 (`p_25519 = 2 EXP 255 - 19`,
  REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let PRIME_P25519 = prove
 (`prime p_25519`,
  REWRITE_TAC[p_25519] THEN (CONV_TAC o PRIME_RULE)
   ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "41";
    "43"; "47"; "53"; "59"; "83"; "97"; "103"; "107"; "127"; "131"; "173";
    "223"; "239"; "353"; "419"; "479"; "487"; "991"; "1723"; "2437"; "3727";
    "4153"; "9463"; "32573"; "37853"; "57467"; "65147"; "75707"; "132049";
    "430751"; "569003"; "1923133"; "8574133"; "2773320623"; "72106336199";
    "1919519569386763"; "31757755568855353";
    "75445702479781427272750846543864801";
    "74058212732561358302231226437062788676166966415465897661863160754340907";
"57896044618658097711785492504343953926634992332820282019728792003956564819949"
]);;

let j_25519 = define
 `j_25519 =
19681161376707505956807079304988542015446066515923890162744021073123829784752`;;

let MODULAR_SQRT_P25519 = prove
 (`!a. let y = (a EXP (2 EXP 252 - 2)) MOD p_25519 in
       (?x. (x EXP 2 == a) (mod p_25519)) <=>
       (y EXP 2 == a) (mod p_25519) \/
       ((j_25519 * y) EXP 2 == a) (mod p_25519)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`p_25519`; `a:num`; `j_25519`] MODULAR_SQRT_5MOD8) THEN
  REWRITE_TAC[PRIME_P25519] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  SUBGOAL_THEN `(p_25519 + 3) DIV 8 = 2 EXP 252 - 2` SUBST1_TAC THENL
   [ALL_TAC; DISCH_THEN MATCH_MP_TAC] THEN
  REWRITE_TAC[p_25519; j_25519] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Overall proof.                                                            *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SQRT_P25519_CORRECT = time prove
 (`!z x n pc stackpointer.
        ALL (nonoverlapping (stackpointer,184))
            [(word pc,0x7a0); (z,8 * 4); (x,8 * 4)] /\
        nonoverlapping (word pc,0x7a0) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sqrt_p25519_tmc /\
                  read RIP s = word(pc + 0x11) /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = word (pc + 0x3d0) /\
                  ival(C_RETURN s) = jacobi(n,p_25519) /\
                  bignum_from_memory (z,4) s < p_25519 /\
                  EVEN(bignum_from_memory (z,4) s) /\
                  (jacobi(n,p_25519) >= &0
                   ==> (bignum_from_memory (z,4) s EXP 2 == n) (mod p_25519)))
             (MAYCHANGE [RIP; RDI; RSI; RAX; RBX; RCX; RDX; RBP;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(stackpointer,184)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN

  (*** Initial modular reduction, trivial tweak of bignum_mod_p25519_4 ***)

  ENSURES_SEQUENCE_TAC `pc + 0x75`
   `\s. read RSP s = word_add stackpointer (word 8) /\
        read (memory :> bytes64(word_add stackpointer (word 168))) s = z /\
        bignum_from_memory(word_add stackpointer (word 8),4) s =
        n MOD p_25519` THEN
  CONJ_TAC THENL
   [BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN
    ABBREV_TAC `b <=> bit 63 (n_3:int64)` THEN
    SUBGOAL_THEN
     `val(n_3:int64) DIV 2 EXP 63 = bitval b /\
      n DIV 2 EXP 255 = bitval b`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "n" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      EXPAND_TAC "b" THEN REWRITE_TAC[BIT_VAL] THEN
      SUBGOAL_THEN `val(n_3:int64) DIV 2 EXP 63 < 2` MP_TAC THENL
       [MP_TAC(SPEC `n_3:int64` VAL_BOUND_64) THEN ARITH_TAC;
        SPEC_TAC(`val(n_3:int64) DIV 2 EXP 63`,`bb:num`)] THEN
      CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[ARITH; BITVAL_CLAUSES];
      ALL_TAC] THEN
    X86_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC
     [11;12;13;14;17;18;19;20] (1--25) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&(val(word_mul (word_add (word 1) (word (bitval b)))
                     (word 19:int64))):real =
      &19 * (&1 + &(bitval b))`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_MUL; DIMINDEX_64; VAL_WORD_BITVAL] THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM] THEN
      MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(val(word_or n_3 (word 9223372036854775808):int64)):real =
      &(val n_3) + &2 pow 63 * (&1 - &(bitval b))`
    SUBST_ALL_TAC THENL
     [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
       `word_or x m = word_or (word_and x (word_not m)) m`] THEN
      SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
       `word_and (word_and x (word_not m)) m = word 0`] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s25" THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`255`;
      `if n < (bitval b + 1) * p_25519
       then &n - &(bitval b) * &p_25519
       else &n - (&(bitval b) + &1) * &p_25519:real`] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[p_25519] THEN ARITH_TAC;
      REWRITE_TAC[p_25519] THEN ARITH_TAC;
      ALL_TAC;
      ASM_SIMP_TAC[REAL_OF_NUM_MOD; EQT_ELIM
       ((REWRITE_CONV[p_25519] THENC (EQT_INTRO o ARITH_RULE))
        `n < 2 EXP (64 * 4)
         ==> n DIV p_25519 =
             if n < (n DIV 2 EXP 255 + 1) * p_25519
             then n DIV 2 EXP 255 else n DIV 2 EXP 255 + 1`)] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES]] THEN
    SUBGOAL_THEN `n < (bitval b + 1) * p_25519 <=> ~carry_s14` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
      EXISTS_TAC `256` THEN
      EXPAND_TAC "n" THEN REWRITE_TAC[p_25519; bignum_of_wordlist] THEN
      REWRITE_TAC[REAL_BITVAL_NOT; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      EXPAND_TAC "n" THEN REWRITE_TAC[COND_SWAP; bignum_of_wordlist] THEN
      REWRITE_TAC[p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_CASES_TAC `carry_s14:bool` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
      REAL_INTEGER_TAC];
    ONCE_REWRITE_TAC[GSYM CONG_RMOD; GSYM JACOBI_MOD] THEN
    SUBGOAL_THEN `n MOD p_25519 < p_25519` MP_TAC THENL
     [REWRITE_TAC[MOD_LT_EQ; p_25519; ARITH_EQ]; ALL_TAC] THEN
    SPEC_TAC(`n MOD p_25519`,`n:num`) THEN REPEAT STRIP_TAC] THEN

  (*** The big exponentiation tower ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (1--4) THEN LOCAL_NSQR_TAC 5 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (6--10) THEN LOCAL_MUL_TAC 11 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (12--16) THEN LOCAL_NSQR_TAC 17 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (18--22) THEN LOCAL_MUL_TAC 23 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (24--28) THEN LOCAL_NSQR_TAC 29 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (30--34) THEN LOCAL_MUL_TAC 35 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (36--40) THEN LOCAL_NSQR_TAC 41 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (42--46) THEN LOCAL_MUL_TAC 47 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (48--52) THEN LOCAL_NSQR_TAC 53 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (54--58) THEN LOCAL_MUL_TAC 59 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (60--64) THEN LOCAL_NSQR_TAC 65 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (66--70) THEN LOCAL_MUL_TAC 71 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (72--76) THEN LOCAL_NSQR_TAC 77 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (78--82) THEN LOCAL_MUL_TAC 83 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (84--88) THEN LOCAL_NSQR_TAC 89 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (90--94) THEN LOCAL_MUL_TAC 95 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (96--100) THEN LOCAL_NSQR_TAC 101 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (102--106) THEN LOCAL_MUL_TAC 107 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (108--112) THEN LOCAL_NSQR_TAC 113 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (114--118) THEN LOCAL_MUL_TAC 119 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (120--124) THEN LOCAL_NSQR_TAC 125 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (126--130) THEN LOCAL_MUL_TAC 131 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (132--136) THEN LOCAL_NSQR_TAC 137 THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC [138] THEN

  REABBREV_TAC
   `c =
    read (memory :> bytes (word_add stackpointer (word 72),8 * 4)) s138` THEN
  POP_ASSUM(MP_TAC o CONV_RULE MOD_DOWN_CONV) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) THEN
  REWRITE_TAC[MULT_EXP] THEN REWRITE_TAC[EXP_EXP] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
  DISCH_TAC THEN

  (*** Multiplication by j_25519 ***)

  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (139--150) THEN
  SUBGOAL_THEN
    `read (memory :> bytes(word_add stackpointer (word 104),8 * 4)) s150 =
     j_25519`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; j_25519] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  LOCAL_MUL_TAC 151 THEN

  (*** Squaring of s ***)

  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (152--156) THEN
  LOCAL_NSQR_TAC 157 THEN

  (*** Comparison and multiplexing ***)

  BIGNUM_LDIGITIZE_TAC "a_"
   `read (memory :> bytes (word_add stackpointer (word 8),8 * 4)) s157` THEN
  BIGNUM_LDIGITIZE_TAC "b_"
   `read (memory :> bytes (word_add stackpointer (word 40),8 * 4)) s157` THEN
  BIGNUM_LDIGITIZE_TAC "c_"
   `read (memory :> bytes (word_add stackpointer (word 72),8 * 4)) s157` THEN
  BIGNUM_LDIGITIZE_TAC "d_"
   `read (memory :> bytes (word_add stackpointer (word 104),8 * 4)) s157` THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (158--181) THEN
  MAP_EVERY ABBREV_TAC
   [`e_0 = read RAX s181`; `e_1 = read RBX s181`;
    `e_2 = read RCX s181`; `e_3 = read RBP s181`] THEN
  ABBREV_TAC `e = bignum_of_wordlist[e_0; e_1; e_2; e_3]` THEN

  SUBGOAL_THEN
   `e < p_25519 /\
    ((?x. (x EXP 2 == n) (mod p_25519)) <=> (e EXP 2 == n) (mod p_25519))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `e = if (c EXP 2 == n) (mod p_25519) then c
          else (c * j_25519) MOD p_25519`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; WORD_OR_EQ_0] THEN
      REWRITE_TAC[WORD_XOR_EQ_0; GSYM CONJ_ASSOC] THEN
      SUBGOAL_THEN
       `a_0:int64 = b_0 /\ a_1:int64 = b_1 /\
        a_2:int64 = b_2 /\ a_3:int64 = b_3 <=>
        (c EXP 2 == n) (mod p_25519)`
      SUBST1_TAC THENL
       [ALL_TAC; COND_CASES_TAC THEN ASM_REWRITE_TAC[]] THEN
      TRANS_TAC EQ_TRANS
       `bignum_of_wordlist [a_0; a_1; a_2; a_3] =
        bignum_of_wordlist [b_0; b_1; b_2; b_3]` THEN
      CONJ_TAC THENL [REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[CONG; MOD_LT] THEN
      REWRITE_TAC[VAL_WORD_1; EXP_1] THEN MESON_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_REDUCE_CONV `2 EXP 252 - 2`)]) THEN
    CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `n EXP (2 EXP 252 - 2) MOD p_25519 = c`)) THEN
      COND_CASES_TAC THEN REWRITE_TAC[MOD_LT_EQ; p_25519] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `n:num` MODULAR_SQRT_P25519) THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(c EXP 2 == n) (mod p_25519)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CONG; MULT_SYM] THEN CONV_TAC MOD_DOWN_CONV THEN
    REFL_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`p = if x then y else z`]] THEN

  (*** Negation to zero the LSB ***)

  X86_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC [188;189;190;191] (182--201) THEN
  ABBREV_TAC `f = read (memory :> bytes (z,8 * 4)) s201` THEN
  SUBGOAL_THEN `(if EVEN e then e else p_25519 - e) = f` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "e" THEN
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV o RAND_CONV)
     [bignum_of_wordlist] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; EVEN_EXP; ARITH] THEN
    REWRITE_TAC[WORD_AND_1_BITVAL; VAL_WORD_BITVAL] THEN
    REWRITE_TAC[BITVAL_EQ_0; BIT_LSB; GSYM NOT_EVEN; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `(e EXP 2 == n) (mod p_25519) <=> (f EXP 2 == n) (mod p_25519)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
    POP_ASSUM(SUBST1_TAC o SYM) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
    REWRITE_TAC[INTEGER_RULE
     `((p - x:int) pow 2 == n) (mod p) <=> (x pow 2 == n) (mod p)`];
    ALL_TAC] THEN

  (*** Final computations to get return value ***)

  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (202--204) THEN LOCAL_NSQR_TAC 205 THEN
  BIGNUM_LDIGITIZE_TAC "g_"
   `read (memory :> bytes (word_add stackpointer (word 40),8 * 4)) s205` THEN
  X86_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (206--226) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  GEN_REWRITE_TAC I [TAUT `p /\ q /\ r /\ s <=> q /\ r /\ p /\ s`] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME
     `(if EVEN e then e else p_25519 - e) = f`)) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[EVEN] `~EVEN x ==> ~(x = 0)`)) THEN
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME
    `(if EVEN e then e else p_25519 - e) = f`)) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[EVEN_SUB] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[JACOBI_PRIME; PRIME_P25519] THEN
  ASM_SIMP_TAC[DIVIDES_MOD; MOD_LT] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_0; WORD_OR_EQ_0; GSYM CONJ_ASSOC] THEN
  MP_TAC(SPEC `[a_0:int64; a_1; a_2; a_3]` BIGNUM_OF_WORDLIST_EQ_0) THEN
  ASM_REWRITE_TAC[ALL] THEN DISCH_THEN(MP_TAC o SYM) THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THEN
    ASM_REWRITE_TAC[IVAL_EQ_0; WORD_OR_EQ_0; GSYM CONJ_ASSOC] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN POP_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC I [SYM th]) THEN
    EXISTS_TAC `0` THEN CONV_TAC NUMBER_RULE;
    REWRITE_TAC[WORD_XOR_EQ_0]] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC INT_ARITH] THEN
  MP_TAC(SPECL
   [`a_0:int64`; `[a_1:int64; a_2; a_3]`;
    `g_0:int64`; `[g_1:int64; g_2; g_3]`]
   BIGNUM_OF_WORDLIST_EQ) THEN
  ASM_REWRITE_TAC[VAL_WORD_1; EXP_1] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ; WORD_XOR_EQ_0] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[CONG; MOD_LT; EQ_SYM_EQ] THEN
  COND_CASES_TAC THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let BIGNUM_SQRT_P25519_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 232),232))
            [(word pc,LENGTH bignum_sqrt_p25519_tmc); (z,8 * 4); (x,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 4))
            [(word pc,LENGTH bignum_sqrt_p25519_tmc); (word_sub stackpointer (word 232),240)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sqrt_p25519_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ival(C_RETURN s) = jacobi (n,p_25519) /\
                  bignum_from_memory (z,4) s < p_25519 /\
                  EVEN (bignum_from_memory (z,4) s) /\
                  (jacobi (n,p_25519) >= &0
                   ==> (bignum_from_memory (z,4) s EXP 2 == n) (mod p_25519)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                    memory :> bytes(word_sub stackpointer (word 232),232)])`,
  X86_ADD_RETURN_STACK_TAC
   BIGNUM_SQRT_P25519_EXEC BIGNUM_SQRT_P25519_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 232);;

let BIGNUM_SQRT_P25519_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 232),232))
            [(word pc,LENGTH bignum_sqrt_p25519_mc); (z,8 * 4); (x,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 4))
            [(word pc,LENGTH bignum_sqrt_p25519_mc); (word_sub stackpointer (word 232),240)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sqrt_p25519_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ival(C_RETURN s) = jacobi (n,p_25519) /\
                  bignum_from_memory (z,4) s < p_25519 /\
                  EVEN (bignum_from_memory (z,4) s) /\
                  (jacobi (n,p_25519) >= &0
                   ==> (bignum_from_memory (z,4) s EXP 2 == n) (mod p_25519)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                    memory :> bytes(word_sub stackpointer (word 232),232)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SQRT_P25519_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_sqrt_p25519_windows_mc = define_from_elf
  "bignum_sqrt_p25519_windows_mc"
  "x86/curve25519/bignum_sqrt_p25519.obj";;

let bignum_sqrt_p25519_windows_tmc = define_trimmed "bignum_sqrt_p25519_windows_tmc" bignum_sqrt_p25519_windows_mc;;

let BIGNUM_SQRT_P25519_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 256),256))
            [(word pc,LENGTH bignum_sqrt_p25519_windows_tmc); (z,8 * 4); (x,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 4))
            [(word pc,LENGTH bignum_sqrt_p25519_windows_tmc); (word_sub stackpointer (word 256),264)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sqrt_p25519_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ival(C_RETURN s) = jacobi (n,p_25519) /\
                  bignum_from_memory (z,4) s < p_25519 /\
                  EVEN (bignum_from_memory (z,4) s) /\
                  (jacobi (n,p_25519) >= &0
                   ==> (bignum_from_memory (z,4) s EXP 2 == n) (mod p_25519)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                    memory :> bytes(word_sub stackpointer (word 256),256)])`,
  let WINDOWS_BIGNUM_SQRT_P25519_EXEC =
    X86_MK_EXEC_RULE bignum_sqrt_p25519_windows_tmc
  and subth =
   X86_SIMD_SHARPEN_RULE
    (REWRITE_RULE[fst BIGNUM_SQRT_P25519_EXEC]
       BIGNUM_SQRT_P25519_NOIBT_SUBROUTINE_CORRECT)
    (X86_ADD_RETURN_STACK_TAC
      BIGNUM_SQRT_P25519_EXEC BIGNUM_SQRT_P25519_CORRECT
      `[RBX; RBP; R12; R13; R14; R15]` 232) in
  REWRITE_TAC[fst WINDOWS_BIGNUM_SQRT_P25519_EXEC] THEN
  REPLICATE_TAC 4 GEN_TAC THEN WORD_FORALL_OFFSET_TAC 256 THEN
  REWRITE_TAC[ALL; WINDOWS_C_ARGUMENTS; SOME_FLAGS; C_RETURN;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC WINDOWS_BIGNUM_SQRT_P25519_EXEC (1--5) THEN
  X86_SUBROUTINE_SIM_TAC
   (bignum_sqrt_p25519_windows_tmc,
    WINDOWS_BIGNUM_SQRT_P25519_EXEC,
    0x10,bignum_sqrt_p25519_tmc,subth)
     [`read RDI s`; `read RSI s`;
      `read (memory :> bytes (read RSI s,8 * 4)) s`;
      `pc + 0x10`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
      6 THEN
  X86_STEPS_TAC WINDOWS_BIGNUM_SQRT_P25519_EXEC (7--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let BIGNUM_SQRT_P25519_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 256),256))
            [(word pc,LENGTH bignum_sqrt_p25519_windows_mc); (z,8 * 4); (x,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 4))
            [(word pc,LENGTH bignum_sqrt_p25519_windows_mc); (word_sub stackpointer (word 256),264)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sqrt_p25519_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ival(C_RETURN s) = jacobi (n,p_25519) /\
                  bignum_from_memory (z,4) s < p_25519 /\
                  EVEN (bignum_from_memory (z,4) s) /\
                  (jacobi (n,p_25519) >= &0
                   ==> (bignum_from_memory (z,4) s EXP 2 == n) (mod p_25519)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                    memory :> bytes(word_sub stackpointer (word 256),256)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SQRT_P25519_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

