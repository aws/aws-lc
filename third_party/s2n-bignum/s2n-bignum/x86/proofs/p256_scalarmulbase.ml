(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar multiplication for NIST P-256 precomputed point.                   *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp256.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

needs "x86/proofs/bignum_demont_p256.ml";;
needs "x86/proofs/bignum_inv_p256.ml";;
needs "x86/proofs/bignum_montmul_p256.ml";;
needs "x86/proofs/bignum_montsqr_p256.ml";;
needs "x86/proofs/p256_montjmixadd.ml";;

(* ------------------------------------------------------------------------- *)
(* Code.                                                                     *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "x86/p256/p256_scalarmulbase.o";;
 ****)

let p256_scalarmulbase_mc = define_assert_from_elf
  "p256_scalarmulbase_mc" "x86/p256/p256_scalarmulbase.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x48; 0x81; 0xec; 0x60; 0x01; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 352)) *)
  0x48; 0x89; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% rdi) *)
  0x48; 0x89; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% rdx) *)
  0x48; 0x89; 0x8c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% rcx) *)
  0x49; 0xbc; 0x51; 0x25; 0x63; 0xfc; 0xc2; 0xca; 0xb9; 0xf3;
                           (* MOV (% r12) (Imm64 (word 17562291160714782033)) *)
  0x49; 0xbd; 0x84; 0x9e; 0x17; 0xa7; 0xad; 0xfa; 0xe6; 0xbc;
                           (* MOV (% r13) (Imm64 (word 13611842547513532036)) *)
  0x49; 0xc7; 0xc6; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r14) (Imm32 (word 4294967295)) *)
  0x49; 0xbf; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r15) (Imm64 (word 18446744069414584320)) *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4d; 0x29; 0xe0;        (* SUB (% r8) (% r12) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4d; 0x19; 0xe9;        (* SBB (% r9) (% r13) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4d; 0x19; 0xf2;        (* SBB (% r10) (% r14) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x4d; 0x19; 0xfb;        (* SBB (% r11) (% r15) *)
  0x4c; 0x0f; 0x42; 0x06;  (* CMOVB (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x0f; 0x42; 0x4e; 0x08;
                           (* CMOVB (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x0f; 0x42; 0x56; 0x10;
                           (* CMOVB (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x0f; 0x42; 0x5e; 0x18;
                           (* CMOVB (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% rax) *)
  0x4c; 0x8b; 0x04; 0x24;  (* MOV (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x10;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x18;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x8b; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,296))) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0xd3; 0xe0;        (* SHL (% rax) (% cl) *)
  0x48; 0xff; 0xc8;        (* DEC (% rax) *)
  0x4c; 0x21; 0xc0;        (* AND (% rax) (% r8) *)
  0x4d; 0x0f; 0xad; 0xc8;  (* SHRD (% r8) (% r9) (% cl) *)
  0x4d; 0x0f; 0xad; 0xd1;  (* SHRD (% r9) (% r10) (% cl) *)
  0x4d; 0x0f; 0xad; 0xda;  (* SHRD (% r10) (% r11) (% cl) *)
  0x49; 0xd3; 0xeb;        (* SHR (% r11) (% cl) *)
  0x48; 0x03; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* ADD (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0x89; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% rax) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x8b; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0xd3; 0xe0;        (* SHL (% rax) (% cl) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xd1; 0xe8;        (* SHR (% rax) (Imm8 (word 1)) *)
  0x48; 0x2b; 0x9c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* SUB (% rbx) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0x3b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* CMP (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0x0f; 0x43; 0x9c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* CMOVAE (% rbx) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x89; 0x9c; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% rbx) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% rax) *)
  0x48; 0x8b; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0xff; 0xc9;        (* DEC (% rcx) *)
  0xbe; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 1)) *)
  0x48; 0xd3; 0xe6;        (* SHL (% rsi) (% cl) *)
  0x4c; 0x8b; 0xa4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,336))) *)
  0x48; 0x8b; 0xac; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,304))) *)
  0x49; 0x83; 0xec; 0x01;  (* SUB (% r12) (Imm8 (word 1)) *)
  0x48; 0x0f; 0x44; 0x45; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0x5d; 0x08;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0x4d; 0x10;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0x55; 0x18;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rbp,24))) *)
  0x4c; 0x0f; 0x44; 0x45; 0x20;
                           (* CMOVE (% r8) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0x4d; 0x28;
                           (* CMOVE (% r9) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0x55; 0x30;
                           (* CMOVE (% r10) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0x5d; 0x38;
                           (* CMOVE (% r11) (Memop Quadword (%% (rbp,56))) *)
  0x48; 0x83; 0xc5; 0x40;  (* ADD (% rbp) (Imm8 (word 64)) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x75; 0xcb;              (* JNE (Imm8 (word 203)) *)
  0x48; 0x89; 0xac; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% rbp) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x4d; 0x8d; 0x66; 0xff;  (* LEA (% r12) (%% (r14,18446744073709551615)) *)
  0x49; 0xbf; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r15) (Imm64 (word 4294967295)) *)
  0x4d; 0x89; 0xfd;        (* MOV (% r13) (% r15) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x4d; 0x29; 0xc4;        (* SUB (% r12) (% r8) *)
  0x4d; 0x19; 0xcd;        (* SBB (% r13) (% r9) *)
  0x4d; 0x19; 0xd6;        (* SBB (% r14) (% r10) *)
  0x4d; 0x19; 0xdf;        (* SBB (% r15) (% r11) *)
  0x48; 0x89; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% rax) *)
  0x48; 0x89; 0x9c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% rbx) *)
  0x48; 0x89; 0x8c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0x85; 0xc0;        (* TEST (% rax) (% rax) *)
  0x4d; 0x0f; 0x45; 0xc4;  (* CMOVNE (% r8) (% r12) *)
  0x4d; 0x0f; 0x45; 0xcd;  (* CMOVNE (% r9) (% r13) *)
  0x4d; 0x0f; 0x45; 0xd6;  (* CMOVNE (% r10) (% r14) *)
  0x4d; 0x0f; 0x45; 0xdf;  (* CMOVNE (% r11) (% r15) *)
  0x4c; 0x89; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% r11) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x94; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,224)) *)
  0xe8; 0x85; 0x1c; 0x00; 0x00;
                           (* CALL (Imm32 (word 7301)) *)
  0x48; 0x8b; 0x84; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,336))) *)
  0x48; 0x85; 0xc0;        (* TEST (% rax) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x89; 0x44; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0x89; 0x44; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x89; 0x44; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0x89; 0x44; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0x89; 0x44; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x0f; 0x45; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* CMOVNE (% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0x89; 0x44; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0xff; 0xc0;        (* INC (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% rax) *)
  0x48; 0x0f; 0xaf; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* IMUL (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0x3d; 0x01; 0x01; 0x00; 0x00;
                           (* CMP (% rax) (Imm32 (word 257)) *)
  0x0f; 0x82; 0x51; 0xfd; 0xff; 0xff;
                           (* JB (Imm32 (word 4294966609)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0x8d; 0x74; 0x24; 0x60;
                           (* LEA (% rsi) (%% (rsp,96)) *)
  0xe8; 0x46; 0x19; 0x00; 0x00;
                           (* CALL (Imm32 (word 6470)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,160)) *)
  0x48; 0x8d; 0x74; 0x24; 0x60;
                           (* LEA (% rsi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0xea; 0x16; 0x00; 0x00;
                           (* CALL (Imm32 (word 5866)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,160)) *)
  0xe8; 0x74; 0x00; 0x00; 0x00;
                           (* CALL (Imm32 (word 116)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,160)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,128)) *)
  0xe8; 0x51; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 337)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0x8d; 0x74; 0x24; 0x60;
                           (* LEA (% rsi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,160)) *)
  0xe8; 0xa6; 0x16; 0x00; 0x00;
                           (* CALL (Imm32 (word 5798)) *)
  0x48; 0x8b; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0x48; 0x89; 0xfb;        (* MOV (% rbx) (% rdi) *)
  0xe8; 0x89; 0x16; 0x00; 0x00;
                           (* CALL (Imm32 (word 5769)) *)
  0x48; 0x8d; 0x7b; 0x20;  (* LEA (% rdi) (%% (rbx,32)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,160)) *)
  0xe8; 0x73; 0x16; 0x00; 0x00;
                           (* CALL (Imm32 (word 5747)) *)
  0x48; 0x81; 0xc4; 0x60; 0x01; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 352)) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0xc3;                    (* RET *)
  0x53;                    (* PUSH (% rbx) *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x48; 0x31; 0xf6;        (* XOR (% rsi) (% rsi) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc8;
                           (* MULX4 (% rcx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc8;
                           (* MULX4 (% rcx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% rbx) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% rax) (% rdx,% r9) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% rbx) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% rsi) (% rcx) *)
  0x41; 0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 0)) *)
  0x66; 0x49; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% rsi) (% r8) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% rbx) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcb;
                           (* MULX4 (% rcx,% rax) (% rdx,% r11) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% rbx) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% rsi) (% rcx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rax) (% rdx,% r10) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% rsi) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcb;
                           (* MULX4 (% rcx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x41; 0xba; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 0)) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xca;
                           (* ADCX (% r9) (% r10) *)
  0x48; 0x89; 0x1f;        (* MOV (Memop Quadword (%% (rdi,0))) (% rbx) *)
  0x48; 0x89; 0x77; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rsi) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xf0; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 240)) *)
  0x48; 0x89; 0xbc; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% rdi) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x48; 0x89; 0xd3;        (* MOV (% rbx) (% rdx) *)
  0x48; 0x8d; 0x41; 0xff;  (* LEA (% rax) (%% (rcx,18446744073709551615)) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x48; 0x89; 0x5c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rbx) *)
  0x48; 0x89; 0x4c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rcx) *)
  0x48; 0x89; 0x54; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rdx) *)
  0x48; 0x89; 0x4c; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rcx) *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x8d; 0x41; 0x01;  (* LEA (% rax) (%% (rcx,1)) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x48; 0x8d; 0x5a; 0xff;  (* LEA (% rbx) (%% (rdx,18446744073709551615)) *)
  0x4c; 0x11; 0xcb;        (* ADC (% rbx) (% r9) *)
  0x48; 0xf7; 0xd1;        (* NOT (% rcx) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x4c; 0x11; 0xda;        (* ADC (% rdx) (% r11) *)
  0x49; 0x0f; 0x43; 0xc0;  (* CMOVAE (% rax) (% r8) *)
  0x49; 0x0f; 0x43; 0xd9;  (* CMOVAE (% rbx) (% r9) *)
  0x49; 0x0f; 0x43; 0xca;  (* CMOVAE (% rcx) (% r10) *)
  0x49; 0x0f; 0x43; 0xd3;  (* CMOVAE (% rdx) (% r11) *)
  0x48; 0x89; 0x44; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rax) *)
  0x48; 0x89; 0x5c; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rbx) *)
  0x48; 0x89; 0x4c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rcx) *)
  0x48; 0x89; 0x54; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rdx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rax) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rax) *)
  0x48; 0xb9; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x04; 0x00;
                           (* MOV (% rcx) (Imm64 (word 1125899906842624)) *)
  0x48; 0x89; 0x4c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% rax) *)
  0x48; 0xc7; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00; 0x0a; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (Imm32 (word 10)) *)
  0x48; 0xc7; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (Imm32 (word 1)) *)
  0xe9; 0x0e; 0x05; 0x00; 0x00;
                           (* JMP (Imm32 (word 1294)) *)
  0x4d; 0x89; 0xc1;        (* MOV (% r9) (% r8) *)
  0x49; 0xc1; 0xf9; 0x3f;  (* SAR (% r9) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xc8;        (* XOR (% r8) (% r9) *)
  0x4d; 0x29; 0xc8;        (* SUB (% r8) (% r9) *)
  0x4d; 0x89; 0xd3;        (* MOV (% r11) (% r10) *)
  0x49; 0xc1; 0xfb; 0x3f;  (* SAR (% r11) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xda;        (* XOR (% r10) (% r11) *)
  0x4d; 0x29; 0xda;        (* SUB (% r10) (% r11) *)
  0x4d; 0x89; 0xe5;        (* MOV (% r13) (% r12) *)
  0x49; 0xc1; 0xfd; 0x3f;  (* SAR (% r13) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x29; 0xec;        (* SUB (% r12) (% r13) *)
  0x4d; 0x89; 0xf7;        (* MOV (% r15) (% r14) *)
  0x49; 0xc1; 0xff; 0x3f;  (* SAR (% r15) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xfe;        (* XOR (% r14) (% r15) *)
  0x4d; 0x29; 0xfe;        (* SUB (% r14) (% r15) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x4c; 0x21; 0xc8;        (* AND (% rax) (% r9) *)
  0x4c; 0x89; 0xd7;        (* MOV (% rdi) (% r10) *)
  0x4c; 0x21; 0xdf;        (* AND (% rdi) (% r11) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x89; 0xbc; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rdi) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x4c; 0x21; 0xe8;        (* AND (% rax) (% r13) *)
  0x4c; 0x89; 0xf6;        (* MOV (% rsi) (% r14) *)
  0x4c; 0x21; 0xfe;        (* AND (% rsi) (% r15) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x89; 0xb4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% rsi) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x0f; 0xac; 0xdf; 0x3b;
                           (* SHRD (% rdi) (% rbx) (Imm8 (word 59)) *)
  0x48; 0x89; 0x3c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rdi) *)
  0x31; 0xff;              (* XOR (% edi) (% edi) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd7;        (* ADC (% rdi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd7;        (* ADC (% rdi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xee; 0x3b;
                           (* SHRD (% rsi) (% rbp) (Imm8 (word 59)) *)
  0x48; 0x89; 0x74; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xcb; 0x3b;
                           (* SHRD (% rbx) (% rcx) (Imm8 (word 59)) *)
  0x48; 0x89; 0x5c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rbx) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x0f; 0xac; 0xfd; 0x3b;
                           (* SHRD (% rbp) (% rdi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x6c; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x48; 0x8b; 0x6c; 0x24; 0x20;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x31; 0xcd;        (* XOR (% rbp) (% r9) *)
  0x4c; 0x21; 0xc5;        (* AND (% rbp) (% r8) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x48; 0x8b; 0x54; 0x24; 0x48;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x31; 0xda;        (* XOR (% rdx) (% r11) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x48; 0x29; 0xd5;        (* SUB (% rbp) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x0f; 0xac; 0xf1; 0x3b;
                           (* SHRD (% rcx) (% rsi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x4c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rcx) *)
  0x48; 0x0f; 0xac; 0xee; 0x3b;
                           (* SHRD (% rsi) (% rbp) (Imm8 (word 59)) *)
  0x48; 0xc1; 0xfd; 0x3b;  (* SAR (% rbp) (Imm8 (word 59)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x89; 0x74; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rsi) *)
  0x48; 0x8b; 0x74; 0x24; 0x20;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x89; 0x6c; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rbp) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x4c; 0x31; 0xee;        (* XOR (% rsi) (% r13) *)
  0x4c; 0x21; 0xe6;        (* AND (% rsi) (% r12) *)
  0x48; 0xf7; 0xde;        (* NEG (% rsi) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x48; 0x8b; 0x54; 0x24; 0x48;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x31; 0xfa;        (* XOR (% rdx) (% r15) *)
  0x4c; 0x21; 0xf2;        (* AND (% rdx) (% r14) *)
  0x48; 0x29; 0xd6;        (* SUB (% rsi) (% rdx) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xdf; 0x3b;
                           (* SHRD (% rdi) (% rbx) (Imm8 (word 59)) *)
  0x48; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rdi) *)
  0x48; 0x0f; 0xac; 0xf3; 0x3b;
                           (* SHRD (% rbx) (% rsi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x5c; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rbx) *)
  0x48; 0xc1; 0xfe; 0x3b;  (* SAR (% rsi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x74; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rsi) *)
  0x48; 0x8b; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0x8b; 0xac; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,168))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x5c; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rbx) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x89; 0x6c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rbp) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x4c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rcx) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x89; 0xb4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rsi) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x5c; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rbx) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x89; 0xac; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x4c; 0x21; 0xc3;        (* AND (% rbx) (% r8) *)
  0x48; 0xf7; 0xdb;        (* NEG (% rbx) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x48; 0x29; 0xd3;        (* SUB (% rbx) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rcx) *)
  0x48; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rdx) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x4c; 0x89; 0xe9;        (* MOV (% rcx) (% r13) *)
  0x4c; 0x21; 0xe1;        (* AND (% rcx) (% r12) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x4c; 0x89; 0xfa;        (* MOV (% rdx) (% r15) *)
  0x4c; 0x21; 0xf2;        (* AND (% rdx) (% r14) *)
  0x48; 0x29; 0xd1;        (* SUB (% rcx) (% rdx) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xca;        (* ADC (% rdx) (% rcx) *)
  0x48; 0x89; 0xb4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% rsi) *)
  0x48; 0x89; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rdx) *)
  0x49; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xe0;
                           (* MOV (% r8) (Imm64 (word 16140901064495857664)) *)
  0x4c; 0x03; 0x44; 0x24; 0x50;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0xc7; 0xc1; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r9) (Imm32 (word 4294967295)) *)
  0x4c; 0x13; 0x4c; 0x24; 0x58;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0xc7; 0xc2; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r10) (Imm32 (word 536870911)) *)
  0x4c; 0x13; 0x54; 0x24; 0x60;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x20;
                           (* MOV (% r11) (Imm64 (word 2305843009213693952)) *)
  0x4c; 0x13; 0x5c; 0x24; 0x68;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0xbc; 0x00; 0x00; 0x00; 0xe0; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r12) (Imm64 (word 2305843008676823040)) *)
  0x4c; 0x13; 0x64; 0x24; 0x70;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0xc1; 0xe8; 0x20;  (* SHR (% r8) (Imm8 (word 32)) *)
  0x49; 0x01; 0xd9;        (* ADD (% r9) (% rbx) *)
  0x4d; 0x11; 0xc2;        (* ADC (% r10) (% r8) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x4c; 0x89; 0x4c; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r9) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0x54; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5c; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r11) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x4c; 0x89; 0x64; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r12) *)
  0x49; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xe0;
                           (* MOV (% r8) (Imm64 (word 16140901064495857664)) *)
  0x4c; 0x03; 0x44; 0x24; 0x78;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0xc7; 0xc1; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r9) (Imm32 (word 4294967295)) *)
  0x4c; 0x13; 0x8c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0xc7; 0xc2; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r10) (Imm32 (word 536870911)) *)
  0x4c; 0x13; 0x94; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x20;
                           (* MOV (% r11) (Imm64 (word 2305843009213693952)) *)
  0x4c; 0x13; 0x9c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0xbc; 0x00; 0x00; 0x00; 0xe0; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r12) (Imm64 (word 2305843008676823040)) *)
  0x4c; 0x13; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0xc1; 0xe8; 0x20;  (* SHR (% r8) (Imm8 (word 32)) *)
  0x49; 0x01; 0xd9;        (* ADD (% r9) (% rbx) *)
  0x4d; 0x11; 0xc2;        (* ADC (% r10) (% r8) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x4c; 0x89; 0x4c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r9) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r11) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x4c; 0x89; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r12) *)
  0x48; 0x8b; 0xb4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0x8b; 0x14; 0x24;  (* MOV (% rdx) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x28;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x89; 0xd3;        (* MOV (% rbx) (% rdx) *)
  0x48; 0x81; 0xe3; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rbx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0xfe; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446741874686296064)) *)
  0x48; 0x09; 0xc3;        (* OR (% rbx) (% rax) *)
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
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0xf7; 0xc1; 0x01; 0x00; 0x00; 0x00;
                           (* TEST (% rcx) (Imm32 (word 1)) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0xb8; 0x00; 0x00; 0x10; 0x00;
                           (* MOV (% eax) (Imm32 (word 1048576)) *)
  0x48; 0x8d; 0x14; 0x03;  (* LEA (% rdx) (%%% (rbx,0,rax)) *)
  0x48; 0x8d; 0x3c; 0x01;  (* LEA (% rdi) (%%% (rcx,0,rax)) *)
  0x48; 0xc1; 0xe2; 0x16;  (* SHL (% rdx) (Imm8 (word 22)) *)
  0x48; 0xc1; 0xe7; 0x16;  (* SHL (% rdi) (Imm8 (word 22)) *)
  0x48; 0xc1; 0xfa; 0x2b;  (* SAR (% rdx) (Imm8 (word 43)) *)
  0x48; 0xc1; 0xff; 0x2b;  (* SAR (% rdi) (Imm8 (word 43)) *)
  0x48; 0xb8; 0x00; 0x00; 0x10; 0x00; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 2199024304128)) *)
  0x48; 0x8d; 0x1c; 0x03;  (* LEA (% rbx) (%%% (rbx,0,rax)) *)
  0x48; 0x8d; 0x0c; 0x01;  (* LEA (% rcx) (%%% (rcx,0,rax)) *)
  0x48; 0xc1; 0xfb; 0x2a;  (* SAR (% rbx) (Imm8 (word 42)) *)
  0x48; 0xc1; 0xf9; 0x2a;  (* SAR (% rcx) (Imm8 (word 42)) *)
  0x48; 0x89; 0x94; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rdx) *)
  0x48; 0x89; 0x9c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% rbx) *)
  0x48; 0x89; 0xbc; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% rdi) *)
  0x48; 0x89; 0x8c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% rcx) *)
  0x4c; 0x8b; 0x24; 0x24;  (* MOV (% r12) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x0f; 0xaf; 0xfc;  (* IMUL (% rdi) (% r12) *)
  0x4c; 0x0f; 0xaf; 0xe2;  (* IMUL (% r12) (% rdx) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x28;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x0f; 0xaf; 0xdd;  (* IMUL (% rbx) (% r13) *)
  0x4c; 0x0f; 0xaf; 0xe9;  (* IMUL (% r13) (% rcx) *)
  0x49; 0x01; 0xdc;        (* ADD (% r12) (% rbx) *)
  0x49; 0x01; 0xfd;        (* ADD (% r13) (% rdi) *)
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
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0xf7; 0xc1; 0x01; 0x00; 0x00; 0x00;
                           (* TEST (% rcx) (Imm32 (word 1)) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
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
  0x4c; 0x8d; 0x3c; 0x03;  (* LEA (% r15) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x1c; 0x01;  (* LEA (% r11) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xff; 0x2a;  (* SAR (% r15) (Imm8 (word 42)) *)
  0x49; 0xc1; 0xfb; 0x2a;  (* SAR (% r11) (Imm8 (word 42)) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x4c; 0x89; 0xe1;        (* MOV (% rcx) (% r12) *)
  0x4d; 0x0f; 0xaf; 0xe0;  (* IMUL (% r12) (% r8) *)
  0x49; 0x0f; 0xaf; 0xdf;  (* IMUL (% rbx) (% r15) *)
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
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x49; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% r8) *)
  0x48; 0x8b; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,208))) *)
  0x49; 0x0f; 0xaf; 0xd7;  (* IMUL (% rdx) (% r15) *)
  0x4c; 0x0f; 0xaf; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* IMUL (% r8) (Memop Quadword (%% (rsp,200))) *)
  0x4c; 0x0f; 0xaf; 0xbc; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* IMUL (% r15) (Memop Quadword (%% (rsp,216))) *)
  0x4d; 0x01; 0xc7;        (* ADD (% r15) (% r8) *)
  0x4c; 0x8d; 0x0c; 0x10;  (* LEA (% r9) (%%% (rax,0,rdx)) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x49; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% r10) *)
  0x48; 0x8b; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,208))) *)
  0x49; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% r11) *)
  0x4c; 0x0f; 0xaf; 0x94; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* IMUL (% r10) (Memop Quadword (%% (rsp,200))) *)
  0x4c; 0x0f; 0xaf; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* IMUL (% r11) (Memop Quadword (%% (rsp,216))) *)
  0x4d; 0x01; 0xd3;        (* ADD (% r11) (% r10) *)
  0x4c; 0x8d; 0x2c; 0x10;  (* LEA (% r13) (%%% (rax,0,rdx)) *)
  0x48; 0xc7; 0xc0; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294967294)) *)
  0xba; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 2)) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0xf7; 0xc1; 0x01; 0x00; 0x00; 0x00;
                           (* TEST (% rcx) (Imm32 (word 1)) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0xb8; 0x00; 0x00; 0x10; 0x00;
                           (* MOV (% eax) (Imm32 (word 1048576)) *)
  0x4c; 0x8d; 0x04; 0x03;  (* LEA (% r8) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x24; 0x01;  (* LEA (% r12) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xe0; 0x15;  (* SHL (% r8) (Imm8 (word 21)) *)
  0x49; 0xc1; 0xe4; 0x15;  (* SHL (% r12) (Imm8 (word 21)) *)
  0x49; 0xc1; 0xf8; 0x2b;  (* SAR (% r8) (Imm8 (word 43)) *)
  0x49; 0xc1; 0xfc; 0x2b;  (* SAR (% r12) (Imm8 (word 43)) *)
  0x48; 0xb8; 0x00; 0x00; 0x10; 0x00; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 2199024304128)) *)
  0x4c; 0x8d; 0x14; 0x03;  (* LEA (% r10) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x34; 0x01;  (* LEA (% r14) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xfa; 0x2b;  (* SAR (% r10) (Imm8 (word 43)) *)
  0x49; 0xc1; 0xfe; 0x2b;  (* SAR (% r14) (Imm8 (word 43)) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x49; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% r8) *)
  0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
  0x49; 0x0f; 0xaf; 0xd2;  (* IMUL (% rdx) (% r10) *)
  0x4d; 0x0f; 0xaf; 0xc7;  (* IMUL (% r8) (% r15) *)
  0x4d; 0x0f; 0xaf; 0xd3;  (* IMUL (% r10) (% r11) *)
  0x4d; 0x01; 0xc2;        (* ADD (% r10) (% r8) *)
  0x4c; 0x8d; 0x04; 0x10;  (* LEA (% r8) (%%% (rax,0,rdx)) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x49; 0x0f; 0xaf; 0xc4;  (* IMUL (% rax) (% r12) *)
  0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
  0x49; 0x0f; 0xaf; 0xd6;  (* IMUL (% rdx) (% r14) *)
  0x4d; 0x0f; 0xaf; 0xe7;  (* IMUL (% r12) (% r15) *)
  0x4d; 0x0f; 0xaf; 0xf3;  (* IMUL (% r14) (% r11) *)
  0x4d; 0x01; 0xe6;        (* ADD (% r14) (% r12) *)
  0x4c; 0x8d; 0x24; 0x10;  (* LEA (% r12) (%%% (rax,0,rdx)) *)
  0x48; 0x89; 0xb4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% rsi) *)
  0x48; 0xff; 0x8c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* DEC (Memop Quadword (%% (rsp,176))) *)
  0x0f; 0x85; 0xba; 0xed; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294962618)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x28;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% r8) *)
  0x49; 0x0f; 0xaf; 0xca;  (* IMUL (% rcx) (% r10) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x48; 0xc1; 0xf8; 0x3f;  (* SAR (% rax) (Imm8 (word 63)) *)
  0x4d; 0x89; 0xc1;        (* MOV (% r9) (% r8) *)
  0x49; 0xc1; 0xf9; 0x3f;  (* SAR (% r9) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xc8;        (* XOR (% r8) (% r9) *)
  0x4d; 0x29; 0xc8;        (* SUB (% r8) (% r9) *)
  0x49; 0x31; 0xc1;        (* XOR (% r9) (% rax) *)
  0x4d; 0x89; 0xd3;        (* MOV (% r11) (% r10) *)
  0x49; 0xc1; 0xfb; 0x3f;  (* SAR (% r11) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xda;        (* XOR (% r10) (% r11) *)
  0x4d; 0x29; 0xda;        (* SUB (% r10) (% r11) *)
  0x49; 0x31; 0xc3;        (* XOR (% r11) (% rax) *)
  0x4d; 0x89; 0xe5;        (* MOV (% r13) (% r12) *)
  0x49; 0xc1; 0xfd; 0x3f;  (* SAR (% r13) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x29; 0xec;        (* SUB (% r12) (% r13) *)
  0x49; 0x31; 0xc5;        (* XOR (% r13) (% rax) *)
  0x4d; 0x89; 0xf7;        (* MOV (% r15) (% r14) *)
  0x49; 0xc1; 0xff; 0x3f;  (* SAR (% r15) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xfe;        (* XOR (% r14) (% r15) *)
  0x4d; 0x29; 0xfe;        (* SUB (% r14) (% r15) *)
  0x49; 0x31; 0xc7;        (* XOR (% r15) (% rax) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x4c; 0x21; 0xc8;        (* AND (% rax) (% r9) *)
  0x4d; 0x89; 0xd4;        (* MOV (% r12) (% r10) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x49; 0x29; 0xd1;        (* SUB (% r9) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x64; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r15) *)
  0x4c; 0x89; 0x4c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r9) *)
  0x49; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xe0;
                           (* MOV (% r8) (Imm64 (word 16140901064495857664)) *)
  0x4c; 0x03; 0x44; 0x24; 0x50;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0xc7; 0xc1; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r9) (Imm32 (word 4294967295)) *)
  0x4c; 0x13; 0x4c; 0x24; 0x58;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0xc7; 0xc2; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r10) (Imm32 (word 536870911)) *)
  0x4c; 0x13; 0x54; 0x24; 0x60;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x20;
                           (* MOV (% r11) (Imm64 (word 2305843009213693952)) *)
  0x4c; 0x13; 0x5c; 0x24; 0x68;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0xbc; 0x00; 0x00; 0x00; 0xe0; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r12) (Imm64 (word 2305843008676823040)) *)
  0x4c; 0x13; 0x64; 0x24; 0x70;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x48; 0xc1; 0xe3; 0x20;  (* SHL (% rbx) (Imm8 (word 32)) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0xc1; 0xe8; 0x20;  (* SHR (% r8) (Imm8 (word 32)) *)
  0x49; 0x01; 0xd9;        (* ADD (% r9) (% rbx) *)
  0x4d; 0x11; 0xc2;        (* ADC (% r10) (% r8) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x4c; 0x89; 0x4c; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r9) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0x54; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5c; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r11) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x4c; 0x89; 0x64; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r12) *)
  0x4c; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x58;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x60;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x68;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,104))) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0x48; 0x8d; 0x48; 0xfe;  (* LEA (% rcx) (%% (rax,18446744073709551614)) *)
  0x48; 0x8d; 0x53; 0xff;  (* LEA (% rdx) (%% (rbx,18446744073709551615)) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x4c; 0x11; 0xcb;        (* ADC (% rbx) (% r9) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x11; 0xda;        (* ADC (% rdx) (% r11) *)
  0x49; 0x0f; 0x43; 0xc0;  (* CMOVAE (% rax) (% r8) *)
  0x49; 0x0f; 0x43; 0xd9;  (* CMOVAE (% rbx) (% r9) *)
  0x49; 0x0f; 0x43; 0xca;  (* CMOVAE (% rcx) (% r10) *)
  0x49; 0x0f; 0x43; 0xd3;  (* CMOVAE (% rdx) (% r11) *)
  0x48; 0x8b; 0xbc; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,224))) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x89; 0x5f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rbx) *)
  0x48; 0x89; 0x4f; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rcx) *)
  0x48; 0x89; 0x57; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rdx) *)
  0x48; 0x81; 0xc4; 0xf0; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 240)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x11;        (* MOV (% rdx) (Memop Quadword (%% (rcx,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0e;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x66; 0x18;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4d; 0x11; 0xec;        (* ADC (% r12) (% r13) *)
  0x48; 0x8b; 0x51; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rcx,8))) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4d; 0x11; 0xf5;        (* ADC (% r13) (% r14) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xef;
                           (* ADCX (% r13) (% r15) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf7;
                           (* ADOX (% r14) (% r15) *)
  0x4d; 0x11; 0xfe;        (* ADC (% r14) (% r15) *)
  0x48; 0x8b; 0x51; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rcx,16))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
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
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x48; 0x8b; 0x51; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rcx,24))) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
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
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% r9) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4d; 0x0f; 0x42; 0xf1;  (* CMOVB (% r14) (% r9) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x27;        (* MOV (Memop Quadword (%% (rdi,0))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r13) *)
  0x4c; 0x89; 0x77; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r15) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% r8) (% rdx,% rdx) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0x66; 0x18;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0x62; 0x93; 0xf6; 0x76; 0x18;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
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
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% rbp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADOX (% r14) (% rbp) *)
  0x49; 0x11; 0xee;        (* ADC (% r14) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xcf;
                           (* ADOX (% r9) (% r15) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
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
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
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
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADCX (% r15) (% rbp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADOX (% r15) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% rbp) *)
  0x41; 0x89; 0xe9;        (* MOV (% r9d) (% ebp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADOX (% r9) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADCX (% r9) (% rbp) *)
  0x4d; 0x01; 0xce;        (* ADD (% r14) (% r9) *)
  0x49; 0x11; 0xef;        (* ADC (% r15) (% rbp) *)
  0x41; 0x89; 0xe8;        (* MOV (% r8d) (% ebp) *)
  0x49; 0x11; 0xe8;        (* ADC (% r8) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADCX (% r15) (% rbp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADOX (% r8) (% rbp) *)
  0x49; 0x11; 0xe8;        (* ADC (% r8) (% rbp) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0x8d; 0x52; 0xff;  (* LEA (% rdx) (%% (rdx,18446744073709551615)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x48; 0x8d; 0x6d; 0xff;  (* LEA (% rbp) (%% (rbp,18446744073709551615)) *)
  0x48; 0x89; 0xe8;        (* MOV (% rax) (% rbp) *)
  0x4c; 0x11; 0xf5;        (* ADC (% rbp) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf5;  (* CMOVB (% r14) (% rbp) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x27;        (* MOV (Memop Quadword (%% (rdi,0))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r13) *)
  0x4c; 0x89; 0x77; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r15) *)
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
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xc0; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 192)) *)
  0x48; 0x89; 0xd5;        (* MOV (% rbp) (% rdx) *)
  0x48; 0x8b; 0x56; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rsi,64))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% r8) (% rdx,% rdx) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x56; 0x48;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0x66; 0x58;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x48; 0x8b; 0x56; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rsi,80))) *)
  0xc4; 0x62; 0x93; 0xf6; 0x76; 0x58;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x48; 0x8b; 0x56; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rsi,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xcf;
                           (* ADOX (% r9) (% r15) *)
  0x48; 0x8b; 0x56; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rsi,72))) *)
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
  0x48; 0x8b; 0x56; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rsi,80))) *)
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
  0x48; 0x8b; 0x56; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rsi,88))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x41; 0x89; 0xc9;        (* MOV (% r9d) (% ecx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% rcx) *)
  0x4d; 0x01; 0xce;        (* ADD (% r14) (% r9) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x41; 0x89; 0xc8;        (* MOV (% r8d) (% ecx) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% rcx) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x41; 0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 1)) *)
  0x48; 0x8d; 0x52; 0xff;  (* LEA (% rdx) (%% (rdx,18446744073709551615)) *)
  0x48; 0x8d; 0x41; 0xff;  (* LEA (% rax) (%% (rcx,18446744073709551615)) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4c; 0x0f; 0x44; 0xc1;  (* CMOVE (% r8) (% rcx) *)
  0x48; 0x0f; 0x44; 0xd1;  (* CMOVE (% rdx) (% rcx) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x4c; 0x0f; 0x44; 0xd9;  (* CMOVE (% r11) (% rcx) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x4c; 0x89; 0x24; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r15) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x55; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rbp,32))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4e; 0x40;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x56; 0x48;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x5e; 0x50;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x66; 0x58;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4d; 0x11; 0xec;        (* ADC (% r12) (% r13) *)
  0x48; 0x8b; 0x55; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rbp,40))) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x58;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4d; 0x11; 0xf5;        (* ADC (% r13) (% r14) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xef;
                           (* ADCX (% r13) (% r15) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf7;
                           (* ADOX (% r14) (% r15) *)
  0x4d; 0x11; 0xfe;        (* ADC (% r14) (% r15) *)
  0x48; 0x8b; 0x55; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rbp,48))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x58;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x48; 0x8b; 0x55; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rbp,56))) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x58;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% r9) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
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
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x55; 0x00;  (* MOV (% rdx) (Memop Quadword (%% (rbp,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0c; 0x24;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x54; 0x24; 0x08;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x64; 0x24; 0x18;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4d; 0x11; 0xec;        (* ADC (% r12) (% r13) *)
  0x48; 0x8b; 0x55; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rbp,8))) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4d; 0x11; 0xf5;        (* ADC (% r13) (% r14) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xef;
                           (* ADCX (% r13) (% r15) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf7;
                           (* ADOX (% r14) (% r15) *)
  0x4d; 0x11; 0xfe;        (* ADC (% r14) (% r15) *)
  0x48; 0x8b; 0x55; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rbp,16))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x48; 0x8b; 0x55; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rbp,24))) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% r9) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
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
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x54; 0x24; 0x20;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,32))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0c; 0x24;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x54; 0x24; 0x08;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x64; 0x24; 0x18;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4d; 0x11; 0xec;        (* ADC (% r12) (% r13) *)
  0x48; 0x8b; 0x54; 0x24; 0x28;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,40))) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4d; 0x11; 0xf5;        (* ADC (% r13) (% r14) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xef;
                           (* ADCX (% r13) (% r15) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf7;
                           (* ADOX (% r14) (% r15) *)
  0x4d; 0x11; 0xfe;        (* ADC (% r14) (% r15) *)
  0x48; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,48))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x48; 0x8b; 0x54; 0x24; 0x38;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,56))) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% r9) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x2b; 0x06;        (* SUB (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x1b; 0x4e; 0x08;  (* SBB (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x1b; 0x46; 0x10;  (* SBB (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x58;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x1b; 0x4e; 0x18;  (* SBB (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x8c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r9) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x2b; 0x46; 0x20;  (* SUB (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x28;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x1b; 0x4e; 0x28;  (* SBB (% rcx) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x1b; 0x46; 0x30;  (* SBB (% r8) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x38;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x1b; 0x4e; 0x38;  (* SBB (% r9) (Memop Quadword (%% (rsi,56))) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r9) *)
  0x48; 0x8b; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,160))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% r8) (% rdx,% rdx) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x48; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,176))) *)
  0xc4; 0x62; 0x93; 0xf6; 0xb4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,184))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xcf;
                           (* ADOX (% r9) (% r15) *)
  0x48; 0x8b; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,168))) *)
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
  0x48; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,176))) *)
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
  0x48; 0x8b; 0x94; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,184))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x41; 0x89; 0xc9;        (* MOV (% r9d) (% ecx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% rcx) *)
  0x4d; 0x01; 0xce;        (* ADD (% r14) (% r9) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x41; 0x89; 0xc8;        (* MOV (% r8d) (% ecx) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% rcx) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x41; 0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 1)) *)
  0x48; 0x8d; 0x52; 0xff;  (* LEA (% rdx) (%% (rdx,18446744073709551615)) *)
  0x48; 0x8d; 0x41; 0xff;  (* LEA (% rax) (%% (rcx,18446744073709551615)) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4c; 0x0f; 0x44; 0xc1;  (* CMOVE (% r8) (% rcx) *)
  0x48; 0x0f; 0x44; 0xd1;  (* CMOVE (% rdx) (% rcx) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x4c; 0x0f; 0x44; 0xd9;  (* CMOVE (% r11) (% rcx) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r15) *)
  0x48; 0x8b; 0x54; 0x24; 0x20;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,32))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% r8) (% rdx,% rdx) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x54; 0x24; 0x28;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0x64; 0x24; 0x38;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,48))) *)
  0xc4; 0x62; 0x93; 0xf6; 0x74; 0x24; 0x38;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x48; 0x8b; 0x54; 0x24; 0x38;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xcf;
                           (* ADOX (% r9) (% r15) *)
  0x48; 0x8b; 0x54; 0x24; 0x28;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,40))) *)
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
  0x48; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,48))) *)
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
  0x48; 0x8b; 0x54; 0x24; 0x38;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,56))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x41; 0x89; 0xc9;        (* MOV (% r9d) (% ecx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% rcx) *)
  0x4d; 0x01; 0xce;        (* ADD (% r14) (% r9) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x41; 0x89; 0xc8;        (* MOV (% r8d) (% ecx) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% rcx) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0xbb; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe3;        (* ADD (% rbx) (% r12) *)
  0x48; 0x8d; 0x52; 0xff;  (* LEA (% rdx) (%% (rdx,18446744073709551615)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x48; 0x8d; 0x49; 0xff;  (* LEA (% rcx) (%% (rcx,18446744073709551615)) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x4c; 0x11; 0xf1;        (* ADC (% rcx) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe3;  (* CMOVB (% r12) (% rbx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf1;  (* CMOVB (% r14) (% rcx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x24; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r15) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4c; 0x24; 0x60;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x54; 0x24; 0x68;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x64; 0x24; 0x78;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4d; 0x11; 0xec;        (* ADC (% r12) (% r13) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4d; 0x11; 0xf5;        (* ADC (% r13) (% r14) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xef;
                           (* ADCX (% r13) (% r15) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf7;
                           (* ADOX (% r14) (% r15) *)
  0x4d; 0x11; 0xfe;        (* ADC (% r14) (% r15) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% r9) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
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
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x54; 0x24; 0x40;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,64))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4c; 0x24; 0x60;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x54; 0x24; 0x68;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x64; 0x24; 0x78;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4d; 0x11; 0xec;        (* ADC (% r12) (% r13) *)
  0x48; 0x8b; 0x54; 0x24; 0x48;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,72))) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4d; 0x11; 0xf5;        (* ADC (% r13) (% r14) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xef;
                           (* ADCX (% r13) (% r15) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf7;
                           (* ADOX (% r14) (% r15) *)
  0x4d; 0x11; 0xfe;        (* ADC (% r14) (% r15) *)
  0x48; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,80))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x48; 0x8b; 0x54; 0x24; 0x58;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,88))) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% r9) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
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
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x2b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x1b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x1b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x18;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,152))) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r9) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x2b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x1b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x1b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x58;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,152))) *)
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
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x56; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rsi,64))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4d; 0x11; 0xec;        (* ADC (% r12) (% r13) *)
  0x48; 0x8b; 0x56; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rsi,72))) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4d; 0x11; 0xf5;        (* ADC (% r13) (% r14) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xef;
                           (* ADCX (% r13) (% r15) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf7;
                           (* ADOX (% r14) (% r15) *)
  0x4d; 0x11; 0xfe;        (* ADC (% r14) (% r15) *)
  0x48; 0x8b; 0x56; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rsi,80))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x48; 0x8b; 0x56; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rsi,88))) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% r9) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
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
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x2b; 0x44; 0x24; 0x40;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x1b; 0x4c; 0x24; 0x48;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x50;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x18;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x58;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,88))) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x2b; 0x04; 0x24;  (* SUB (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x1b; 0x4c; 0x24; 0x08;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x10;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x18;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r9) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x56; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rsi,32))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4c; 0x24; 0x60;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x54; 0x24; 0x68;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x64; 0x24; 0x78;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4d; 0x11; 0xec;        (* ADC (% r12) (% r13) *)
  0x48; 0x8b; 0x56; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rsi,40))) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4d; 0x11; 0xf5;        (* ADC (% r13) (% r14) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xef;
                           (* ADCX (% r13) (% r15) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf7;
                           (* ADOX (% r14) (% r15) *)
  0x4d; 0x11; 0xfe;        (* ADC (% r14) (% r15) *)
  0x48; 0x8b; 0x56; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rsi,48))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x48; 0x8b; 0x56; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rsi,56))) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% r9) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
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
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,128))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4c; 0x24; 0x20;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,32))) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x54; 0x24; 0x28;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x5c; 0x24; 0x30;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsp,48))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x64; 0x24; 0x38;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x4d; 0x11; 0xec;        (* ADC (% r12) (% r13) *)
  0x48; 0x8b; 0x94; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,136))) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4d; 0x11; 0xf5;        (* ADC (% r13) (% r14) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% rbx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xd9;
                           (* MULX4 (% rbx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xef;
                           (* ADCX (% r13) (% r15) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf7;
                           (* ADOX (% r14) (% r15) *)
  0x4d; 0x11; 0xfe;        (* ADC (% r14) (% r15) *)
  0x48; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,144))) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x4d; 0x11; 0xc7;        (* ADC (% r15) (% r8) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x8d; 0x52; 0x02;  (* LEA (% rdx) (%% (rdx,2)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdb;
                           (* MULX4 (% rbx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% r9) *)
  0x4d; 0x11; 0xc8;        (* ADC (% r8) (% r9) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4d; 0x11; 0xf1;        (* ADC (% r9) (% r14) *)
  0x41; 0xbb; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967294)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
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
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x2b; 0x44; 0x24; 0x60;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x1b; 0x4c; 0x24; 0x68;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x70;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x78;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,120))) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x29; 0xd2;        (* SUB (% rdx) (% r10) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r9) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x8b; 0x56; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0x0b; 0x46; 0x50;  (* OR (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0x0b; 0x56; 0x58;  (* OR (% rdx) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0x09; 0xd0;        (* OR (% rax) (% rdx) *)
  0x4c; 0x8b; 0x04; 0x24;  (* MOV (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x45; 0x00;  (* MOV (% rax) (Memop Quadword (%% (rbp,0))) *)
  0x4c; 0x0f; 0x44; 0xc0;  (* CMOVE (% r8) (% rax) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x8b; 0x45; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rbp,8))) *)
  0x4c; 0x0f; 0x44; 0xc8;  (* CMOVE (% r9) (% rax) *)
  0x4c; 0x8b; 0x54; 0x24; 0x10;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x8b; 0x45; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rbp,16))) *)
  0x4c; 0x0f; 0x44; 0xd0;  (* CMOVE (% r10) (% rax) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x18;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x8b; 0x45; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rbp,24))) *)
  0x4c; 0x0f; 0x44; 0xd8;  (* CMOVE (% r11) (% rax) *)
  0x4c; 0x8b; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x8b; 0x45; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xe0;  (* CMOVE (% r12) (% rax) *)
  0x4c; 0x8b; 0xac; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x8b; 0x45; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xe8;  (* CMOVE (% r13) (% rax) *)
  0x4c; 0x8b; 0xb4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0x8b; 0x45; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xf0;  (* CMOVE (% r14) (% rax) *)
  0x4c; 0x8b; 0xbc; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x8b; 0x45; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xf8;  (* CMOVE (% r15) (% rax) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0x4c; 0x89; 0x77; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r15) *)
  0x4c; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,176))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,184))) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x4c; 0x0f; 0x44; 0xc0;  (* CMOVE (% r8) (% rax) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584320)) *)
  0x4c; 0x0f; 0x44; 0xc8;  (* CMOVE (% r9) (% rax) *)
  0x48; 0xc7; 0xc0; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294967295)) *)
  0x4c; 0x0f; 0x44; 0xd0;  (* CMOVE (% r10) (% rax) *)
  0xb8; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% eax) (Imm32 (word 4294967294)) *)
  0x4c; 0x0f; 0x44; 0xd8;  (* CMOVE (% r11) (% rax) *)
  0x4c; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% r9) *)
  0x4c; 0x89; 0x57; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r11) *)
  0x48; 0x81; 0xc4; 0xc0; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 192)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let p256_scalarmulbase_tmc = define_trimmed "p256_scalarmulbase_tmc" p256_scalarmulbase_mc;;

let P256_SCALARMULBASE_EXEC = X86_MK_EXEC_RULE p256_scalarmulbase_tmc;;

(* ------------------------------------------------------------------------- *)
(* Local versions of the subroutines.                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_DEMONT_TAC =
  let baseth = X86_SIMD_SHARPEN_RULE BIGNUM_DEMONT_P256_NOIBT_SUBROUTINE_CORRECT
  (X86_PROMOTE_RETURN_STACK_TAC
    bignum_demont_p256_tmc BIGNUM_DEMONT_P256_CORRECT `[RBX]` 8) in
  X86_SUBROUTINE_SIM_TAC
   (p256_scalarmulbase_tmc,P256_SCALARMULBASE_EXEC,
    0x441,bignum_demont_p256_tmc,baseth)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 4)) s`;
   `pc + 0x441`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`];;

let LOCAL_INV_TAC =
  let baseth = X86_SIMD_SHARPEN_RULE BIGNUM_INV_P256_NOIBT_SUBROUTINE_CORRECT
  (X86_PROMOTE_RETURN_STACK_TAC bignum_inv_p256_tmc
     BIGNUM_INV_P256_CORRECT
      `[RBX; RBP; R12; R13; R14; R15]` 288) in
  X86_SUBROUTINE_SIM_TAC
   (p256_scalarmulbase_tmc,P256_SCALARMULBASE_EXEC,
    0x533,bignum_inv_p256_tmc,baseth)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 4)) s`;
   `pc + 0x533`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`];;

let LOCAL_MUL_TAC =
  let baseth = X86_SIMD_SHARPEN_RULE BIGNUM_MONTMUL_P256_NOIBT_SUBROUTINE_CORRECT
  (X86_PROMOTE_RETURN_STACK_TAC
   bignum_montmul_p256_tmc BIGNUM_MONTMUL_P256_CORRECT
   `[RBX; R12; R13; R14; R15]` 40) in
  X86_SUBROUTINE_SIM_TAC
   (p256_scalarmulbase_tmc,P256_SCALARMULBASE_EXEC,
    0x1aa2,bignum_montmul_p256_tmc,
    baseth)
  [`read RDI s`; `read RSI s`; `read RDX s`;
   `read(memory :> bytes(read RSI s,8 * 4)) s`;
   `read(memory :> bytes(read RDX s,8 * 4)) s`;
   `pc + 0x1aa2`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`];;

let LOCAL_SQR_TAC =
  let baseth = X86_SIMD_SHARPEN_RULE BIGNUM_MONTSQR_P256_NOIBT_SUBROUTINE_CORRECT
  (X86_PROMOTE_RETURN_STACK_TAC
   bignum_montsqr_p256_tmc BIGNUM_MONTSQR_P256_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 48) in
  X86_SUBROUTINE_SIM_TAC
   (p256_scalarmulbase_tmc,P256_SCALARMULBASE_EXEC,
    0x1ce4,bignum_montsqr_p256_tmc,
    baseth)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 4)) s`;
   `pc + 0x1ce4`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`];;

let LOCAL_JMIXADD_TAC =
  let baseth = X86_SIMD_SHARPEN_RULE P256_MONTJMIXADD_NOIBT_SUBROUTINE_CORRECT
  (X86_PROMOTE_RETURN_STACK_TAC p256_montjmixadd_tmc P256_MONTJMIXADD_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 240) in
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_pair_from_memory]
       baseth) in
  X86_SUBROUTINE_SIM_TAC
   (p256_scalarmulbase_tmc,P256_SCALARMULBASE_EXEC,
    0x1efa,p256_montjmixadd_tmc,th)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 64),8 * 4)) s`;
   `read RDX s`;
   `read(memory :> bytes(read RDX s,8 * 4)) s,
    read(memory :> bytes(word_add (read RDX s) (word 32),8 * 4)) s`;
   `pc + 0x1efa`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`];;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let affinepointz_p256 = new_definition
 `affinepointz_p256 (x,y) P <=>
        if x = 0 /\ y = 0 then P = NONE
        else P = SOME(paired (modular_decode (256,p_256)) (x,y))`;;

let REPRESENTS2_P256_NONZERO = prove
 (`!P x y. represents2_p256 P (x,y) ==> ~(P = group_id p256_group)`,
  REWRITE_TAC[represents2_p256; P256_GROUP] THEN MESON_TAC[option_DISTINCT]);;

let REPRESENTS_P256_2 = prove
 (`!P x y. represents_p256 P (x,y,(2 EXP 256) MOD p_256) <=>
           represents2_p256 P (x,y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[represents2_p256; represents_p256] THEN
  REWRITE_TAC[paired; tripled; weierstrass_of_jacobian] THEN
  REWRITE_TAC[montgomery_decode; INTEGER_MOD_RING_CLAUSES; p_256] THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INVERSE_MOD_CONV)) THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[ring_div; RING_INV_INTEGER_MOD_RING;
              INTEGER_MOD_RING_CLAUSES; COPRIME_1] THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INVERSE_MOD_CONV)) THEN
  REWRITE_TAC[INT_MUL_RID] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[]);;

let REPRESENTS_P256_NEGATION = prove
 (`!P x y z.
        represents_p256 P (x,y,z)
        ==> P IN group_carrier p256_group /\ ~(P = group_id p256_group)
            ==> represents_p256 (group_inv p256_group P) (x,p_256 - y,z)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; P256_GROUP] THEN
  REWRITE_TAC[IN; option_DISTINCT] THEN REWRITE_TAC[weierstrass_curve] THEN
  REWRITE_TAC[represents_p256; weierstrass_of_jacobian; tripled] THEN
  MAP_EVERY X_GEN_TAC [`X:int`; `Y:int`; `x:num`; `y:num`; `z:num`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  POP_ASSUM(K ALL_TAC) THEN
  REWRITE_TAC[montgomery_decode; option_INJ; PAIR_EQ; weierstrass_neg] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  REWRITE_TAC[INT_ARITH `a + --(&3) * b + c:int = a - &3 * b + c`] THEN
  ONCE_REWRITE_TAC[INT_CONG_SYM] THEN
  ASM_CASES_TAC `Y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[NO_ROOTS_P256];
    ALL_TAC] THEN
  ASM_CASES_TAC `y = 0` THENL
   [ASM_REWRITE_TAC[ring_div; RING_INV_INTEGER_MOD_RING; INT_OF_NUM_CLAUSES;
                    INT_OF_NUM_REM; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[MULT_CLAUSES; p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[INT_MUL_LZERO; INT_REM_ZERO];
    ALL_TAC] THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o SYM)) THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ring_div]] THEN
  REWRITE_TAC[RING_INV_INTEGER_MOD_RING; INT_OF_NUM_CLAUSES;
              INT_OF_NUM_REM; INTEGER_MOD_RING_CLAUSES] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO; INT_NEG_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  REWRITE_TAC[INTEGER_RULE
   `((i * (p - y)) * j:int == --((i * y) * j)) (mod p)`]);;

let REPRESENTS_P256_Y_NONZERO = prove
 (`!P x y z.
        represents_p256 P (x,y,z)
        ==> P IN group_carrier p256_group /\ ~(z = 0)
            ==> ~(y = 0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS_P256_NEGATION) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [represents_p256]) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[montgomery_decode; tripled; weierstrass_of_jacobian] THEN
  REWRITE_TAC[represents_p256; SUB_0; LT_REFL; P256_GROUP] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; INT_REM_EQ_0] THEN
  MATCH_MP_TAC(MESON[]
   `~(x = y) /\ ~p ==> (if p then x else y) = a ==> ~(a = x)`) THEN
  REWRITE_TAC[option_DISTINCT; GSYM INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(MP_TAC o SPEC `(&2:int) pow 256` o MATCH_MP (INTEGER_RULE
    `p divides i * z ==> !q:int. (q * i == &1) (mod p) ==> p divides z`)) THEN
  REWRITE_TAC[GSYM num_divides; INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2; NOT_IMP] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  MP_TAC p_256 THEN ASM_ARITH_TAC);;

let REPRESENTS2_P256_NEGATION = prove
 (`!P x y.
        represents2_p256 P (x,y)
        ==> P IN group_carrier p256_group
            ==> represents2_p256 (group_inv p256_group P) (x,p_256 - y)`,
  MESON_TAC[REPRESENTS2_P256_NONZERO; REPRESENTS_P256_2;
                REPRESENTS_P256_NEGATION]);;

let unilemma0 = prove
 (`x = a MOD p_256 ==> x < p_256 /\ &x = &a rem &p_256`,
  REWRITE_TAC[INT_OF_NUM_REM; p_256] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_256 ==> x < p_256 /\ &x = a rem &p_256`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_256] THEN INT_ARITH_TAC);;

let fdivlemma = prove
  (`!f a b c:A.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ c IN ring_carrier f /\
        ~(b = ring_0 f) /\
        ring_mul f b c = a
        ==> ring_div f a b = c`,
  FIELD_TAC);;

(* ------------------------------------------------------------------------- *)
(* Conveniently encoding tabulation in terms of specific byte array.         *)
(* ------------------------------------------------------------------------- *)

let p256_tabulates =
  let lemma = prove
   (`read (memory :> bytes(base,len)) s = read (memory :> bytes(base,len)) s'
     ==> m + n <= len
         ==> read (memory :> bytes(word_add base (word n),m)) s =
             read (memory :> bytes(word_add base (word n),m)) s'`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM
      `\x. x DIV 2 EXP (8 * n) MOD (2 EXP (8 * m))`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
    ASM_SIMP_TAC[ARITH_RULE `m + n <= len ==> MIN (len - n) m = m`]) in
  let eth = prove
   (`?f. !P blocksize table len s.
        f P blocksize table len (read (memory :> bytes(table,len)) s) <=>
        (256 DIV blocksize + 1) * 2 EXP (blocksize - 1) * 64 <= len /\
        !i. i <= 256 DIV blocksize
            ==> !j. 1 <= j /\ j <= 2 EXP (blocksize - 1)
                    ==> represents2_p256
                         (group_pow p256_group P (2 EXP (blocksize * i) * j))
                         (bignum_pair_from_memory
                           (word_add table
                         (word (64 * ((2 EXP (blocksize - 1) * i + j - 1)))),4)
                          s)`,
    REWRITE_TAC[GSYM SKOLEM_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC
     `(256 DIV blocksize + 1) * 2 EXP (blocksize - 1) * 64 <= len` THEN
    ASM_REWRITE_TAC[] THENL
     [ONCE_REWRITE_TAC[EQ_SYM_EQ];
      EXISTS_TAC `\x:num. F` THEN REWRITE_TAC[]] THEN
    GEN_REWRITE_TAC I
     [GSYM(REWRITE_RULE[FUN_EQ_THM; o_THM] FUNCTION_FACTORS_LEFT)] THEN
    MAP_EVERY X_GEN_TAC [`s':x86state`; `s:x86state`] THEN DISCH_TAC THEN
    REPEAT(MATCH_MP_TAC(MESON[]
            `(!x. P x ==> (Q x <=> R x))
             ==> ((!x. P x ==> Q x) <=> (!x. P x ==> R x))`) THEN
           GEN_TAC THEN DISCH_TAC) THEN
    AP_TERM_TAC THEN REWRITE_TAC[bignum_pair_from_memory; PAIR_EQ] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN CONJ_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP lemma) THEN
    REWRITE_TAC[ARITH_RULE `8 * 4 + x + 8 * 4 = 8 * 8 + x`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `a * b * 64 <= len
      ==> x <= 64 /\ y < b * a ==> x + 64 * y <= len`)) THEN
    (CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `1 <= j /\ j <= b
      ==> b * (i + 1) <= b * k ==> b * i + j - 1 < b * k`)) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC) in
  new_specification ["p256_tabulates"] eth;;

let P256_SCALARMULBASE_CORRECT = time prove
 (`!res scalar blocksize tab n len tabulation pc stackpointer.
        2 <= val blocksize /\ val blocksize <= 31 /\
        ALL (nonoverlapping (stackpointer,648))
            [(word pc,0x3bae); (res,64); (scalar,32); (tab,len)] /\
        nonoverlapping (res,64) (word pc,0x3bae)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p256_scalarmulbase_tmc /\
                  read RIP s = word(pc + 0x11) /\
                  read RSP s = word_add stackpointer (word 296) /\
                  C_ARGUMENTS [res;scalar;blocksize;tab] s /\
                  bignum_from_memory (scalar,4) s = n /\
                  read (memory :> bytes(tab,len)) s = tabulation)
             (\s. read RIP s = word (pc + 0x42f) /\
                  !P. P IN group_carrier p256_group /\
                      p256_tabulates P (val blocksize) tab len tabulation
                      ==> affinepointz_p256
                           (bignum_pair_from_memory(res,4) s)
                           (group_pow p256_group P n))
          (MAYCHANGE [RIP] ,,
           MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
           MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
           MAYCHANGE [RBX; RBP; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(res,64);
                      memory :> bytes(stackpointer,648)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[GSYM SEQ_ASSOC; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAP_EVERY X_GEN_TAC [`res:int64`; `scalar:int64`] THEN
  W64_GEN_TAC `blocksize:num` THEN
  MAP_EVERY X_GEN_TAC
   [`tab:int64`; `n_input:num`; `len:num`; `tabulation:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_pair_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `b <= 31 ==> b < 64`)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN

  SUBGOAL_THEN `val(word blocksize:int64) = blocksize` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `blocksize < 64` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Modified input argument, mathematically first ***)

  ABBREV_TAC `n = n_input MOD n_256` THEN
  SUBGOAL_THEN `n < n_256` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[n_256] THEN ARITH_TAC; ALL_TAC] THEN

  (*** Main loop invariant setup ***)

  ENSURES_WHILE_PUP_TAC `256 DIV blocksize + 1` `pc + 0xdd` `pc + 0x377`
   `\i s.
     (read RSP s = word_add stackpointer (word 296) /\
      read (memory :> bytes64(word_add stackpointer (word 584))) s = res /\
      read (memory :> bytes64(word_add stackpointer (word 592))) s =
      word blocksize /\
      read (memory :> bytes64(word_add stackpointer (word 600))) s =
      word_add tab (word(64 * (2 EXP (blocksize - 1) * i))) /\
      read (memory :> bytes64(word_add stackpointer (word 608))) s = word i /\
      val(read (memory :> bytes64(word_add stackpointer (word 624))) s) <= 1 /\
      bignum_from_memory(word_add stackpointer (word 296),4) s =
      n DIV 2 EXP (blocksize * i) /\
      read (memory :> bytes(tab,len)) s = tabulation /\
      (~(val(read (memory :> bytes64(word_add stackpointer (word 624))) s) = 0)
       ==> &2 * &n rem &2 pow (blocksize * i) >= &2 pow (blocksize * i)) /\
      !P. P IN group_carrier p256_group /\
          p256_tabulates P blocksize tab len tabulation
          ==> represents_p256
                (group_zpow p256_group P
                    (&n rem &2 pow (blocksize * i) -
                     &2 pow (blocksize * i) *
                     &(val(read (memory :> bytes64
                          (word_add stackpointer (word 624))) s))))
                    (bignum_triple_from_memory
                     (word_add stackpointer (word 328),4) s)) /\
     (read RAX s = word i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of invariant ***)

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "nin_" `read (memory :> bytes(scalar,8 * 4)) s0` THEN
    X86_ACCSTEPS_TAC P256_SCALARMULBASE_EXEC [9;11;13;15] (1--38) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    REWRITE_TAC[bignum_triple_from_memory] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s33" THEN
    REWRITE_TAC[MULT_CLAUSES; INT_POW; INT_REM_1] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `carry_s15 <=> n_input < n_256` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
        EXPAND_TAC "n_input" THEN
        REWRITE_TAC[n_256; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[DIV_1] THEN EXPAND_TAC "n" THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[n_256] THEN EXPAND_TAC "n_input" THEN BOUNDER_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_SUB] THEN
      EXPAND_TAC "n_input" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_MUL] THEN
        ASM_REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN
        MATCH_MP_TAC(REAL_ARITH `x:real < y ==> x - &n < y`) THEN
        REWRITE_TAC[REAL_OF_NUM_LT] THEN EXPAND_TAC "n_input" THEN
        BOUNDER_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
      EXPAND_TAC "n_input" THEN
      REWRITE_TAC[bignum_of_wordlist; n_256; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; n_256] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[GROUP_NPOW; group_pow] THEN
      REWRITE_TAC[represents_p256; P256_GROUP; tripled; montgomery_decode;
                  weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES;
                  bignum_of_wordlist; p_256] THEN
      CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC INVERSE_MOD_CONV))];

    (*** Defer the interesting bit, invariant preservation, till later ***)

    ALL_TAC;

    (*** Trivial loop-back goal ***)

    REPEAT STRIP_TAC THEN
    X86_SIM_TAC P256_SCALARMULBASE_EXEC (1--3) THEN
    ASM_REWRITE_TAC[VAL_WORD_MUL; VAL_WORD; ADD_CLAUSES; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    UNDISCH_TAC `i < 256 DIV blocksize + 1` THEN
    REWRITE_TAC[ARITH_RULE `i < n + 1 <=> i <= n`] THEN
    ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `2 <= b ==> ~(b = 0)`] THEN
    REWRITE_TAC[ARITH_RULE `i < 257 <=> i <= 256`] THEN
    MESON_TAC[LE_TRANS; MOD_LE; MULT_SYM];

    (*** Final conversion and mathematics ***)

    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [bignum_triple_from_memory] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN

    SUBGOAL_THEN `257 <= blocksize * (256 DIV blocksize + 1)` ASSUME_TAC THENL
     [MP_TAC(GSYM(SPECL [`256`; `blocksize:num`] DIVISION)) THEN
      ASM_SIMP_TAC[ARITH_RULE `2 <= b ==> ~(b = 0)`] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&n rem &2 pow (blocksize * (256 DIV blocksize + 1)) = &n`
    SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `2 EXP 257` THEN
      ASM_SIMP_TAC[LE_EXP; ARITH_EQ] THEN
      UNDISCH_TAC `n < n_256` THEN REWRITE_TAC[n_256] THEN ARITH_TAC;
      ALL_TAC] THEN

    GHOST_INTRO_TAC `X:num`
     `bignum_from_memory (word_add stackpointer (word 328),4)` THEN
    GHOST_INTRO_TAC `Y:num`
     `bignum_from_memory (word_add stackpointer (word 360),4)` THEN
    GHOST_INTRO_TAC `Z:num`
     `bignum_from_memory (word_add stackpointer (word 392),4)` THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC P256_SCALARMULBASE_EXEC (1--3) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[]
     `read RIP s = (if p then x else y) ==> ~p ==> read RIP s = y`)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD; VAL_WORD_MUL; ADD_CLAUSES; DIMINDEX_64] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[NOT_LT] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o rand o snd) THEN
      ANTS_TAC THENL
       [TRANS_TAC LET_TRANS `31 * (256 + 1)` THEN
        CONJ_TAC THENL [MATCH_MP_TAC LE_MULT2; CONV_TAC NUM_REDUCE_CONV] THEN
        ASM_REWRITE_TAC[LE_ADD_RCANCEL; DIV_LE];
        ASM_SIMP_TAC[]];
      DISCH_TAC] THEN

    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM]) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GE; NOT_LE] THEN ANTS_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP 257` THEN
      ASM_SIMP_TAC[LE_EXP; ARITH_EQ] THEN
      UNDISCH_TAC `n < n_256` THEN REWRITE_TAC[n_256] THEN ARITH_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INT_MUL_RZERO; INT_SUB_RZERO])] THEN

    X86_STEPS_TAC P256_SCALARMULBASE_EXEC (4--6) THEN LOCAL_SQR_TAC 7 THEN
    ABBREV_TAC
     `Z2 =
      read(memory :> bytes(word_add stackpointer (word 424),8 * 4)) s7` THEN
    X86_STEPS_TAC P256_SCALARMULBASE_EXEC (8--11) THEN
    LOCAL_MUL_TAC 12 THEN
    ABBREV_TAC
     `Z3 =
      read(memory :> bytes(word_add stackpointer (word 456),8 * 4)) s12` THEN
    X86_STEPS_TAC P256_SCALARMULBASE_EXEC (13--15) THEN
    LOCAL_DEMONT_TAC 16 THEN
    ABBREV_TAC
     `Z3' =
      read(memory :> bytes(word_add stackpointer (word 424),8 * 4)) s16` THEN
    X86_STEPS_TAC P256_SCALARMULBASE_EXEC (17--19) THEN
    LOCAL_INV_TAC 20 THEN
    ABBREV_TAC
     `I3 =
      read(memory :> bytes(word_add stackpointer (word 456),8 * 4)) s20` THEN
    X86_STEPS_TAC P256_SCALARMULBASE_EXEC (21--24) THEN
    LOCAL_MUL_TAC 25 THEN
    ABBREV_TAC
     `I2 =
      read (memory :> bytes(word_add stackpointer (word 424),8 * 4)) s25` THEN
    X86_STEPS_TAC P256_SCALARMULBASE_EXEC (26--30) THEN
    LOCAL_MUL_TAC 31 THEN
    ABBREV_TAC `X' = read (memory :> bytes(res,8 * 4)) s31` THEN
    X86_STEPS_TAC P256_SCALARMULBASE_EXEC (32--35) THEN
    LOCAL_MUL_TAC 36 THEN
    ABBREV_TAC
     `Y' = read (memory :> bytes(word_add res (word 32),8 * 4)) s36` THEN

    (*** Final mathematics sorting out last affine conversion operations ***)

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s36" THEN X_GEN_TAC `P:(int#int)option` THEN
    STRIP_TAC THEN

    FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
    ASM_REWRITE_TAC[GROUP_NPOW] THEN
    SUBGOAL_THEN
     `group_pow p256_group P n = group_pow p256_group P n_input`
    SUBST1_TAC THENL
     [EXPAND_TAC "n" THEN REWRITE_TAC[GSYM P256_GROUP_ORDER] THEN
      ASM_SIMP_TAC[GROUP_POW_MOD_ORDER; FINITE_GROUP_CARRIER_P256];
      ALL_TAC] THEN

    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS_P256_Y_NONZERO) THEN
    ASM_SIMP_TAC[GROUP_POW] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [represents_p256]) THEN
    REWRITE_TAC[affinepointz_p256] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN

    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    REPEAT(ANTS_TAC THENL
     [TRY(COND_CASES_TAC THEN REWRITE_TAC[MULT_CLAUSES; LE_0] THEN
          W(MP_TAC o PART_MATCH (lhand o lhand) INVERSE_MOD_BOUND o
            rand o lhand o snd) THEN
          REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC) THEN
      REWRITE_TAC[p_256] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_256]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
      (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
       DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
       STRIP_TAC)]) THEN

    ASM_CASES_TAC `Z = 0` THENL
     [ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_MUL_LZERO; INT_MUL_RZERO;
                      INT_REM_ZERO; num_divides; INT_DIVIDES_0; tripled;
                      weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES;
                      montgomery_decode];
      ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN

    MP_TAC(SPECL [`p_256`; `2 EXP 256`] INVERSE_MOD_LMUL_EQ) THEN
    REWRITE_TAC[COPRIME_REXP; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN ANTS_TAC THENL
     [REWRITE_TAC[p_256] THEN ARITH_TAC; DISCH_TAC] THEN

    SUBGOAL_THEN `~(p_256 divides Z3')` MP_TAC THENL
     [ASM_REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      MP_TAC(SPECL [`3`; `p_256`; `Z:num`] PRIME_DIVEXP_EQ) THEN
      ASM_SIMP_TAC[DIVIDES_EQ_ZERO; ARITH_EQ; PRIME_P256] THEN
      ASM_REWRITE_TAC[INT_REM_EQ_0] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_congruent]) THEN
      REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[TAUT `p ==> ~q ==> ~r <=> p /\ r ==> q`] THEN
      CONV_TAC INTEGER_RULE;
      DISCH_THEN(fun th ->
       RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th)] THEN

    SUBGOAL_THEN `~(p_256 divides Y')` MP_TAC THENL
     [ASM_REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      MP_TAC(SPECL [`p_256`; `Z3':num`] INVERSE_MOD_LMUL_EQ) THEN
      ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P256] THEN
      MP_TAC(SPECL [`p_256`; `Y:num`] DIVIDES_EQ_ZERO) THEN
      ASM_REWRITE_TAC[INT_REM_EQ_0] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_congruent]) THEN
      REWRITE_TAC[num_divides; num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[TAUT `p ==> ~q ==> r ==> ~s <=> p /\ r /\ s ==> q`] THEN
      CONV_TAC INTEGER_RULE;
      ASM_SIMP_TAC[DIVIDES_EQ_ZERO] THEN DISCH_TAC] THEN

    ASM_REWRITE_TAC[weierstrass_of_jacobian; tripled; paired] THEN
    COND_CASES_TAC THENL
     [POP_ASSUM MP_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
      REWRITE_TAC[montgomery_decode; INTEGER_MOD_RING_CLAUSES] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_congruent]) THEN
      SIMP_TAC[INT_REM_EQ_0; PRIME_INT_DIVPROD_EQ; PRIME_P256;
               GSYM INT_OF_NUM_CLAUSES] THEN
      ASM_SIMP_TAC[GSYM num_divides; DIVIDES_EQ_ZERO] THEN
      SIMP_TAC[GSYM PRIME_COPRIME_EQ; PRIME_P256; num_coprime] THEN
      CONV_TAC INTEGER_RULE;
      REWRITE_TAC[option_INJ; PAIR_EQ]] THEN

    RULE_ASSUM_TAC(REWRITE_RULE
     [montgomery_decode; INTEGER_MOD_RING_CLAUSES]) THEN
    CONJ_TAC THEN MATCH_MP_TAC fdivlemma THEN
    SIMP_TAC[INTEGER_MOD_RING_CARRIER_REM; montgomery_decode; modular_decode;
             RING_POW; FIELD_POW_EQ_0; FIELD_INTEGER_MOD_RING; PRIME_P256] THEN
    ASM_REWRITE_TAC[ARITH_EQ; INTEGER_MOD_RING_CLAUSES] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
    REWRITE_TAC[INT_MUL_ASSOC] THEN MATCH_MP_TAC(INTEGER_RULE
     `!e:int. (i * e == &1) (mod p) /\ (b * e == a) (mod p)
              ==> (a * i == b) (mod p)`) THEN
    EXISTS_TAC `&Z3':int` THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
       ASM_SIMP_TAC[INVERSE_MOD_LMUL_EQ; PRIME_COPRIME_EQ; PRIME_P256];
       ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES]]) THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC; INT_REM_EQ] THEN
    CONV_TAC INTEGER_RULE] THEN

  (*** Initial ghosting and abbreviations for invariant step ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < 129` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `i < 256 DIV b + 1 ==> 256 DIV b <= 256 DIV 2==> i < 129`)) THEN
    MATCH_MP_TAC DIV_MONO2 THEN ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [bignum_triple_from_memory] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  GHOST_INTRO_TAC `X:num`
   `bignum_from_memory (word_add stackpointer (word 328),4)` THEN
  GHOST_INTRO_TAC `Y:num`
   `bignum_from_memory (word_add stackpointer (word 360),4)` THEN
  GHOST_INTRO_TAC `Z:num`
   `bignum_from_memory (word_add stackpointer (word 392),4)` THEN
  GHOST_INTRO_TAC `ncf:num`
   `\s. val(read (memory :> bytes64(word_add stackpointer (word 624))) s)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `cf:bool` SUBST_ALL_TAC) THEN
  REWRITE_TAC[VAL_EQ_BITVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQ_BITVAL]) THEN
  ABBREV_TAC `bf = n DIV 2 EXP (blocksize * i) MOD 2 EXP blocksize` THEN
  SUBGOAL_THEN `bf < 2 EXP blocksize` ASSUME_TAC THENL
   [EXPAND_TAC "bf" THEN REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `bf + bitval cf <= 2 EXP blocksize` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `b < e /\ c <= 1 ==> b + c <= e`) THEN
    ASM_REWRITE_TAC[BITVAL_BOUND];
    ALL_TAC] THEN
  ABBREV_TAC `cf' <=> bf + bitval cf > 2 EXP (blocksize - 1)` THEN
  ABBREV_TAC
   `j = if cf' then 2 EXP blocksize - (bf + bitval cf)
         else bf + bitval cf` THEN
  SUBGOAL_THEN `j <= 2 EXP (blocksize - 1)` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN UNDISCH_TAC `bf + bitval cf <= 2 EXP blocksize` THEN
    SUBGOAL_THEN `2 EXP blocksize = 2 * 2 EXP (blocksize - 1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `2 <= blocksize` THEN ARITH_TAC;
      EXPAND_TAC "cf'" THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Setup of the inner loop for constant-time table selection ***)

  ENSURES_WHILE_PUP_TAC `2 EXP (blocksize - 1)` `pc + 0x1a0` `pc + 0x1d3`
   `\k s.
     (read RSP s = word_add stackpointer (word 296) /\
      read (memory :> bytes64(word_add stackpointer (word 584))) s = res /\
      read (memory :> bytes64(word_add stackpointer (word 592))) s =
      word blocksize /\
      read RBP s = word_add tab
       (word(64 * (2 EXP (blocksize - 1) * i + k))) /\
      read (memory :> bytes64(word_add stackpointer (word 608))) s = word i /\
      bignum_from_memory(word_add stackpointer (word 296),4) s =
      n DIV 2 EXP (blocksize * (i + 1)) /\
      read (memory :> bytes(tab,len)) s = tabulation /\
      bignum_from_memory (word_add stackpointer (word 328),4) s = X /\
      bignum_from_memory (word_add stackpointer (word 360),4) s = Y /\
      bignum_from_memory (word_add stackpointer (word 392),4) s = Z /\
      read (memory :> bytes64(word_add stackpointer (word 632))) s = word j /\
      read (memory :> bytes64(word_add stackpointer (word 624))) s =
      word (bitval cf') /\
      read RSI s = word_sub (word(2 EXP (blocksize - 1))) (word k) /\
      read R12 s = word_sub (word j) (word k) /\
      !P. ~(j = 0) /\ j <= k /\
          P IN group_carrier p256_group /\
          p256_tabulates P blocksize tab len tabulation
          ==> represents2_p256
               (group_pow p256_group P (2 EXP (blocksize * i) * j))
             (bignum_of_wordlist[read RAX s;read RBX s;read RCX s;read RDX s],
              bignum_of_wordlist[read R8 s;read R9 s;read R10 s;read R11 s])) /\
     (read ZF s <=> k = 2 EXP (blocksize - 1))`
  THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXP_EQ_0; ARITH_EQ];

    (*** Bitfield selection and processing for indexing step ***)
    (*** Finished lazily by case analysis over blocksize not intelligence ***)

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "nin_"
     `read (memory :> bytes (word_add stackpointer (word 296),8 * 4)) s0` THEN
    X86_STEPS_TAC P256_SCALARMULBASE_EXEC (1--9) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `word bf:int64` o  MATCH_MP (MESON[]
        `read RAX s = a ==> !a'. a = a' ==> read RAX s = a'`)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_64_CLAUSES; MOD_LT] THEN
      EXPAND_TAC "bf" THEN
      SUBGOAL_THEN
       `(n DIV 2 EXP (blocksize * i)) MOD 2 EXP blocksize =
        (n DIV 2 EXP (blocksize * i)) MOD 2 EXP 64 MOD 2 EXP blocksize`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `n < s ==> MIN s n = n`];
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
        (RAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV) [SYM th]) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      ONCE_REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; VAL_MOD_REFL] THEN
      REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD; WORD_VAL] THEN
      SIMP_TAC[WORD_SUB; EXP_EQ_0; ARITH_EQ; LE_1] THEN
      REWRITE_TAC[word_shl; MULT_CLAUSES; VAL_WORD_1] THEN
      REWRITE_TAC[WORD_AND_SYM];
      DISCH_TAC] THEN

    X86_STEPS_TAC P256_SCALARMULBASE_EXEC (10--37) THEN

    SUBGOAL_THEN
     `word_add (word bf) (word(bitval cf)):int64 =
      word(bf + bitval cf)`
    SUBST_ALL_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN

    FIRST_X_ASSUM(MP_TAC o check (can
      (term_match []
       `read (memory :> bytes64(word_add stackpointer (word 624))) s = a` o
      concl))) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM NOT_LE] THEN

    SUBGOAL_THEN
     `val(word(bf + bitval cf):int64) <=
       val(word_ushr
           (word_shl (word 1:int64)
             (val (word(blocksize MOD 256):byte) MOD 64)) 1) <=>
      ~cf'`
    SUBST_ALL_TAC THENL
     [EXPAND_TAC "cf'" THEN REWRITE_TAC[GT; NOT_LT; MOD_64_CLAUSES] THEN
      ASM_SIMP_TAC[MOD_LT; GSYM WORD_ADD; VAL_WORD_USHR; VAL_WORD_SHL] THEN
      REWRITE_TAC[VAL_WORD_1; MULT_CLAUSES; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 64 ==> n < 2 EXP 64`] THEN
      ASM_SIMP_TAC[MOD_LT; LT_EXP; ARITH_EQ; ARITH_LE; ARITH_LT] THEN
      ASM_SIMP_TAC[DIV_EXP; ARITH_EQ; ARITH_RULE `2 <= b ==> 1 <= b`] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN
      TRANS_TAC LET_TRANS `2 EXP blocksize` THEN
      ASM_REWRITE_TAC[LT_EXP; ARITH_EQ; LE_REFL];
      REWRITE_TAC[WORD_NEG_NEG] THEN DISCH_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP])] THEN

    RULE_ASSUM_TAC(REWRITE_RULE[MOD_64_CLAUSES]) THEN

    SUBGOAL_THEN
     `(if cf'
       then word_sub (word_shl (word 1) (blocksize MOD 64))
            (word(bf + bitval cf))
       else word(bf + bitval cf)):int64 =
      word j`
    SUBST_ALL_TAC THENL
     [ASM_SIMP_TAC[MOD_LT] THEN EXPAND_TAC "j" THEN COND_CASES_TAC THEN
      REWRITE_TAC[WORD_SUB; word_jshl; word_shl; VAL_WORD_1] THEN
      ASM_SIMP_TAC[DIMINDEX_64; MOD_LT; VAL_WORD_USHR; VAL_WORD_SHL;
                   VAL_WORD_1; MULT_CLAUSES; MOD_LT; LT_EXP;
                   ARITH_EQ; ARITH_LE; ARITH_LT; DIV_EXP] THEN
      REWRITE_TAC[WORD_ADD];
      ALL_TAC] THEN

    SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LET_TRANS `2 EXP (blocksize - 1)` THEN
      ASM_REWRITE_TAC[LT_EXP; ARITH_EQ; LE_REFL] THEN
      UNDISCH_TAC `blocksize < 64` THEN ARITH_TAC;
      ALL_TAC] THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; SUB_0; WORD_SUB_0] THEN
    REWRITE_TAC[MESON[LE] `~(j = 0) /\ j <= 0 /\ P <=> F`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `b * (i + 1) = b * i + b`] THEN
    REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN
      EXISTS_TAC `val(nin_0:int64) MOD 2 EXP blocksize` THEN
      REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    UNDISCH_TAC `2 <= blocksize` THEN UNDISCH_TAC `blocksize < 64` THEN
    SPEC_TAC(`blocksize:num`,`blocksize:num`) THEN
    REWRITE_TAC[bignum_of_wordlist; word_jushr; word_jshl; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;

    (*** The actual indexing ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; bignum_triple_from_memory] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY ABBREV_TAC
     [`t0 = read RAX s0`;
      `t1 = read RBX s0`;
      `t2 = read RCX s0`;
      `t3 = read RDX s0`;
      `t4 = read R8 s0`;
      `t5 = read R9 s0`;
      `t6 = read R10 s0`;
      `t7 = read R11 s0`] THEN
    ABBREV_TAC
     `newtab:int64 = word_add tab
                     (word(64 * (2 EXP (blocksize - 1) * i + k)))` THEN
    BIGNUM_LDIGITIZE_TAC "tabw_"
     `read (memory :> bytes (newtab,8 * 8)) s0` THEN
    X86_STEPS_TAC P256_SCALARMULBASE_EXEC (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [EXPAND_TAC "newtab" THEN CONV_TAC WORD_RULE; ALL_TAC]) THEN
    REWRITE_TAC[VAL_EQ_0; WORD_RULE
     `word_sub (word_sub x (word k)) (word 1) = word 0 <=>
      word(k + 1) = x`] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[GSYM VAL_EQ] THEN BINOP_TAC THEN
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      TRANS_TAC LET_TRANS `2 EXP (blocksize - 1)` THEN
      ASM_SIMP_TAC[ARITH_RULE `k + 1 <= n <=> k < n`] THEN
      SIMP_TAC[LT_EXP] THEN UNDISCH_TAC `blocksize < 64` THEN ARITH_TAC] THEN
    X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
    SUBGOAL_THEN `word(k + 1):int64 = word j <=> j = k + 1` SUBST1_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
      REWRITE_TAC[GSYM VAL_EQ] THEN BINOP_TAC THEN
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      TRANS_TAC LET_TRANS `2 EXP (blocksize - 1)` THEN
      ASM_REWRITE_TAC[ARITH_RULE `k + 1 <= n <=> k < n`] THEN
      REWRITE_TAC[LT_EXP] THEN UNDISCH_TAC `blocksize < 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
     `j <= k + 1 ==> j = k + 1 \/ j <= k /\ ~(j = k + 1)`)) THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `p256_tabulates P blocksize tab len tabulation` THEN
    EXPAND_TAC "tabulation" THEN REWRITE_TAC[p256_tabulates] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[ARITH_RULE `i <= 256 DIV b <=> i < 256 DIV b + 1`] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_SIMP_TAC[LE_1; ADD_SUB] THEN
    REWRITE_TAC[bignum_pair_from_memory; BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[WORD_RULE `word(8 * 4) = word 32`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[ARITH_RULE `k + 1 <= n <=> k < n`];

    (*** Loop-back for the inner loop ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; bignum_triple_from_memory] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC P256_SCALARMULBASE_EXEC [1]  THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    ALL_TAC] THEN

  (*** The continuation into the rest of the main loop ***)

  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY ABBREV_TAC
   [`t0 = read RAX s0`;
    `t1 = read RBX s0`;
    `t2 = read RCX s0`;
    `t3 = read RDX s0`;
    `t4 = read R8 s0`;
    `t5 = read R9 s0`;
    `t6 = read R10 s0`;
    `t7 = read R11 s0`] THEN
  X86_ACCSTEPS_TAC P256_SCALARMULBASE_EXEC (8--11) (1--25) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL; BITVAL_EQ_0]) THEN
  MAP_EVERY ABBREV_TAC
   [`xs = read(memory :> bytes(word_add stackpointer (word 520),8 * 4)) s25`;
    `ys =
     read(memory :> bytes(word_add stackpointer (word 552),8 * 4)) s25`] THEN

  SUBGOAL_THEN
  `!P. ~(j = 0) /\
       P IN group_carrier p256_group /\
       p256_tabulates P blocksize tab len tabulation
       ==> represents2_p256
            (group_zpow p256_group P
              (--(&1) pow (bitval cf') * &2 pow (blocksize * i) * &j))
            (xs,ys)`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
    ASM_REWRITE_TAC[GSYM GROUP_NPOW; GSYM INT_OF_NUM_CLAUSES] THEN
    MAP_EVERY EXPAND_TAC ["xs"; "ys"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[WORD_BITVAL_EQ_0; COND_SWAP] THEN
    COND_CASES_TAC THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[INT_MUL_LID; GSYM INT_NEG_MINUS1] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS2_P256_NEGATION) THEN
    ASM_SIMP_TAC[GROUP_ZPOW; GROUP_ZPOW_NEG] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [REWRITE_TAC[p_256] THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o el 1 o CONJUNCTS o
     GEN_REWRITE_RULE I [represents2_p256]) THEN
    SIMP_TAC[num_congruent; GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_POW_EQ_0] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[bignum_of_wordlist; p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Mixed addition operation ***)

  X86_STEPS_TAC P256_SCALARMULBASE_EXEC (26--29) THEN
  LOCAL_JMIXADD_TAC 30 THEN
  MAP_EVERY ABBREV_TAC
   [`Xo = read(memory :> bytes(word_add stackpointer (word 424),8 * 4)) s30`;
    `Yo = read(memory :> bytes(word_add stackpointer (word 456),8 * 4)) s30`;
    `Zo = read(memory :> bytes(word_add stackpointer (word 488),8 * 4)) s30`]
  THEN BIGNUM_LDIGITIZE_TAC "xo_"
   `read(memory :> bytes(word_add stackpointer (word 424),8 * 4)) s30` THEN
  BIGNUM_LDIGITIZE_TAC "yo_"
   `read(memory :> bytes(word_add stackpointer (word 456),8 * 4)) s30` THEN
  BIGNUM_LDIGITIZE_TAC "z0_"
   `read(memory :> bytes(word_add stackpointer (word 488),8 * 4)) s30` THEN
  BIGNUM_LDIGITIZE_TAC "xi_"
   `read(memory :> bytes(word_add stackpointer (word 328),8 * 4)) s30` THEN
  BIGNUM_LDIGITIZE_TAC "yi_"
   `read(memory :> bytes(word_add stackpointer (word 360),8 * 4)) s30` THEN
  BIGNUM_LDIGITIZE_TAC "zi_"
   `read(memory :> bytes(word_add stackpointer (word 392),8 * 4)) s30` THEN

  (*** Multiplexing away the j = 0 case ***)

  X86_STEPS_TAC P256_SCALARMULBASE_EXEC (31--71) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL; BITVAL_BOUND; GSYM WORD_ADD] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_BOUND; GSYM WORD_ADD]] THEN

  (*** Final mathematics ***)

  SUBGOAL_THEN
   `&n rem &2 pow (blocksize * (i + 1)) =
    &2 pow (blocksize * i) * &bf + &n rem &2 pow (blocksize * i)`
  (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "+" th) THENL
   [EXPAND_TAC "bf" THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; INT_OF_NUM_REM] THEN
    REWRITE_TAC[GSYM MOD_MULT_MOD] THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE `b * (i + 1) = b * i + b`];
    ALL_TAC] THEN

  REWRITE_TAC[BITVAL_EQ_0] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [EXPAND_TAC "cf'" THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GE; GT; INT_OF_NUM_REM] THEN
    MATCH_MP_TAC(ARITH_RULE
     `c <= 1 /\ (2 * h <= 2 * b ==> x <= 2 * y)
      ==> h < b + c ==> x <= 2 * (y + z)`) THEN
    REWRITE_TAC[GSYM(CONJUNCT2 EXP); BITVAL_BOUND] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= b ==> SUC(b - 1) = b`] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `2 * a * b = a * 2 * b`] THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE `b * (i + 1) = b * i + b`] THEN
    SIMP_TAC[LE_MULT_LCANCEL];
    DISCH_TAC] THEN

  X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
  REWRITE_TAC[bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[WORD_SUB_0; COND_SWAP] THEN

  DISCARD_STATE_TAC "s71" THEN

  SUBGOAL_THEN `val(word j:int64) = 0 <=> j = 0` SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    REWRITE_TAC[DIMINDEX_64] THEN
    TRANS_TAC LET_TRANS `2 EXP (blocksize - 1)` THEN
    ASM_REWRITE_TAC[LT_EXP] THEN UNDISCH_TAC `blocksize < 64` THEN ARITH_TAC;
    ALL_TAC] THEN

  ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THENL
   [REPLICATE_TAC 3
     (FIRST_X_ASSUM(K ALL_TAC o SPEC `P:(int#int)option`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC
     `(if cf' then 2 EXP blocksize - (bf + bitval cf) else bf + bitval cf) =
      j` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_SUB] THEN
    REWRITE_TAC[ARITH_RULE `b * (i + 1) = b * i + b`; INT_POW_ADD] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_RING;
    ALL_TAC] THEN

  ASM_CASES_TAC
   `&n rem &2 pow (blocksize * i) - &2 pow (blocksize * i) * &(bitval cf) =
    -- &1 pow bitval cf' * &2 pow (blocksize * i) * &j`
  THENL
   [POP_ASSUM MP_TAC THEN MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    ASM_CASES_TAC `&n rem &2 pow (blocksize * i) = &0` THENL
     [FIRST_X_ASSUM(K ALL_TAC o check (is_imp o concl)) THEN
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
      ASM_REWRITE_TAC[INT_GE; INT_MUL_RZERO; BITVAL_EQ_0] THEN
      SIMP_TAC[INT_NOT_LE; INT_LT_POW2; BITVAL_CLAUSES] THEN
      DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(MP_TAC o SYM) THEN
      REWRITE_TAC[INT_MUL_RZERO; INT_SUB_REFL; INT_ENTIRE] THEN
      ASM_REWRITE_TAC[INT_OF_NUM_EQ; INT_POW_EQ_0] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
      REWRITE_TAC[ARITH_RULE `b * (i + 1) = b * i + b`; INT_POW_ADD] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
        `r - e * x:int = c * e * j ==> e divides r`)) THEN
      REWRITE_TAC[GSYM num_divides; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      REWRITE_TAC[GSYM NOT_LT; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES]];
    ALL_TAC] THEN

  FIRST_X_ASSUM(MP_TAC o SPECL
   [`group_zpow p256_group P
       (&n rem &2 pow (blocksize * i) -
        &2 pow (blocksize * i) * &(bitval cf))`;
    `group_zpow p256_group P
        (-- &1 pow bitval cf' * &2 pow (blocksize * i) * &j)`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
  FIRST_X_ASSUM(K ALL_TAC o SPEC `P:(int#int)option`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN

  SUBGOAL_THEN
   `-- &1 pow bitval cf' * &2 pow (blocksize * i) * &j:int =
    (&2 pow (blocksize * i) * (&bf + &(bitval cf))) -
    &2 pow (blocksize * (i + 1)) * &(bitval cf')`
  (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "*" th) THENL
   [UNDISCH_THEN
     `(if cf' then 2 EXP blocksize - (bf + bitval cf) else bf + bitval cf) =
      j` (SUBST1_TAC o SYM) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
    REWRITE_TAC[ARITH_RULE `b * (i + 1) = b * i + b`; INT_POW_ADD] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_RING;
    ASM_SIMP_TAC[GSYM GROUP_ZPOW_ADD]] THEN

  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN CONV_TAC INT_RING] THEN
  ASM_SIMP_TAC[GROUP_ZPOW_EQ; P256_GROUP_ELEMENT_ORDER] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS2_P256_NONZERO) THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GROUP_ZPOW_ID] THEN
  DISCH_THEN(K ALL_TAC) THEN

  W(MP_TAC o PART_MATCH (rand o lhand) INT_CONG_IMP_EQ o rand o snd) THEN
  ASM_REWRITE_TAC[TAUT `~(p /\ q) ==> ~q <=> ~(~p /\ q)`] THEN
  REWRITE_TAC[INT_NOT_LT] THEN

  ASM_CASES_TAC `blocksize * (i + 1) <= 256` THENL
   [DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[INT_NOT_LE] THEN
    MATCH_MP_TAC(INT_ARITH
     `!y. (&0 <= x /\ x < e) /\ (&0 <= b * e /\ b * e <= e) /\
          abs(z:int) <= e * y /\ e * (y + &1) < f
          ==> abs(x - e * b - z) < f`) THEN
    EXISTS_TAC `(&2:int) pow (blocksize - 1)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES; LE_0; MOD_LT_EQ] THEN
      REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0; bitval] THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_ABS_MUL; INT_ABS_POW; INT_ABS_NEG; INT_ABS_NUM] THEN
      REWRITE_TAC[INT_POW_ONE; INT_MUL_LID] THEN
      SIMP_TAC[INT_LE_LMUL_EQ; INT_LT_POW2] THEN
      ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
      ALL_TAC] THEN
    MATCH_MP_TAC(INT_ARITH
     `e * &2 pow 1 <= e * b /\ &3 * e * &2 * b:int < &4 * n
      ==> e * (b + &1) < n`) THEN
    SIMP_TAC[INT_LE_LMUL_EQ; INT_LT_POW2; GSYM(CONJUNCT2 INT_POW)] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INT_POW_MONO THEN UNDISCH_TAC `2 <= blocksize` THEN
      ARITH_TAC;
      REWRITE_TAC[GSYM INT_POW_ADD]] THEN
    ASM_SIMP_TAC[ARITH_RULE
      `2 <= b ==> b * i + SUC(b - 1) = b * (i + 1)`] THEN
    TRANS_TAC INT_LET_TRANS `(&3:int) * &2 pow 256` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[n_256] THEN INT_ARITH_TAC] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN REWRITE_TAC[INT_POS] THEN
    MATCH_MP_TAC INT_POW_MONO THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN

  FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE I [TAUT `p ==> q <=> q \/ ~p`]) THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    REMOVE_THEN "+" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GE; NOT_LE; INT_OF_NUM_REM] THEN
    MATCH_MP_TAC(ARITH_RULE
     `m MOD n <= m /\ 2 * m < e ==> 2 * m MOD n < e`) THEN
    REWRITE_TAC[MOD_LE] THEN TRANS_TAC LTE_TRANS `2 EXP 257` THEN
    ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; ARITH_RULE `257 <= a <=> 256 < a`] THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[n_256] THEN ARITH_TAC;
    DISCH_THEN(fun th -> SUBST_ALL_TAC(EQF_INTRO th)) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    REWRITE_TAC[BITVAL_CLAUSES; INT_MUL_RZERO; CONJUNCT1 INT_POW;
                INT_MUL_LID; INT_SUB_RZERO; INT_ADD_RID] THEN
    STRIP_TAC] THEN

  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  BOOL_CASES_TAC `cf:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; INT_MUL_RZERO; CONJUNCT1 INT_POW;
                INT_MUL_LID; INT_SUB_RZERO; INT_ADD_RID; INT_MUL_RID;
                ARITH_EQ; ADD_CLAUSES] THEN
  STRIP_TAC THENL
   [UNDISCH_THEN
     `&2 pow (blocksize * i) * &j:int = &2 pow (blocksize * i) * (&bf + &1)`
     (K ALL_TAC) THEN
    UNDISCH_THEN `bf + 1 = j` (SUBST_ALL_TAC o SYM);
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[INT_NOT_LE] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0:int <= x /\ abs(y) + x < n ==> abs(x - y) < n`) THEN
    REWRITE_TAC[INT_ABS_MUL; INT_ABS_POW; INT_ABS_NUM] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_POS] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    W(MP_TAC o PART_MATCH lhand MOD_LE o lhand o snd) THEN
    UNDISCH_TAC `n < n_256` THEN ARITH_TAC] THEN

  SUBGOAL_THEN `blocksize * i <= 256` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM LE_RDIV_EQ; ARITH_RULE `2 <= b ==> ~(b = 0)`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `a <= b <=> a < b + 1`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `bi <= 256 ==> bi = 256 \/ bi <= 255`))
  THENL
   [SUBGOAL_THEN `&bf:int = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC
       `&n rem &2 pow (blocksize * (i + 1)) =
        &2 pow (blocksize * i) * &bf + &n rem &2 pow (blocksize * i)` THEN
      GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN DISCH_TAC THEN
      MATCH_MP_TAC(ARITH_RULE
       `n' < n_256 /\ n_256 < e /\ (e * 1 <= e * b)
        ==> ~(n' = e * b + n)`) THEN
      ASM_SIMP_TAC[LE_MULT_LCANCEL; LE_1; EXP_EQ_0; ARITH_EQ] THEN
      CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[n_256] THEN ARITH_TAC] THEN
      W(MP_TAC o PART_MATCH lhand MOD_LE o lhand o snd) THEN
      UNDISCH_TAC `n < n_256` THEN ARITH_TAC;
      REWRITE_TAC[INT_ADD_LID; INT_MUL_RID]] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[INTEGER_RULE
     `(a - b:int == b) (mod n) <=> (a == &2 * b) (mod n)`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES;
                    GSYM num_congruent] THEN
    SUBGOAL_THEN `n MOD 2 EXP 256 = n` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `n < n_256` THEN
      REWRITE_TAC[n_256] THEN ARITH_TAC;
      ASM_SIMP_TAC[CONG; MOD_LT] THEN DISCH_TAC] THEN
    UNDISCH_TAC
     `&2 * &n rem &2 pow (blocksize * i) >= &2 pow (blocksize * i)` THEN
    ASM_REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[n_256] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (INTEGER_RULE
   `(l - q:int == q * (b + &1)) (mod n)
    ==> (n - q == q * (b + &1) - l) (mod n)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    INT_CONG_IMP_EQ)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `(&0:int <= x /\ x < n) /\ (&0 <= y /\ y < n) ==> abs(x - y) < n`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INT_SUB_LE] THEN
      TRANS_TAC INT_LE_TRANS `(&2:int) pow 255` THEN
      ASM_SIMP_TAC[INT_POW_MONO; INT_ARITH `&1:int <= &2`] THEN
      REWRITE_TAC[n_256] THEN INT_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `a - b:int < a <=> &0 < b`; INT_LT_POW2];
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM; INT_SUB_LE] THEN
      MATCH_MP_TAC(ARITH_RULE `m < e ==> m <= e * (b + 1)`) THEN
      REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    TRANS_TAC INT_LET_TRANS `&n rem &2 pow (blocksize * (i + 1))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC
        `&2 * &n rem &2 pow (blocksize * i) >= &2 pow (blocksize * i)` THEN
      INT_ARITH_TAC;
      REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
      W(MP_TAC o PART_MATCH lhand MOD_LE o lhand o snd) THEN
      UNDISCH_TAC `n < n_256` THEN ARITH_TAC];
    REWRITE_TAC[INT_ARITH
     `n - q:int = q * (b + &1) - l <=> q * (b + &2) = n + l`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN DISCH_TAC] THEN

  FIRST_ASSUM(MP_TAC o SPEC `2 EXP 256 - n_256` o MATCH_MP (NUMBER_RULE
   `e * b:num = n + x ==> !m. e divides (n + m) ==> (x == m) (mod e)`)) THEN
  REWRITE_TAC[n_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 256`)] THEN
  ASM_SIMP_TAC[DIVIDES_EXP_LE_IMP; ARITH_RULE `i <= 255 ==> i <= 256`] THEN
  REWRITE_TAC[CONG; MOD_MOD_REFL] THEN MATCH_MP_TAC(MESON[]
   `(n MOD 2 EXP 256 MOD e = n MOD e) /\ ~(x = n MOD 2 EXP 256 MOD e)
    ==> ~(x = n MOD e)`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `i <= 255 ==> MIN 256 i = i`];
    CONV_TAC NUM_REDUCE_CONV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[MOD_LE; LE_TRANS]
   `x = a MOD n ==> x <= a`)) THEN
  UNDISCH_TAC
   `&2 * &n rem &2 pow (blocksize * i) >= &2 pow (blocksize * i)` THEN
  REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES; GE] THEN
  MATCH_MP_TAC(ARITH_RULE
   `2 * a < e ==> e <= 2 * x ==> ~(x <= a)`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  TRANS_TAC LTE_TRANS `2 EXP 225` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
  MAP_EVERY UNDISCH_TAC
   [`256 < blocksize * (i + 1)`; `blocksize <= 31`] THEN
  ARITH_TAC);;

let P256_SCALARMULBASE_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!res scalar blocksize tab n len tabulation pc stackpointer returnaddress.
        2 <= val blocksize /\ val blocksize <= 31 /\
        ALL (nonoverlapping (word_sub stackpointer (word 696),696))
            [(word pc,LENGTH p256_scalarmulbase_tmc); (scalar,32); (tab,len)] /\
        ALL (nonoverlapping (res,64))
            [(word pc,LENGTH p256_scalarmulbase_tmc); (word_sub stackpointer (word 696),704)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p256_scalarmulbase_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [res;scalar;blocksize;tab] s /\
                  bignum_from_memory (scalar,4) s = n /\
                  read (memory :> bytes(tab,len)) s = tabulation)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. P IN group_carrier p256_group /\
                      p256_tabulates P (val blocksize) tab len tabulation
                      ==> affinepointz_p256
                           (bignum_pair_from_memory(res,4) s)
                           (group_pow p256_group P n))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,64);
                      memory :> bytes(word_sub stackpointer (word 696),696)])`,
   X86_ADD_RETURN_STACK_TAC P256_SCALARMULBASE_EXEC
   P256_SCALARMULBASE_CORRECT `[RBX; RBP; R12; R13; R14; R15]`
     696);;

let P256_SCALARMULBASE_SUBROUTINE_CORRECT = time prove
 (`!res scalar blocksize tab n len tabulation pc stackpointer returnaddress.
        2 <= val blocksize /\ val blocksize <= 31 /\
        ALL (nonoverlapping (word_sub stackpointer (word 696),696))
            [(word pc,LENGTH p256_scalarmulbase_mc); (scalar,32); (tab,len)] /\
        ALL (nonoverlapping (res,64))
            [(word pc,LENGTH p256_scalarmulbase_mc); (word_sub stackpointer (word 696),704)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p256_scalarmulbase_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [res;scalar;blocksize;tab] s /\
                  bignum_from_memory (scalar,4) s = n /\
                  read (memory :> bytes(tab,len)) s = tabulation)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. P IN group_carrier p256_group /\
                      p256_tabulates P (val blocksize) tab len tabulation
                      ==> affinepointz_p256
                           (bignum_pair_from_memory(res,4) s)
                           (group_pow p256_group P n))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,64);
                      memory :> bytes(word_sub stackpointer (word 696),696)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE P256_SCALARMULBASE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let p256_scalarmulbase_windows_mc = define_from_elf "p256_scalarmulbase_windows_mc"
      "x86/p256/p256_scalarmulbase.obj";;

let p256_scalarmulbase_windows_tmc = define_trimmed "p256_scalarmulbase_windows_tmc" p256_scalarmulbase_windows_mc;;

let P256_SCALARMULBASE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!res scalar blocksize tab n len tabulation pc stackpointer returnaddress.
        2 <= val blocksize /\ val blocksize <= 31 /\
        ALL (nonoverlapping (word_sub stackpointer (word 728),728))
            [(word pc,LENGTH p256_scalarmulbase_windows_tmc); (scalar,32); (tab,len)] /\
        ALL (nonoverlapping (res,64))
            [(word pc,LENGTH p256_scalarmulbase_windows_tmc); (word_sub stackpointer (word 728),736)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p256_scalarmulbase_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [res;scalar;blocksize;tab] s /\
                  bignum_from_memory (scalar,4) s = n /\
                  read (memory :> bytes(tab,len)) s = tabulation)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. P IN group_carrier p256_group /\
                      p256_tabulates P (val blocksize) tab len tabulation
                      ==> affinepointz_p256
                           (bignum_pair_from_memory(res,4) s)
                           (group_pow p256_group P n))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,64);
                      memory :> bytes(word_sub stackpointer (word 728),728)])`,
  let WINDOWS_P256_SCALARMULBASE_EXEC =
    X86_MK_EXEC_RULE p256_scalarmulbase_windows_tmc
  and baseth =
    X86_SIMD_SHARPEN_RULE P256_SCALARMULBASE_NOIBT_SUBROUTINE_CORRECT
    (X86_ADD_RETURN_STACK_TAC P256_SCALARMULBASE_EXEC
      P256_SCALARMULBASE_CORRECT `[RBX; RBP; R12; R13; R14; R15]`
        696) in
  let subth =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
     (REWRITE_RULE[bignum_pair_from_memory] baseth) in
  REWRITE_TAC[fst WINDOWS_P256_SCALARMULBASE_EXEC] THEN
  REPLICATE_TAC 8 GEN_TAC THEN WORD_FORALL_OFFSET_TAC 728 THEN
  REWRITE_TAC[ALL; WINDOWS_C_ARGUMENTS; SOME_FLAGS;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  REWRITE_TAC[bignum_pair_from_memory; WORD_RULE `word(8 * 4) = word 32`] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  UNDISCH_THEN `read RSP s0 = word_add stackpointer (word 728)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  RULE_ASSUM_TAC
   (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  X86_STEPS_TAC WINDOWS_P256_SCALARMULBASE_EXEC (1--7) THEN
  X86_SUBROUTINE_SIM_TAC
   (p256_scalarmulbase_windows_tmc,
    WINDOWS_P256_SCALARMULBASE_EXEC,
    0x16,p256_scalarmulbase_tmc,subth)
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
    `read(memory :> bytes(read RSI s,8 * 4)) s`;
    `len:num`; `tabulation:num`;
    `pc + 0x16`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`] 8 THEN
  X86_STEPS_TAC WINDOWS_P256_SCALARMULBASE_EXEC (9--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let P256_SCALARMULBASE_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!res scalar blocksize tab n len tabulation pc stackpointer returnaddress.
        2 <= val blocksize /\ val blocksize <= 31 /\
        ALL (nonoverlapping (word_sub stackpointer (word 728),728))
            [(word pc,LENGTH p256_scalarmulbase_windows_mc); (scalar,32); (tab,len)] /\
        ALL (nonoverlapping (res,64))
            [(word pc,LENGTH p256_scalarmulbase_windows_mc); (word_sub stackpointer (word 728),736)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p256_scalarmulbase_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [res;scalar;blocksize;tab] s /\
                  bignum_from_memory (scalar,4) s = n /\
                  read (memory :> bytes(tab,len)) s = tabulation)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. P IN group_carrier p256_group /\
                      p256_tabulates P (val blocksize) tab len tabulation
                      ==> affinepointz_p256
                           (bignum_pair_from_memory(res,4) s)
                           (group_pow p256_group P n))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,64);
                      memory :> bytes(word_sub stackpointer (word 728),728)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE P256_SCALARMULBASE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

