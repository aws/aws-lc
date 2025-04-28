(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery inverse modulo p_384, the field characteristic for NIST P-384. *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "Divstep/divstep_bounds.ml";;

(* ------------------------------------------------------------------------- *)
(* The code.                                                                 *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "x86/p384/bignum_montinv_p384.o";;
 ****)

let bignum_montinv_p384_mc = define_assert_from_elf "bignum_montinv_p384_mc" "x86/p384/bignum_montinv_p384.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0x50; 0x01; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 336)) *)
  0x48; 0x89; 0xbc; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% rdi) *)
  0xb8; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% eax) (Imm32 (word 4294967295)) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x89; 0x5c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rbx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8d; 0x4d; 0xfe;  (* LEA (% rcx) (%% (rbp,18446744073709551614)) *)
  0x48; 0x89; 0x4c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rcx) *)
  0x48; 0x8d; 0x55; 0xff;  (* LEA (% rdx) (%% (rbp,18446744073709551615)) *)
  0x48; 0x89; 0x54; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rdx) *)
  0x48; 0x89; 0x54; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rdx) *)
  0x48; 0x89; 0x54; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rdx) *)
  0x48; 0x89; 0x6c; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rbp) *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x4c; 0x8b; 0x66; 0x20;  (* MOV (% r12) (Memop Quadword (%% (rsi,32))) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x4c; 0x8b; 0x6e; 0x28;  (* MOV (% r13) (Memop Quadword (%% (rsi,40))) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0x06;  (* CMOVB (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x0f; 0x42; 0x4e; 0x08;
                           (* CMOVB (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x0f; 0x42; 0x56; 0x10;
                           (* CMOVB (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x0f; 0x42; 0x5e; 0x18;
                           (* CMOVB (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x0f; 0x42; 0x66; 0x20;
                           (* CMOVB (% r12) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x0f; 0x42; 0x6e; 0x28;
                           (* CMOVB (% r13) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r13) *)
  0x48; 0x89; 0x6c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rbp) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rax) *)
  0x48; 0xb9; 0x00; 0x08; 0x00; 0x00; 0x00; 0xf0; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446726481523509248)) *)
  0x48; 0x89; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% rcx) *)
  0x48; 0xba; 0xff; 0x07; 0x00; 0x00; 0x00; 0x10; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 17592186046463)) *)
  0x48; 0x89; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% rdx) *)
  0x48; 0x0f; 0xba; 0xf1; 0x0b;
                           (* BTR (% rcx) (Imm8 (word 11)) *)
  0x48; 0x89; 0x8c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% rdx) *)
  0x48; 0x0f; 0xba; 0xe8; 0x0b;
                           (* BTS (% rax) (Imm8 (word 11)) *)
  0x48; 0x89; 0x84; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% rax) *)
  0x48; 0xc7; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00; 0x0f; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (Imm32 (word 15)) *)
  0x48; 0xc7; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (Imm32 (word 1)) *)
  0xe9; 0xaf; 0x07; 0x00; 0x00;
                           (* JMP (Imm32 (word 1967)) *)
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
  0x48; 0x89; 0xbc; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% rdi) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x4c; 0x21; 0xe8;        (* AND (% rax) (% r13) *)
  0x4c; 0x89; 0xf6;        (* MOV (% rsi) (% r14) *)
  0x4c; 0x21; 0xfe;        (* AND (% rsi) (% r15) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x89; 0xb4; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% rsi) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd7;        (* ADC (% rdi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xee; 0x3b;
                           (* SHRD (% rsi) (% rbp) (Imm8 (word 59)) *)
  0x48; 0x89; 0x74; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x0f; 0xac; 0xfd; 0x3b;
                           (* SHRD (% rbp) (% rdi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x6c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x0f; 0xac; 0xf1; 0x3b;
                           (* SHRD (% rcx) (% rsi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x4c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x0f; 0xac; 0xdf; 0x3b;
                           (* SHRD (% rdi) (% rbx) (Imm8 (word 59)) *)
  0x48; 0x89; 0x7c; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rdi) *)
  0x31; 0xff;              (* XOR (% edi) (% edi) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd7;        (* ADC (% rdi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd7;        (* ADC (% rdi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xee; 0x3b;
                           (* SHRD (% rsi) (% rbp) (Imm8 (word 59)) *)
  0x48; 0x89; 0x74; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xcb; 0x3b;
                           (* SHRD (% rbx) (% rcx) (Imm8 (word 59)) *)
  0x48; 0x89; 0x5c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rbx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x48; 0x8b; 0x5c; 0x24; 0x30;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x31; 0xcb;        (* XOR (% rbx) (% r9) *)
  0x4c; 0x21; 0xc3;        (* AND (% rbx) (% r8) *)
  0x48; 0xf7; 0xdb;        (* NEG (% rbx) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x48; 0x8b; 0x54; 0x24; 0x70;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x31; 0xda;        (* XOR (% rdx) (% r11) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x48; 0x29; 0xd3;        (* SUB (% rbx) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x0f; 0xac; 0xfd; 0x3b;
                           (* SHRD (% rbp) (% rdi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x6c; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rbp) *)
  0x48; 0x0f; 0xac; 0xdf; 0x3b;
                           (* SHRD (% rdi) (% rbx) (Imm8 (word 59)) *)
  0x48; 0xc1; 0xfb; 0x3b;  (* SAR (% rbx) (Imm8 (word 59)) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x89; 0x7c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rdi) *)
  0x48; 0x8b; 0x7c; 0x24; 0x30;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x89; 0x5c; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rbx) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x4c; 0x31; 0xef;        (* XOR (% rdi) (% r13) *)
  0x4c; 0x21; 0xe7;        (* AND (% rdi) (% r12) *)
  0x48; 0xf7; 0xdf;        (* NEG (% rdi) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd7;        (* ADC (% rdi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x48; 0x8b; 0x54; 0x24; 0x70;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x31; 0xfa;        (* XOR (% rdx) (% r15) *)
  0x4c; 0x21; 0xf2;        (* AND (% rdx) (% r14) *)
  0x48; 0x29; 0xd7;        (* SUB (% rdi) (% rdx) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd7;        (* ADC (% rdi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xf1; 0x3b;
                           (* SHRD (% rcx) (% rsi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x4c; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rcx) *)
  0x48; 0x0f; 0xac; 0xfe; 0x3b;
                           (* SHRD (% rsi) (% rdi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x74; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rsi) *)
  0x48; 0xc1; 0xff; 0x3b;  (* SAR (% rdi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x7c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rdi) *)
  0x48; 0x8b; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0x8b; 0xac; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,264))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rbx) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x89; 0xac; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rbp) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rcx) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x89; 0xb4; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% rsi) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,208))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x9c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% rbx) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,208))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x89; 0xac; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% rbp) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,216))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rcx) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,216))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x89; 0xb4; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% rsi) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,224))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rbx) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,224))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x89; 0xac; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x4c; 0x21; 0xc3;        (* AND (% rbx) (% r8) *)
  0x48; 0xf7; 0xdb;        (* NEG (% rbx) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,232))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x48; 0x29; 0xd3;        (* SUB (% rbx) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0x89; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% rdx) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x4c; 0x89; 0xe9;        (* MOV (% rcx) (% r13) *)
  0x4c; 0x21; 0xe1;        (* AND (% rcx) (% r12) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,232))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x4c; 0x89; 0xfa;        (* MOV (% rdx) (% r15) *)
  0x4c; 0x21; 0xf2;        (* AND (% rdx) (% r14) *)
  0x48; 0x29; 0xd1;        (* SUB (% rcx) (% rdx) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xca;        (* ADC (% rdx) (% rcx) *)
  0x48; 0x89; 0xb4; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% rsi) *)
  0x48; 0x89; 0x94; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% rdx) *)
  0x49; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xe0;
                           (* MOV (% r8) (Imm64 (word 16140901064495857664)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4c; 0x03; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0xc7; 0xc1; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r9) (Imm32 (word 536870911)) *)
  0x48; 0x8d; 0x40; 0xff;  (* LEA (% rax) (%% (rax,18446744073709551615)) *)
  0x4c; 0x13; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0xba; 0x00; 0x00; 0x00; 0xe0; 0xff; 0xff; 0xff; 0xdf;
                           (* MOV (% r10) (Imm64 (word 16140901063958986752)) *)
  0x4c; 0x13; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x4c; 0x8b; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x4c; 0x8b; 0xac; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0xbe; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r14) (Imm64 (word 2305843009213693951)) *)
  0x4c; 0x13; 0xb4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,176))) *)
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
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x49; 0x01; 0xde;        (* ADD (% r14) (% rbx) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0xbb; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967295)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x48; 0xb9; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584320)) *)
  0x48; 0x21; 0xc1;        (* AND (% rcx) (% rax) *)
  0x48; 0xc7; 0xc2; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm32 (word 4294967294)) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x49; 0x29; 0xd9;        (* SUB (% r9) (% rbx) *)
  0x4c; 0x89; 0x8c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r9) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x4c; 0x89; 0x94; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r10) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x4c; 0x89; 0x9c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r11) *)
  0x49; 0x19; 0xc4;        (* SBB (% r12) (% rax) *)
  0x4c; 0x89; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r12) *)
  0x49; 0x19; 0xc5;        (* SBB (% r13) (% rax) *)
  0x4c; 0x89; 0xac; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r13) *)
  0x49; 0x19; 0xc6;        (* SBB (% r14) (% rax) *)
  0x4c; 0x89; 0xb4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r14) *)
  0x49; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xe0;
                           (* MOV (% r8) (Imm64 (word 16140901064495857664)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4c; 0x03; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,192))) *)
  0x49; 0xc7; 0xc1; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r9) (Imm32 (word 536870911)) *)
  0x48; 0x8d; 0x40; 0xff;  (* LEA (% rax) (%% (rax,18446744073709551615)) *)
  0x4c; 0x13; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,200))) *)
  0x49; 0xba; 0x00; 0x00; 0x00; 0xe0; 0xff; 0xff; 0xff; 0xdf;
                           (* MOV (% r10) (Imm64 (word 16140901063958986752)) *)
  0x4c; 0x13; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,208))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,216))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x4c; 0x8b; 0xa4; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,224))) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x4c; 0x8b; 0xac; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,232))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0xbe; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r14) (Imm64 (word 2305843009213693951)) *)
  0x4c; 0x13; 0xb4; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,240))) *)
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
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x49; 0x01; 0xde;        (* ADD (% r14) (% rbx) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0xbb; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967295)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x48; 0xb9; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584320)) *)
  0x48; 0x21; 0xc1;        (* AND (% rcx) (% rax) *)
  0x48; 0xc7; 0xc2; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm32 (word 4294967294)) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x49; 0x29; 0xd9;        (* SUB (% r9) (% rbx) *)
  0x4c; 0x89; 0x8c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% r9) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x4c; 0x89; 0x94; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r10) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x4c; 0x89; 0x9c; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% r11) *)
  0x49; 0x19; 0xc4;        (* SBB (% r12) (% rax) *)
  0x4c; 0x89; 0xa4; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% r12) *)
  0x49; 0x19; 0xc5;        (* SBB (% r13) (% rax) *)
  0x4c; 0x89; 0xac; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% r13) *)
  0x49; 0x19; 0xc6;        (* SBB (% r14) (% rax) *)
  0x4c; 0x89; 0xb4; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% r14) *)
  0x48; 0x8b; 0xb4; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0x8b; 0x14; 0x24;  (* MOV (% rdx) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x40;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,64))) *)
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
  0x48; 0x89; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% rdx) *)
  0x48; 0x89; 0x9c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% rbx) *)
  0x48; 0x89; 0xbc; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% rdi) *)
  0x48; 0x89; 0x8c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% rcx) *)
  0x4c; 0x8b; 0x24; 0x24;  (* MOV (% r12) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x0f; 0xaf; 0xfc;  (* IMUL (% rdi) (% r12) *)
  0x4c; 0x0f; 0xaf; 0xe2;  (* IMUL (% r12) (% rdx) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x40;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,64))) *)
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
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x49; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% r8) *)
  0x48; 0x8b; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,304))) *)
  0x49; 0x0f; 0xaf; 0xd7;  (* IMUL (% rdx) (% r15) *)
  0x4c; 0x0f; 0xaf; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* IMUL (% r8) (Memop Quadword (%% (rsp,296))) *)
  0x4c; 0x0f; 0xaf; 0xbc; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* IMUL (% r15) (Memop Quadword (%% (rsp,312))) *)
  0x4d; 0x01; 0xc7;        (* ADD (% r15) (% r8) *)
  0x4c; 0x8d; 0x0c; 0x10;  (* LEA (% r9) (%%% (rax,0,rdx)) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x49; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% r10) *)
  0x48; 0x8b; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,304))) *)
  0x49; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% r11) *)
  0x4c; 0x0f; 0xaf; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* IMUL (% r10) (Memop Quadword (%% (rsp,296))) *)
  0x4c; 0x0f; 0xaf; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* IMUL (% r11) (Memop Quadword (%% (rsp,312))) *)
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
  0x48; 0x89; 0xb4; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% rsi) *)
  0x48; 0xff; 0x8c; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* DEC (Memop Quadword (%% (rsp,272))) *)
  0x0f; 0x85; 0x19; 0xeb; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294961945)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x40;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,64))) *)
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
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x4c; 0x89; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r12) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x4c; 0x89; 0xac; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r13) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,208))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x4c; 0x89; 0xb4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r14) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,216))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x4c; 0x89; 0xbc; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r15) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,224))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x4c; 0x89; 0xb4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r14) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,232))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x49; 0x29; 0xd1;        (* SUB (% r9) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x4c; 0x89; 0xbc; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r15) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x8c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r9) *)
  0x49; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xe0;
                           (* MOV (% r8) (Imm64 (word 16140901064495857664)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4c; 0x03; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0xc7; 0xc1; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r9) (Imm32 (word 536870911)) *)
  0x48; 0x8d; 0x40; 0xff;  (* LEA (% rax) (%% (rax,18446744073709551615)) *)
  0x4c; 0x13; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0xba; 0x00; 0x00; 0x00; 0xe0; 0xff; 0xff; 0xff; 0xdf;
                           (* MOV (% r10) (Imm64 (word 16140901063958986752)) *)
  0x4c; 0x13; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x4c; 0x8b; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x4c; 0x8b; 0xac; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x49; 0xbe; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x1f;
                           (* MOV (% r14) (Imm64 (word 2305843009213693951)) *)
  0x4c; 0x13; 0xb4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,176))) *)
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
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x49; 0x01; 0xde;        (* ADD (% r14) (% rbx) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0xbb; 0xff; 0xff; 0xff; 0xff; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294967295)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x48; 0xb9; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584320)) *)
  0x48; 0x21; 0xc1;        (* AND (% rcx) (% rax) *)
  0x48; 0xc7; 0xc2; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm32 (word 4294967294)) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x49; 0x29; 0xd9;        (* SUB (% r9) (% rbx) *)
  0x4c; 0x89; 0x8c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r9) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x4c; 0x89; 0x94; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r10) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x4c; 0x89; 0x9c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r11) *)
  0x49; 0x19; 0xc4;        (* SBB (% r12) (% rax) *)
  0x4c; 0x89; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r12) *)
  0x49; 0x19; 0xc5;        (* SBB (% r13) (% rax) *)
  0x4c; 0x89; 0xac; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r13) *)
  0x49; 0x19; 0xc6;        (* SBB (% r14) (% rax) *)
  0x4c; 0x89; 0xb4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r14) *)
  0xb8; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% eax) (Imm32 (word 4294967295)) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8d; 0x4d; 0xfe;  (* LEA (% rcx) (%% (rbp,18446744073709551614)) *)
  0x48; 0x8d; 0x55; 0xff;  (* LEA (% rdx) (%% (rbp,18446744073709551615)) *)
  0x4c; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x4c; 0x8b; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x19; 0xd4;        (* SBB (% r12) (% rdx) *)
  0x4c; 0x8b; 0xac; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* CMOVB (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x0f; 0x42; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* CMOVB (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x0f; 0x42; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* CMOVB (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x0f; 0x42; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* CMOVB (% r11) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x0f; 0x42; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* CMOVB (% r12) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x0f; 0x42; 0xac; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* CMOVB (% r13) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0x8b; 0xbc; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,320))) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0x48; 0x81; 0xc4; 0x50; 0x01; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 336)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_montinv_p384_tmc = define_trimmed "bignum_montinv_p384_tmc" bignum_montinv_p384_mc;;

let BIGNUM_MONTINV_P384_EXEC = X86_MK_CORE_EXEC_RULE bignum_montinv_p384_tmc;;

(* ------------------------------------------------------------------------- *)
(* Do the main proof for the core that is sometimes inlined elsewhere        *)
(* ------------------------------------------------------------------------- *)

let CORE_INV_P384_EXEC =
    X86_MK_EXEC_RULE
     ((GEN_REWRITE_CONV RAND_CONV [bignum_montinv_p384_tmc] THENC TRIM_LIST_CONV)
      `TRIM_LIST (17,18) bignum_montinv_p384_tmc`);;

(* ------------------------------------------------------------------------- *)
(* A localized form of the word_divstep59 proof, very similar but differing  *)
(* both in negation of the output and small register/memory details.         *)
(* ------------------------------------------------------------------------- *)

let BIT_1_WORD_ISHR = prove
 (`!x:int64. bit 1 x = bit 0 (word_ishr x 1)`,
  CONV_TAC WORD_BLAST);;

let VAL_WORD_AND_2_ISHR = prove
 (`!x:int64. val(word_and x (word 2)) = 0 <=> ~bit 0 (word_ishr x 1)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `2 = 2 EXP 1`] THEN
  REWRITE_TAC[VAL_WORD_AND_POW2; GSYM BIT_1_WORD_ISHR] THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let lemma1,lemma2 = (CONJ_PAIR o prove)
 (`(--(&2 pow 20) <= h /\ h < &2 pow 20 /\ &0 <= l /\ l < &2 pow 43
    ==> word_ishr (iword(&2 pow 43 * h + l):int64) 43 = iword h) /\
   (--(&2 pow 20) <= h /\ h < &2 pow 20 /\ &0 <= l /\ l < &2 pow 42
    ==> word_ishr (iword(&2 pow 42 * h + l):int64) 42 = iword h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ishr] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
  EXISTS_TAC `l:int` THEN ASM_REWRITE_TAC[INT_ABS_POW; INT_ABS_NUM] THEN
  REWRITE_TAC[INT_MUL_SYM] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_INT_ARITH_TAC);;

let divstep_fvec = define
 `divstep_fvec n (d,f,g) =
    divstep_f n (d,f rem &2 pow 20,g rem &2 pow 20) -
    &2 pow (41 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$1$1 -
    &2 pow (62 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$1$2`;;

let divstep_gvec = define
 `divstep_gvec n (d,f,g) =
    divstep_g n (d,f rem &2 pow 20,g rem &2 pow 20) -
    &2 pow (41 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$2$1 -
    &2 pow (62 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$2$2`;;

let divstep_dvec = define
 `divstep_dvec n (d,f,g) =
  divstep_d n (d,f rem &2 pow 20,g rem &2 pow 20)`;;

let DIVSTEP_DVEC_BOUND = prove
 (`!n d f g. abs(divstep_dvec n (d,f,g)) <= abs(d) + &2 * &n`,
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  REWRITE_TAC[divstep_dvec] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[DIVSTEP_D; GSYM INT_OF_NUM_SUC] THEN
  ASM_INT_ARITH_TAC);;

let DIVSTEP_DVEC_PARITY = prove
 (`!n d f g. divstep_dvec n (d,f,g) rem &2 = d rem &2`,
  REWRITE_TAC[divstep_dvec; DIVSTEP_D_PARITY]);;

let DIVSTEP_FVEC_PARITY = prove
 (`!n d f g.
        n <= 20
        ==> divstep_fvec n (d,f,g) rem &2 =
            divstep_f n (d,f rem &2 pow 20,g rem &2 pow 20) rem &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[divstep_fvec; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `n pow 1 divides p /\ n pow 1 divides q
    ==> (x - p * a - q * b:int == x) (mod n)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ASM_ARITH_TAC);;

let DIVSTEP_FVEC_ODD = prove
 (`!n d f g.
        n <= 20 /\ f rem &2 = &1
        ==> divstep_fvec n (d,f,g) rem &2 = &1`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DIVSTEP_FVEC_PARITY] THEN
  MATCH_MP_TAC DIVSTEP_F_ODD THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [INT_ARITH `&2:int = &2 pow 1`] THEN
  REWRITE_TAC[INT_REM_REM_POW_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[INT_POW_1]);;

let DIVSTEP_GVEC_PARITY = prove
 (`!n d f g.
        n <= 20
        ==> divstep_gvec n (d,f,g) rem &2 =
            divstep_g n (d,f rem &2 pow 20,g rem &2 pow 20) rem &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[divstep_gvec; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `n pow 1 divides p /\ n pow 1 divides q
    ==> (x - p * a - q * b:int == x) (mod n)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ASM_ARITH_TAC);;

let DIVSTEP_DVEC = prove
 (`(!d f g. divstep_dvec 0 (d,f,g) = d) /\
   (!n t. n <= 20
          ==> divstep_dvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then &2 - divstep_dvec n t else &2 + divstep_dvec n t)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_dvec; DIVSTEP_D] THEN
  SIMP_TAC[DIVSTEP_GVEC_PARITY]);;

let DIVSTEP_FVEC = prove
 (`(!d f g. divstep_fvec 0 (d,f,g) = f rem &2 pow 20 - &2 pow 41) /\
   (!n t. n <= 20
          ==> divstep_fvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then divstep_gvec n t else divstep_fvec n t)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_fvec; DIVSTEP_F; divstep_mat] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  CONJ_TAC THENL [CONV_TAC INT_ARITH; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `d:int`; `f:int`; `g:int`] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[DIVSTEP_GVEC_PARITY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[divstep_dvec; divstep_gvec] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 41 - n = (41 - SUC n) + 1`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 62 - n = (62 - SUC n) + 1`] THEN
  REWRITE_TAC[INT_POW_ADD; INT_POW_1; GSYM INT_MUL_ASSOC] THEN
  SIMP_TAC[imat_mul; VECTOR_2; ISUM_2; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  INT_ARITH_TAC);;

let DIVSTEP_GVEC = prove
 (`(!d f g. divstep_gvec 0 (d,f,g) = g rem &2 pow 20 - &2 pow 62) /\
   (!n t. n <= 20
          ==> divstep_gvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then (divstep_gvec n t - divstep_fvec n t) div &2
              else (divstep_gvec n t +
                    divstep_gvec n t rem &2 * divstep_fvec n t) div &2)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_gvec; DIVSTEP_G; divstep_mat] THEN
  REWRITE_TAC[GSYM divstep_gvec] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  CONJ_TAC THENL [CONV_TAC INT_ARITH; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `d:int`; `f:int`; `g:int`] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[DIVSTEP_GVEC_PARITY] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[divstep_dvec; divstep_fvec; divstep_gvec] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 41 - n = 1 + (41 - SUC n)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 62 - n = 1 + (62 - SUC n)`] THEN
  REWRITE_TAC[INT_POW_ADD; INT_POW_1; GSYM INT_MUL_ASSOC] THEN
  REWRITE_TAC[INT_ARITH
   `(x - &2 * y - &2 * z) - (x' - &2 * y' - &2 * z'):int =
    (x - x') + &2 * ((y' + z') - (y + z))`] THEN
  REWRITE_TAC[INT_ARITH
   `(x - &2 * y - &2 * z) + b * (x' - &2 * y' - &2 * z'):int =
    (x + b * x') + &2 * --(b * (y' + z') + (y + z))`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_OF_NUM_EQ; ARITH_EQ] THEN
  SIMP_TAC[imat_mul; VECTOR_2; ISUM_2; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  INT_ARITH_TAC);;

let DIVSTEP_FGVEC_PACK = prove
 (`!d f g. word_or (word_and (iword f) (word 1048575))
                   (word 18446741874686296064):int64 =
           iword(divstep_fvec 0 (d,f,g)) /\
           word_or (word_and (iword g) (word 1048575))
                   (word 13835058055282163712):int64 =
           iword(divstep_gvec 0 (d,f,g))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC;
              DIVSTEP_F; DIVSTEP_G; divstep_mat] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  W(MP_TAC o PART_MATCH (rand o rand) WORD_ADD_OR o lhand o snd) THEN
  (ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  REWRITE_TAC[INT_SUB] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[IWORD_INT_ADD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_AND_MASK_WORD; GSYM(NUM_REDUCE_CONV `2 EXP 20 - 1`)] THEN
  REWRITE_TAC[WORD_IWORD; IWORD_EQ; GSYM INT_OF_NUM_CLAUSES; DIMINDEX_64] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC INT_EQ_IMP_CONG THEN REWRITE_TAC[INT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN REWRITE_TAC[VAL_IWORD_CONG] THEN
  REWRITE_TAC[DIMINDEX_64; GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REDUCE_CONV);;

let IVAL_IWORD_DVEC = prove
 (`!n d f g.
        abs(d) < &2 pow 63 - &2 * &n
        ==> ival(iword(divstep_dvec n (d,f,g)):int64) =
            divstep_dvec n (d,f,g)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`n:num`; `d:int`; `f:int`; `g:int`] DIVSTEP_DVEC_BOUND) THEN
  ASM_INT_ARITH_TAC);;

let DIVSTEP_FVEC_BOUNDS,DIVSTEP_GVEC_BOUNDS = (CONJ_PAIR o prove)
 (`(!n d f g.
        n <= 20
        ==> --(&2 pow 62) <= divstep_fvec n (d,f,g) /\
            divstep_fvec n (d,f,g) < &2 pow 62) /\
   (!n d f g.
        n <= 20
        ==> --(&2 pow 62) <= divstep_gvec n (d,f,g) /\
            divstep_gvec n (d,f,g) < &2 pow 62)`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  REWRITE_TAC[divstep_dvec] THEN INDUCT_TAC THENL
   [REWRITE_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC; ARITH] THEN
    MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_DIVISION) THEN
    MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_DIVISION) THEN
    INT_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o MATCH_MP
     (ARITH_RULE `SUC n <= 20 ==> n <= 20`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_SIMP_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC] THEN STRIP_TAC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_LE_DIV_EQ; INT_DIV_LT_EQ;  INT_ARITH `(&0:int) < &2`] THEN
  DISJ_CASES_THEN SUBST1_TAC
   (SPEC `divstep_gvec n (d,f,g)` INT_REM_2_CASES) THEN
  ASM_INT_ARITH_TAC);;

let PACKED_DIVSTEP_TAC n shf s =
  let s' = if mem n shf then s+7 else s+12 in
  X86_STEPS_TAC CORE_INV_P384_EXEC (s--s') THEN
  SUBGOAL_THEN
   (subst [mk_small_numeral(n-1),`n:num`;
           mk_var("s"^string_of_int s',`:x86state`),`s:x86state`]
     `read RSI s = iword(divstep_dvec (SUC n) (d,f,g)) /\
      read RBX s = iword(divstep_fvec (SUC n) (d,f,g)) /\
      read RCX s = iword(divstep_gvec (SUC n) (d,f,g))`)
  MP_TAC THENL
   [ASM_REWRITE_TAC[WORD_AND_1_BITVAL] THEN
    REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_EQ_0] THEN
    SIMP_TAC(ARITH::map CONJUNCT2
     [DIVSTEP_DVEC; DIVSTEP_FVEC; DIVSTEP_GVEC]) THEN
    REWRITE_TAC[COND_SWAP; INT_ARITH `~(x:int < &0) <=> x >= &0`] THEN
    REWRITE_TAC[BIT_LSB_IWORD] THEN
    MP_TAC(ISPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
      IVAL_IWORD_DVEC) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
       `abs(d:int) < a ==> a <= b ==> abs(d) < b`)) THEN
      CONV_TAC INT_ARITH;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[WORD_RULE `word_sub x y = word_add (word_neg y) x`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[MESON[]
     `(if p /\ q then x else y) =
      (if p then if q then x else y else y)`] THEN
    REWRITE_TAC[COND_SWAP; INT_ARITH `x:int < &0 <=> ~(x >= &0)`] THEN
    DISJ_CASES_THEN SUBST1_TAC
       (SPEC(subst [mk_small_numeral(n - 1),`n:num`] `divstep_gvec n (d,f,g)`)
          INT_REM_2_CASES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_MUL_LID; INT_ADD_RID] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[WORD_XOR_0; WORD_ADD_0; WORD_BLAST
     `word_xor (x:int64) (word 18446744073709551614) =
      word_sub (word_neg x) (word_shl (word(bitval(~bit 0 x))) 1)`] THEN
    REWRITE_TAC[BIT_LSB_IWORD] THEN
    ASM_SIMP_TAC[DIVSTEP_FVEC_ODD; DIVSTEP_DVEC_PARITY; ARITH_LT; ARITH_LE;
                 BITVAL_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    REWRITE_TAC[word_ishr; WORD_SUB_0] THEN AP_TERM_TAC THEN
    REWRITE_TAC[WORD_ADD_0; INT_POW_1; MULT_CLAUSES; WORD_VAL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[WORD_RULE `word_add x (word_neg y) = word_sub x y`] THEN
    REWRITE_TAC[GSYM IWORD_INT_ADD; GSYM IWORD_INT_SUB] THEN
    MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    MP_TAC(SPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
     DIVSTEP_FVEC_BOUNDS) THEN
    MP_TAC(SPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
     DIVSTEP_GVEC_BOUNDS) THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read RCX s = x`) o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read RBX s = x`) o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read RSI s = x`) o concl)) THEN
    RULE_ASSUM_TAC(PURE_REWRITE_RULE [VAL_WORD_AND_2_ISHR]) THEN
    REPLICATE_TAC 3 (DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_SUC_CONV)) THEN
    DISCH_THEN(fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN STRIP_ASSUME_TAC th)];;

let RENAME_DFG_TAC d0 f0 g0 =
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`f:int`,f0) THEN
  SPEC_TAC(`g:int`,g0) THEN
  SPEC_TAC(`d:int`,d0) THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read RSI s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read R12 s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read R13 s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th));;

let DIVSTEP_MAT_UNPACK_20 = prove
 (`word_ishr
    (word_shl (word_add (iword (divstep_fvec 20 (d,f,g))) (word 1048576)) 22)
    43:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$1$1)) /\
   word_ishr (word_add (iword (divstep_fvec 20 (d,f,g))) (word 2199024304128))
             42:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$1$2)) /\
   word_ishr
    (word_shl (word_add (iword (divstep_gvec 20 (d,f,g))) (word 1048576)) 22)
    43:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$2$1)) /\
   word_ishr (word_add (iword (divstep_gvec 20 (d,f,g))) (word 2199024304128))
             42:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$2$2))`,
  REWRITE_TAC[WORD_RULE `word_add (iword x) (word y) = iword(x + &y)`] THEN
  REWRITE_TAC[WORD_SHL_IWORD] THEN
  REWRITE_TAC[divstep_fvec; divstep_gvec] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_ARITH
   `&2 pow 22 * (l - &2 pow 21 * m - &2 pow 42 * h + z):int =
    &2 pow 64 * --h + &2 pow 43 * --m + &2 pow 22 * (l + z)`] THEN
  REWRITE_TAC[INT_ARITH
   `l - &2 pow 21 * m - &2 pow 42 * h + z:int =
    &2 pow 42 * --h + &2 pow 21 * --m + (l + z)`] THEN
  ONCE_REWRITE_TAC[GSYM IWORD_REM_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64; INT_REM_MUL_ADD] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; IWORD_REM_SIZE] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC lemma1 ORELSE MATCH_MP_TAC lemma2) THEN
  MP_TAC(SPECL [`20`; `(d:int,f rem &2 pow 20,g rem &2 pow 20)`]
        DIVSTEP_MAT_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `20`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_F_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `20`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_G_BOUNDS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let DIVSTEP_MAT_UNPACK_19 = prove
 (`word_ishr
    (word_shl (word_add (iword (divstep_fvec 19 (d,f,g))) (word 1048576)) 21)
    43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$1$1)) /\
   word_ishr (word_add (iword(divstep_fvec 19 (d,f,g)):int64)
                       (word 2199024304128)) 43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$1$2)) /\
   word_ishr
    (word_shl (word_add (iword (divstep_gvec 19 (d,f,g))) (word 1048576)) 21)
    43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$2$1)) /\
   word_ishr (word_add (iword(divstep_gvec 19 (d,f,g)):int64)
                       (word 2199024304128)) 43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$2$2))`,
  REWRITE_TAC[WORD_RULE `word_add (iword x) (word y) = iword(x + &y)`] THEN
  REWRITE_TAC[WORD_SHL_IWORD] THEN
  REWRITE_TAC[divstep_fvec; divstep_gvec] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_ARITH
   `&2 pow 21 * (l - &2 pow 22 * m - &2 pow 43 * h + z):int =
    &2 pow 64 * --h + &2 pow 43 * --m + &2 pow 21 * (l + z)`] THEN
  REWRITE_TAC[INT_ARITH
   `l - &2 pow 22 * m - &2 pow 43 * h + z:int =
    &2 pow 43 * --h + &2 pow 22 * --m + (l + z)`] THEN
  ONCE_REWRITE_TAC[GSYM IWORD_REM_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64; INT_REM_MUL_ADD] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; IWORD_REM_SIZE] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC lemma1 THEN
  MP_TAC(SPECL [`19`; `(d:int,f rem &2 pow 20,g rem &2 pow 20)`]
        DIVSTEP_MAT_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `19`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_F_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `19`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_G_BOUNDS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let LOCAL_WORD_DIVSTEP59_CORRECT = prove
 (`!d f g stackpointer pc.
   nonoverlapping (stackpointer,336) (word pc,0x19aa)
   ==> ensures x86
        (\s. bytes_loaded s (word pc)
                  (TRIM_LIST (17,18) bignum_montinv_p384_tmc) /\
             read RIP s = word(pc + 0x8f4) /\
             read RSP s = stackpointer /\
             read (memory :> bytes64(word_add stackpointer (word 280))) s =
             d /\
             read (memory :> bytes64 stackpointer) s = f /\
             read (memory :> bytes64(word_add stackpointer (word 64))) s = g)
        (\s. read RIP s = word(pc + 0x1616) /\
             (ival d rem &2 = &1 /\
              ival f rem &2 = &1 /\
              abs(ival d) < &2 pow 62
          ==> read RSI s = iword(divstep_d 59 (ival d,ival f,ival g)) /\
              let M = divstep_mat 59 (ival d,ival f,ival g) in
              read R8 s = iword(--(M$1$1)) /\
              read R10 s = iword(--(M$1$2)) /\
              read R12 s = iword(--(M$2$1)) /\
              read R14 s = iword(--(M$2$2))))
          (MAYCHANGE [RIP; RDI; RSI; RAX; RBX; RCX; RDX; RBP;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(word_add stackpointer (word 288),32)] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY
    (fun t -> GEN_REWRITE_TAC I [FORALL_IVAL_GEN] THEN
              X_GEN_TAC t THEN STRIP_TAC)
    [`d:int`; `f:int`; `g:int`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`]) THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  STRIP_TAC THEN

  (*** Globalize the odd(d), odd(f) and |d| < 2^62 assumption ***)

  ASM_CASES_TAC `d rem &2 = &1 /\ f rem &2 = &1 /\ abs(d:int) < &2 pow 62` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    X86_QUICKSIM_TAC CORE_INV_P384_EXEC [`read RSP s = x`] (1--898)] THEN

  (*** The first packing ***)

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC CORE_INV_P384_EXEC (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read RSI s = a ==> !x. a = x ==> read RSI s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The first block of 20 divsteps ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (11--20) THEN
  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [20] (13*n+8)) (1--20) THEN

  (*** The unpacking of the first block ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (276--291) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_20]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** Application of first update matrix to f and g ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (292--301) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_ishr]) THEN

  (*** Renaming new values and checking d bound ***)

  SUBGOAL_THEN
    `abs(divstep_d 20 (d,f,g)) < &2 pow 62 + &40`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`20`; `d:int`; `f:int`; `g:int`] DIVSTEP_D_BOUND) THEN
    UNDISCH_TAC `abs(d:int) < &2 pow 62` THEN CONV_TAC INT_ARITH;
    ALL_TAC] THEN
  RENAME_DFG_TAC `d0:int` `f0:int` `g0:int` THEN

  (*** Get congruences on the new f and g, and prove oddness ***)

  SUBGOAL_THEN `d rem &2 = &1` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[DIVSTEP_D_PARITY] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(divstep_f 20 (d0,f0,g0) == --f) (mod (&2 pow 40)) /\
    (divstep_g 20 (d0,f0,g0) == --g) (mod (&2 pow 40))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`d0:int`; `f0:int`; `g0:int`; `20`] DIVSTEP_MAT) THEN
    ASM_SIMP_TAC[CART_EQ; FORALL_2; VECTOR_2; imat_vmul;
                 DIMINDEX_2; LAMBDA_BETA; ISUM_2] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
    SIMP_TAC[GSYM IWORD_INT_NEG; GSYM IWORD_INT_ADD; GSYM IWORD_INT_MUL] THEN
    SIMP_TAC[INT_ARITH `f * --m + --n * g:int = --(m * f + n * g)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [INT_ADD_SYM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(a:int == --b) (mod p) <=> (b == --a) (mod p)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_CONG_DIV THEN
    (CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[INT_MUL_RNEG] THEN MATCH_MP_TAC(INTEGER_RULE
     `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN
    REWRITE_TAC[IVAL_IWORD_CONG; GSYM INT_POW_ADD] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `f rem &2 = &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INT_REM_2_NEG] THEN
    TRANS_TAC EQ_TRANS `divstep_f 20 (d0,f0,g0) rem &2` THEN
    REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[DIVSTEP_F_ODD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(d:int == f) (mod p) ==> q pow 1 divides p ==> (f == d) (mod q)`)) THEN
    MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The second packing ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (302--309) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read RSI s = a ==> !x. a = x ==> read RSI s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The second block of 20 divsteps ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (310--318) THEN
  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [20] (13*n+306)) (1--20) THEN

  (*** The unpacking of the second block ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (574--585) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_20]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** Application of second update matrix to f and g ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (586--595) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_ishr]) THEN

  (*** Renaming new values and checking d bound ***)

  SUBGOAL_THEN
    `abs(divstep_d 20 (d,f,g)) < &2 pow 62 + &80`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`20`; `d:int`; `f:int`; `g:int`] DIVSTEP_D_BOUND) THEN
    UNDISCH_TAC `abs(d:int) < &2 pow 62 + &40` THEN CONV_TAC INT_ARITH;
    ALL_TAC] THEN
  RENAME_DFG_TAC `d1:int` `f1:int` `g1:int` THEN

  (*** Get congruences on the new f and g, and prove oddness ***)

  SUBGOAL_THEN `d rem &2 = &1` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[DIVSTEP_D_PARITY] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(divstep_f 20 (d1,f1,g1) == --f) (mod (&2 pow 40)) /\
    (divstep_g 20 (d1,f1,g1) == --g) (mod (&2 pow 40))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`d1:int`; `f1:int`; `g1:int`; `20`] DIVSTEP_MAT) THEN
    ASM_SIMP_TAC[CART_EQ; FORALL_2; VECTOR_2; imat_vmul;
                 DIMINDEX_2; LAMBDA_BETA; ISUM_2] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
    SIMP_TAC[GSYM IWORD_INT_NEG; GSYM IWORD_INT_ADD; GSYM IWORD_INT_MUL] THEN
    SIMP_TAC[INT_ARITH `f * --m + g * --n:int = --(m * f + n * g)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [INT_ADD_SYM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(a:int == --b) (mod p) <=> (b == --a) (mod p)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_CONG_DIV THEN
    (CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[INT_MUL_RNEG] THEN MATCH_MP_TAC(INTEGER_RULE
     `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN
    REWRITE_TAC[IVAL_IWORD_CONG; GSYM INT_POW_ADD] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `f rem &2 = &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INT_REM_2_NEG] THEN
    TRANS_TAC EQ_TRANS `divstep_f 20 (d1,f1,g1) rem &2` THEN
    REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[DIVSTEP_F_ODD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(d:int == f) (mod p) ==> q pow 1 divides p ==> (f == d) (mod q)`)) THEN
    MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The third and final packing ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (596--603) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read RSI s = a ==> !x. a = x ==> read RSI s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The multiplication of the first two matrices ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (604--619) THEN

  (*** The last 19 divsteps ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (620--628) THEN
  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [19] (13*n+616)) (1--19) THEN

  (*** The final unpacking is a little different as it's 19 not 20 ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (871--882) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_19]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** The final matrix multiplication and writeback ***)

  X86_STEPS_TAC CORE_INV_P384_EXEC (883--898) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s898" THEN

  (*** The ending mathematics ***)

  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[IWORD_IVAL; IWORD_INT_SUB; IWORD_INT_NEG; IWORD_INT_ADD;
           IWORD_INT_MUL; WORD_ADD; WORD_MUL; ADD_CLAUSES; WORD_VAL] THEN
  REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_MUL; GSYM IWORD_INT_ADD;
              GSYM IWORD_INT_SUB; GSYM IWORD_INT_NEG] THEN
  SUBGOAL_THEN
   `divstep_d 59 (d0,f0,g0) = divstep_d 19 (d,f,g) /\
    divstep_mat 59 (d0,f0,g0) =
    imat_mul (divstep_mat 19 (d,f,g))
             (imat_mul (divstep_mat 20 (d1,f1,g1))
                       (divstep_mat 20 (d0,f0,g0)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[ARITH_RULE `59 = 19 + 40`; DIVSTEP_MAT_ADD; DIVSTEP_DFG_ADD];
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[imat_mul; LAMBDA_BETA; DIMINDEX_2; ARITH; ISUM_2] THEN
    INT_ARITH_TAC] THEN
  SUBGOAL_THEN
   `divstep_d 40 (d0,f0,g0) = d /\
    (divstep_f 40 (d0,f0,g0) == f) (mod (&2 pow 19)) /\
    (divstep_g 40 (d0,f0,g0) == g) (mod (&2 pow 19)) /\
    divstep_mat 40 (d0,f0,g0) =
    imat_mul (divstep_mat 20 (d1,f1,g1))
             (divstep_mat 20 (d0,f0,g0))`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[ARITH_RULE `59 = 19 + 40`;
                    DIVSTEP_MAT_ADD; DIVSTEP_DFG_ADD] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIVSTEP_D_CONGRUENCE;
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC DIVSTEP_MAT_CONGRUENCE] THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL
   [`40`; `d1:int`; `divstep_f 20 (d0,f0,g0)`; `divstep_g 20 (d0,f0,g0)`;
    `f1:int`; `g1:int`; `20`]
   DIVSTEP_CONGRUENCE_NEG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[DIVSTEP_F_ODD]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `40 = 20 + 20`;
                  DIVSTEP_DFG_ADD; DIVSTEP_MAT_ADD] THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
   `(x:int == y) (mod p) ==> (y == z) (mod p) /\ q divides p
    ==> (x == z) (mod q)`)) THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(--x:int == y) (mod p) <=> (x == --y) (mod p)`] THEN
  SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
   `(x:int == y) (mod p) ==> q divides p ==> (x == y) (mod q)`)) THEN
  SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT]);;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let PRIME_P384 = time prove
 (`prime p_384`,
  REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "41"; "43"; "47";
   "59"; "61"; "67"; "73"; "79"; "97"; "131"; "139"; "157"; "181"; "211";
   "233"; "263"; "271"; "293"; "599"; "661"; "881"; "937"; "1033"; "1373";
   "1579"; "2213"; "3253"; "3517"; "6317"; "8389"; "21407"; "38557";
   "312289"; "336757"; "363557"; "568151"; "6051631"; "105957871";
   "246608641"; "513928823"; "532247449"; "2862218959"; "53448597593";
   "807145746439"; "44925942675193"; "1357291859799823621";
   "529709925838459440593"; "35581458644053887931343";
   "23964610537191310276190549303"; "862725979338887169942859774909";
   "20705423504133292078628634597817";
   "413244619895455989650825325680172591660047";
   "12397338596863679689524759770405177749801411";
   "19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097"]);;

let IWORD_CASES_LEMMA = prove
 (`!m:int64.
        word_sub (word_xor m (word_ishr m 63)) (word_ishr m 63) =
        if ival m < &0 then word_neg m else m`,
  GEN_TAC THEN MP_TAC(ISPEC `m:int64` WORD_ISHR_MSB) THEN
  REWRITE_TAC[DIMINDEX_64; GSYM MSB_IVAL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_XOR_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_RULE);;

let IWORD_CASES_ABS_ALT = prove
 (`!m. (if m < &0 then word_neg(iword m) else iword m) = iword(abs m)`,
  GEN_TAC THEN REWRITE_TAC[GSYM IWORD_INT_NEG] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ASM_INT_ARITH_TAC);;

let WORD_AND_ISHR_CASES = prove
 (`!x y:int64. word_and (word_ishr x 63) y =
               if ival x < &0 then y else word 0`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `x:int64` WORD_ISHR_MSB) THEN
  REWRITE_TAC[MSB_IVAL] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_AND_MASK]);;

let TWOS_COMPLEMENT_448 = prove
 (`(&(bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6]) == x) (mod (&2 pow 448))
   ==> --(&2 pow 384) <= x /\ x:int < &2 pow 384
       ==> ?b. n6 = word_neg(word(bitval b)) /\
               x = &(bignum_of_wordlist[n0;n1;n2;n3;n4;n5]) -
                   &2 pow 384 * &(bitval b)`,
  REWRITE_TAC[ARITH_RULE `448 = 384 + 64`] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] TWOS_COMPLEMENT_GEN)) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(6,1)] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `x:int < &0` THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM VAL_EQ]; CONV_TAC INT_ARITH] THEN
  ASM_REWRITE_TAC[VAL_WORD_MASK; DIMINDEX_64] THEN ARITH_TAC);;

let TWOS_COMPLEMENT_448_WEAK = prove
 (`(&(bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6]) == x) (mod (&2 pow 448))
   ==> --(&2 pow 447) <= x /\ x:int < &2 pow 447
       ==> &(bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6]) =
           x + &2 pow 448 * &(bitval(bit 63 n6))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] TWOS_COMPLEMENT)) THEN
  ASM_REWRITE_TAC[ARITH_EQ; NUM_REDUCE_CONV `448 - 1`] THEN
  ANTS_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VAL_EXPAND_CONV) THEN
  SIMP_TAC[EXP; MULT_CLAUSES; INT_EQ_SUB_RADD]);;

let swlemma = WORD_RULE
  `word_add (word_shl x 32) x:int64 = word(4294967297 * val x)`;;

let mmlemma_alt = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &18446744069414584321 * &(val(word(4294967297 * val x):int64))
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(4294967297 * val x):int64)) * &18446744069414584321`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let CORE_INV_P384_CORRECT = time prove
 (`!z x n pc stackpointer.
        ALL (nonoverlapping (stackpointer,336))
            [(word pc,0x19aa); (z,8 * 6); (x,8 * 6)] /\
        nonoverlapping (word pc,0x19aa) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    (TRIM_LIST (17,18) bignum_montinv_p384_tmc) /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = word (pc + 0x19aa) /\
                  bignum_from_memory(z,6) s =
                  (if p_384 divides n then 0
                   else (2 EXP 768 * inverse_mod p_384 n) MOD p_384))
          (MAYCHANGE [RIP; RDI; RSI; RAX; RBX; RCX; RDX; RBP;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(z,8 * 6);
                      memory :> bytes(stackpointer,336)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Abbreviate the starting tuple for divstep ***)

  ABBREV_TAC `t:int#int#int = (&1,&p_384,&n rem &p_384)` THEN

  (*** Set up the main loop invariant ***)

  ENSURES_WHILE_UP_TAC `14` `pc + 0x8f4` `pc + 0x8f4`
   `\i s.
      read RSP s = stackpointer /\
      read (memory :> bytes64(word_add stackpointer (word 320))) s = z /\
      read (memory :> bytes64(word_add stackpointer (word 272))) s =
      word(15 - i) /\
      read (memory :> bytes64(word_add stackpointer (word 280))) s =
      iword(divstep_d (59 * i) t) /\
      (&(read (memory :> bytes(stackpointer,8 * 7)) s) ==
       --(&1) pow i * divstep_f (59 * i) t) (mod (&2 pow 448)) /\
      (&(read (memory :> bytes(word_add stackpointer (word 64),8 * 7)) s) ==
       --(&1) pow i * divstep_g (59 * i) t) (mod (&2 pow 448)) /\
      (&2 pow (843 - 5 * i) * --(&1) pow i * divstep_f (59 * i) t ==
       &n * &(read (memory :> bytes(word_add stackpointer (word 128),8 * 6)) s))
      (mod (&p_384)) /\
      (&2 pow (843 - 5 * i) * --(&1) pow i * divstep_g (59 * i) t ==
       &n * &(read (memory :> bytes(word_add stackpointer (word 192),8 * 6)) s))
      (mod (&p_384)) /\
     (p_384 divides n
      ==> p_384 divides
          read(memory :> bytes(word_add stackpointer (word 128),8 * 6)) s)`
  THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    BIGNUM_TERMRANGE_TAC `6` `n:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN
    X86_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [16;18;20;22;24;26] (1--59) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[DIVSTEP_D; DIVSTEP_F; DIVSTEP_G; GSYM WORD_IWORD] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s56" THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES; p_384;
                GSYM INT_REM_EQ] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[DIVIDES_0] THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INT_REM_REM; INT_MUL_RID; GSYM p_384; INT_MUL_LID] THEN
    CONJ_TAC THENL [AP_THM_TAC THEN AP_TERM_TAC; REWRITE_TAC[INT_MUL_SYM]] THEN
    REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN MAP_EVERY EXISTS_TAC
     [`64 * 6`; `if n < p_384 then &n else &n - &p_384:real`] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[p_384] THEN ARITH_TAC;
      REWRITE_TAC[p_384] THEN ARITH_TAC;
      ALL_TAC;
      SIMP_TAC[GSYM NOT_LE; COND_SWAP; REAL_OF_NUM_SUB; GSYM COND_RAND] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN
      MATCH_MP_TAC MOD_CASES THEN REWRITE_TAC[p_384] THEN ASM_ARITH_TAC] THEN
    SUBGOAL_THEN `carry_s26 <=> n < p_384` (SUBST1_TAC o SYM) THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `384` THEN
      EXPAND_TAC "n" THEN REWRITE_TAC[REAL_BITVAL_NOT] THEN
      REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD; p_384;
                  GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(BINOP_CONV(BINOP_CONV REAL_POLY_CONV)) THEN BOUNDER_TAC[];
      EXPAND_TAC "n" THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];

    (*** Main invariant proof ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `f:num` `read (memory :> bytes (stackpointer,8 * 7))` THEN
    GHOST_INTRO_TAC `g:num`
     `read (memory :> bytes (word_add stackpointer (word 64),8 * 7))` THEN
    GHOST_INTRO_TAC `u:num`
     `read (memory :> bytes (word_add stackpointer (word 128),8 * 6))` THEN
    GHOST_INTRO_TAC `v:num`
     `read (memory :> bytes (word_add stackpointer (word 192),8 * 6))` THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    MAP_EVERY (BIGNUM_TERMRANGE_TAC `7`) [`f:num`; `g:num`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "f_"
     `read (memory :> bytes(stackpointer,8 * 7)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "g_"
     `read (memory :> bytes(word_add stackpointer (word 64),8 * 7)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "u_"
     `read (memory :> bytes(word_add stackpointer (word 128),8 * 6)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "v_"
     `read (memory :> bytes(word_add stackpointer (word 192),8 * 6)) s0` THEN

    MP_TAC(SPECL
     [`iword (divstep_d (59 * i) t):int64`;
      `f_0:int64`; `g_0:int64`; `stackpointer:int64`; `pc:num`]
     LOCAL_WORD_DIVSTEP59_CORRECT) THEN
    ASM_REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
    X86_BIGSTEP_TAC CORE_INV_P384_EXEC "s1" THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN

    SUBGOAL_THEN `ival(f_0:int64) rem &2 = &1` ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS `(--(&1) pow i * divstep_f (59 * i) t) rem &2` THEN
      EXPAND_TAC "t" THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[INT_REM_EQ];
        ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
        ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN
        CONV_TAC INT_REDUCE_CONV THEN CONV_TAC INT_REM_DOWN_CONV THEN
        REWRITE_TAC[INT_POW_ONE; INT_MUL_LID] THEN
        MATCH_MP_TAC DIVSTEP_F_ODD THEN REWRITE_TAC[p_384] THEN
        CONV_TAC INT_REDUCE_CONV] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
       `(z:int == y) (mod q)
        ==> !r. (p divides q /\ p divides r) /\ (z == x) (mod r)
                ==> (x == y) (mod p)`)) THEN
      EXISTS_TAC `(&2:int) pow 64` THEN REWRITE_TAC[GSYM INT_REM_EQ_0] THEN
      CONJ_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
      EXPAND_TAC "f" THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; GSYM INT_OF_NUM_POW] THEN
      REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG] THEN
      REWRITE_TAC[DIMINDEX_64; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      SIMP_TAC[VAL_BOUND_64; MOD_LT];
      ALL_TAC] THEN

    SUBGOAL_THEN `abs(divstep_d (59 * i) t) < &2 pow 62` ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN W(MP_TAC o
       PART_MATCH (lhand o rand o lhand) DIVSTEP_D_BOUND o lhand o snd) THEN
      MATCH_MP_TAC(INT_ARITH
       `e:int < &59 * &14
        ==> abs(x - abs(&1)) <= &2 * e ==> x < &2 pow 62`) THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ival(iword(divstep_d (59 * i) t):int64) = divstep_d (59 * i) t`
    SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
      ASM_REWRITE_TAC[]] THEN
    ANTS_TAC THENL
     [EXPAND_TAC "t" THEN REWRITE_TAC[DIVSTEP_D_PARITY] THEN
      CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN

    SUBGOAL_THEN
     `divstep_d 59 (divstep_d (59 * i) t,ival(f_0:int64),ival(g_0:int64)) =
      divstep_d (59 * (i + 1)) t`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `59 * (i + 1) = 59 + 59 * i`] THEN
      TRANS_TAC EQ_TRANS
       `divstep_d 59 (divstep_d (59 * i) t,
                      --(&1) pow i * ival(f_0:int64),
                      --(&1) pow i * ival(g_0:int64))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN
        COND_CASES_TAC THEN REWRITE_TAC[INT_MUL_LNEG; INT_MUL_LID] THEN
        ASM_SIMP_TAC[DIVSTEP_D_NEG];
        ALL_TAC] THEN
      REWRITE_TAC[DIVSTEP_DFG_ADD] THEN
      MATCH_MP_TAC DIVSTEP_D_CONGRUENCE THEN CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
       `(z:int == i * y) (mod q)
        ==> !r. (p divides q /\ p divides r) /\ (z == x) (mod r) /\
                i pow 2 = &1
                ==> (i * x == y) (mod p)`)) THEN
      EXISTS_TAC `(&2:int) pow 64` THEN
      SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
      REWRITE_TAC[INT_POW_POW] THEN
      REWRITE_TAC[INT_POW_NEG; EVEN_MULT; ARITH_EVEN; INT_POW_ONE] THEN
      MAP_EVERY EXPAND_TAC ["f"; "g"] THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; GSYM INT_OF_NUM_POW] THEN
      REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG] THEN
      REWRITE_TAC[DIMINDEX_64; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      SIMP_TAC[VAL_BOUND_64; MOD_LT];
      ALL_TAC] THEN

    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV let_CONV)) THEN
    MAP_EVERY ABBREV_TAC
     [`mm = divstep_mat 59
             (divstep_d (59 * i) t,ival(f_0:int64),ival(g_0:int64))`;
      `m00 = --((mm:int^2^2)$1$1)`;
      `m01 = --((mm:int^2^2)$1$2)`;
      `m10 = --((mm:int^2^2)$2$1)`;
      `m11 = --((mm:int^2^2)$2$2)`] THEN
    STRIP_TAC THEN

    (*** The trivial fact that we loop back ***)

    X86_STEPS_TAC CORE_INV_P384_EXEC (2--4) THEN
    SUBGOAL_THEN
     `word_sub (word (15 - i)) (word 1):int64 = word(15 - (i + 1))`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[ARITH_RULE `15 - (i + 1) = (15 - i) - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 14 ==> 1 <= 15 - i`];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(val(word(15 - (i + 1)):int64) = 0)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL
     [VAL_INT64_TAC `15 - (i + 1)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `i < 14` THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** Sign-magnitude breakdown of matrix entries ***)

    X86_STEPS_TAC CORE_INV_P384_EXEC (5--20) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IWORD_CASES_LEMMA]) THEN

    SUBGOAL_THEN
     `abs(m00:int) <= &2 pow 59 /\
      abs(m01:int) <= &2 pow 59 /\
      abs(m10:int) <= &2 pow 59 /\
      abs(m11:int) <= &2 pow 59`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m00"; "m01"; "m10"; "m11"; "mm"] THEN
      REWRITE_TAC[INT_ABS_NEG] THEN
      SIMP_TAC[INT_ABS_BOUNDS; DIVSTEP_MAT_BOUNDS; INT_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ival(iword m00:int64) = m00 /\
      ival(iword m01:int64) = m01 /\
      ival(iword m10:int64) = m10 /\
      ival(iword m11:int64) = m11`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN STRIP_ASSUME_TAC th)
    THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[INT_ARITH
       `abs(m:int) <= &2 pow 59 ==> --(&2 pow 63) <= m /\ m < &2 pow 63`];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `ival(word_neg(iword m00:int64)) = --m00 /\
      ival(word_neg(iword m01:int64)) = --m01 /\
      ival(word_neg(iword m10:int64)) = --m10 /\
      ival(word_neg(iword m11:int64)) = --m11`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN STRIP_ASSUME_TAC th)
    THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      MATCH_MP_TAC(WORD_ARITH
       `!x:N word. abs(ival(x)) < &2 pow (dimindex(:N) - 1)
                   ==> ival(word_neg x) = --ival x`) THEN
      ASM_REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
      MATCH_MP_TAC(INT_ARITH `x:int <= &2 pow 59 ==> x < &2 pow 63`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    RULE_ASSUM_TAC(REWRITE_RULE[IWORD_CASES_ABS_ALT]) THEN

    SUBGOAL_THEN
     `val(iword(abs m00):int64) <= 2 EXP 59 /\
      val(iword(abs m01):int64) <= 2 EXP 59 /\
      val(iword(abs m10):int64) <= 2 EXP 59 /\
      val(iword(abs m11):int64) <= 2 EXP 59`
    (STRIP_ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THENL
     [REWRITE_TAC[iword] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC VAL_WORD_LE THEN
      SIMP_TAC[GSYM INT_OF_NUM_CLAUSES; INT_OF_NUM_OF_INT; INT_ABS_POS;
               INT_REM_POS_EQ] THEN
      REWRITE_TAC[DIMINDEX_64] THEN MATCH_MP_TAC INT_REM_LE THEN
      ASM_REWRITE_TAC[INT_ABS_POS];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `abs(real_of_int m00) = &(val(iword(abs m00):int64)) /\
      abs(real_of_int m01) = &(val(iword(abs m01):int64)) /\
      abs(real_of_int m10) = &(val(iword(abs m10):int64)) /\
      abs(real_of_int m11) = &(val(iword(abs m11):int64))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN REPEAT CONJ_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_VAL_IWORD THEN
      REWRITE_TAC[INT_ABS_POS; DIMINDEX_64] THEN
      ASM_SIMP_TAC[INT_ARITH `x:int <= &2 pow 59 ==> x < &2 pow 64`];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `word_ishr(iword m00:int64) 63 = word_neg(word(bitval(m00 < &0))) /\
      word_ishr(iword m01:int64) 63 = word_neg(word(bitval(m01 < &0))) /\
      word_ishr(iword m10:int64) 63 = word_neg(word(bitval(m10 < &0))) /\
      word_ishr(iword m11:int64) 63 = word_neg(word(bitval(m11 < &0)))`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL
     [REWRITE_TAC[GSYM DIMINDEX_64; ARITH_RULE `63 = 64 - 1`] THEN
      REWRITE_TAC[WORD_ISHR_MSB; MSB_IVAL] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    (*** Starting offset, common to both accumulations ***)

    X86_ACCSTEPS_TAC CORE_INV_P384_EXEC [25;31] (21--32) THEN

    (*** Accumulation of new f and g (then keep 2 accumulations above) ***)

    X86_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [36;37;38;41;42;43;47;48;49;52;53;54;58;59;60;63;64;
      65;71;72;73;76;77;78;84;85;86;89;90;91;97;98;99;102;
      103;104;110;111;112;115;116;117;123;124;125;128;129;130;
      136;137;138;141;142;143;149;150;151;154;155;156;165;166;
      167;173;174;175;176;189;190;191;197;198;199;200]
     (33--206) THEN
    MAP_EVERY ABBREV_TAC
     [`fup = bignum_of_wordlist
        [sum_s42;sum_s64;sum_s90;sum_s116;sum_s142;sum_s175;sum_s176]`;
      `gup = bignum_of_wordlist
        [sum_s53;sum_s77;sum_s103;sum_s129;sum_s155;sum_s199;sum_s200]`] THEN
    SUBGOAL_THEN
     `(&fup:int ==
       --(&1) pow i *
       (m00 * divstep_f (59 * i) t + m01 * divstep_g (59 * i) t))
      (mod (&2 pow 448)) /\
      (&gup:int ==
       --(&1) pow i *
       (m10 * divstep_f (59 * i) t + m11 * divstep_g (59 * i) t))
      (mod (&2 pow 448))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[INT_ARITH
       `i * (m * x + n * y):int = m * (i * x) + n * i * y`] THEN
      CONJ_TAC THEN MAP_EVERY
       (SUBST1_TAC o C SPEC
         (INT_ARITH `!m:int. m = if m < &0 then --(abs m) else abs m`))
       [`m00:int`; `m01:int`; `m10:int`; `m11:int`] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      REPLICATE_TAC 2 (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
      REWRITE_TAC[WORD_AND_ISHR_CASES; WORD_SUB_LZERO; REAL_VAL_WORD_NOT;
                  VAL_WORD_0; DIMINDEX_64] THEN
      STRIP_TAC THEN MAP_EVERY UNDISCH_TAC
       [`(&f == --(&1) pow i * divstep_f (59 * i) t) (mod (&2 pow 448))`;
        `(&g == --(&1) pow i * divstep_g (59 * i) t) (mod (&2 pow 448))`] THEN
      MAP_EVERY EXPAND_TAC ["f"; "g"; "t"] THEN
      (DISCH_THEN(MP_TAC o MATCH_MP TWOS_COMPLEMENT_448) THEN ANTS_TAC THENL
       [MATCH_MP_TAC(INT_ARITH `abs(x:int) < e ==> --e <= x /\ x < e`) THEN
        REWRITE_TAC[INT_ABS_MUL; INT_ABS_POW; INT_ABS_NEG; INT_ABS_NUM] THEN
        REWRITE_TAC[INT_POW_ONE; INT_MUL_LID] THEN MATCH_MP_TAC(INT_ARITH
         `--(e - &1):int <= g /\ g < e - &1 ==> abs(g) < e`) THEN
        MATCH_MP_TAC DIVSTEP_G_BOUNDS THEN
        REWRITE_TAC[p_384] THEN INT_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `gtop:bool`
          (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST1_TAC))] THEN
       DISCH_THEN(MP_TAC o MATCH_MP TWOS_COMPLEMENT_448) THEN ANTS_TAC THENL
        [MATCH_MP_TAC(INT_ARITH `abs(x:int) < e ==> --e <= x /\ x < e`) THEN
         REWRITE_TAC[INT_ABS_MUL; INT_ABS_POW; INT_ABS_NEG; INT_ABS_NUM] THEN
         REWRITE_TAC[INT_POW_ONE; INT_MUL_LID] THEN MATCH_MP_TAC(INT_ARITH
          `--(e - &1):int <= g /\ g < e - &1 ==> abs(g) < e`) THEN
         MATCH_MP_TAC DIVSTEP_F_BOUNDS THEN
         REWRITE_TAC[p_384] THEN INT_ARITH_TAC;
         DISCH_THEN(X_CHOOSE_THEN `ftop:bool`
           (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST1_TAC))]) THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
      MAP_EVERY EXPAND_TAC ["fup"; "gup"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK; WORD_NOT_MASK] THEN
      REWRITE_TAC[COND_SWAP] THEN
      MAP_EVERY ASM_CASES_TAC [`ftop:bool`; `gtop:bool`] THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN STRIP_TAC THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      ACCUMULATOR_ASSUM_LIST(fun ths ->
        ASSUM_LIST(fun cths ->
           let tts = filter (is_ratconst o rand o concl)
                            (GEN_DECARRY_RULE cths ths) in
           REWRITE_TAC tts)) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64; ARITH] THEN
      REWRITE_TAC[BIT_WORD_NOT; COND_SWAP; DIMINDEX_64; ARITH] THEN
      REWRITE_TAC[REAL_VAL_WORD_NEG; DIMINDEX_64] THEN
      REPEAT(COND_CASES_TAC THEN
        ASM_REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; REAL_VAL_WORD_NEG;
                        BITVAL_CLAUSES; DIMINDEX_64]) THEN
      REAL_INTEGER_TAC;

      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        fst o chop_list 2 o rev) THEN
      STRIP_TAC] THEN

    (*** Accumulation of new u and v values before reduction ***)

    X86_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [212;213;214;217;218;219;223;225;226;229;230;231;236;237;
      238;241;242;243;247;249;250;253;254;255;260;261;262;265;
      266;267;271;273;274;277;278;279;284;285;286;289;290;291;
      295;297;298;301;302;303;308;309;310;313;314;315;319;321;
      322;325;326;327;334;335;336;341;342;343;344;352;353;354;
      359;360;361;362]
     (207--364) THEN
    MAP_EVERY ABBREV_TAC
     [`uup = bignum_of_wordlist
        [sum_s218;sum_s242;sum_s266;sum_s290;sum_s314;sum_s343;sum_s344]`;
      `vup = bignum_of_wordlist
        [sum_s230;sum_s254;sum_s278;sum_s302;sum_s326;sum_s361;sum_s362]`] THEN
    SUBGOAL_THEN
     `(&uup:int == m00 * &u + m01 * &v) (mod (&2 pow 448)) /\
      (&vup:int == m10 * &u + m11 * &v) (mod (&2 pow 448))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MAP_EVERY
       (SUBST1_TAC o C SPEC
         (INT_ARITH `!m:int. m = if m < &0 then --(abs m) else abs m`))
       [`m00:int`; `m01:int`; `m10:int`; `m11:int`] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      REPLICATE_TAC 2 (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
      REWRITE_TAC[WORD_AND_ISHR_CASES; WORD_SUB_LZERO; REAL_VAL_WORD_NOT;
                  VAL_WORD_0; DIMINDEX_64] THEN
      STRIP_TAC THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
      MAP_EVERY EXPAND_TAC ["uup"; "vup"; "u"; "v"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      ACCUMULATOR_ASSUM_LIST(fun ths ->
        ASSUM_LIST(fun cths ->
           let tts = filter (is_ratconst o rand o concl)
                            (GEN_DECARRY_RULE cths ths) in
           REWRITE_TAC tts)) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64; ARITH] THEN
      REWRITE_TAC[BIT_WORD_NOT; COND_SWAP; DIMINDEX_64; ARITH] THEN
      ASM_REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; REAL_VAL_WORD_NEG;
                      BITVAL_CLAUSES; DIMINDEX_64] THEN
      REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    (*** Bounds on the updated u and v integers ***)

    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    SUBGOAL_THEN
     `abs(m00 * &u + m01 * &v:int) <= &2 pow 444 /\
      abs(m10 * &u + m11 * &v:int) <= &2 pow 444`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(INT_ARITH
       `abs(x) <= &2 pow 59 * &2 pow 384 /\
        abs(y) <= &2 pow 59 * &2 pow 384
        ==> abs(x + y:int) <= &2 pow 444`) THEN
      REWRITE_TAC[INT_ABS_MUL] THEN
      CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL2 THEN
      ASM_REWRITE_TAC[INT_ABS_NUM; INT_POS; INT_ABS_POS] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      MAP_EVERY EXPAND_TAC ["u"; "v"] THEN BOUNDER_TAC[];
      ALL_TAC] THEN

    (*** Biasing and Montgomery reduction of u ***)

    X86_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [367;370;372;374;376;378;380] (365--380) THEN
    ABBREV_TAC
     `upos =
      bignum_of_wordlist
       [sum_s367; sum_s370; sum_s372; sum_s374;
        sum_s376; sum_s378; sum_s380]` THEN
    SUBGOAL_THEN
     `upos < 2 EXP 446 /\ (&upos:int == m00 * &u + m01 * &v) (mod (&p_384))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      SUBGOAL_THEN
       `&upos:int = (m00 * &u + m01 * &v) + &2 pow 61 * &p_384`
      SUBST1_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[INTEGER_RULE `(x + k * p:int == x) (mod p)`] THEN
        UNDISCH_TAC `abs(m00 * &u + m01 * &v):int <= &2 pow 444` THEN
        REWRITE_TAC[p_384] THEN INT_ARITH_TAC] THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `upos < 2 EXP 448` MP_TAC THENL
         [EXPAND_TAC "upos" THEN BOUNDER_TAC[];
          UNDISCH_TAC `abs(m00 * &u + m01 * &v):int <= &2 pow 444`] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_384] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
       `(uup:int == uexp) (mod p)
        ==> (upos == uup + c) (mod p)
            ==> (upos == uexp + c) (mod p)`)) THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
      MAP_EVERY EXPAND_TAC ["upos"; "uup"] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; bignum_of_wordlist; p_384;
                  GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
    X86_STEPS_TAC CORE_INV_P384_EXEC (381--383) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
    X86_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [386;389;390;391;392;393;394;395;396;397;398;400;401;
      409;411;413;415;417;419] (384--420) THEN
    RULE_ASSUM_TAC(fun th ->
      try MATCH_MP mmlemma_alt th with Failure _ -> th) THEN
    SUBGOAL_THEN
     `(&2 pow 64 *
       &(bignum_of_wordlist
          [sum_s409; sum_s411; sum_s413; sum_s415; sum_s417; sum_s419]):int ==
       m00 * &u + m01 * &v) (mod &p_384)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          INT_CONG_TRANS)) THEN
      ABBREV_TAC `w:int64 = word(4294967297 * val(sum_s367:int64))` THEN
      MATCH_MP_TAC INT_CONG_TRANS THEN EXISTS_TAC
       `if &upos + &(val(w:int64)) * &p_384:int < &2 pow 448
        then &upos + &(val w) * &p_384:int
        else (&upos + &(val w) * &p_384) - &2 pow 64 * &p_384` THEN
      CONJ_TAC THENL [ALL_TAC; COND_CASES_TAC THEN CONV_TAC INTEGER_RULE] THEN
      MATCH_MP_TAC INT_EQ_IMP_CONG THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
        MATCH_MP_TAC(INT_ARITH
         `&0:int <= x /\ x < p /\ &0 <= y /\ y < p ==> abs(x - y) < p`) THEN
        REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
         [EXPAND_TAC "upos" THEN REWRITE_TAC[p_384] THEN BOUNDER_TAC[];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [POP_ASSUM MP_TAC THEN REWRITE_TAC[p_384] THEN INT_ARITH_TAC;
          EXPAND_TAC "upos" THEN REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `2 EXP 64 * bignum_of_wordlist
         [sum_s393;sum_s394;sum_s395;sum_s396;sum_s397;sum_s400;sum_s401] =
        upos + val(w:int64) * p_384`
      ASSUME_TAC THENL
      [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 512` THEN
         REPLICATE_TAC 2 (CONJ_TAC THENL
         [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC]) THEN
        REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
        EXPAND_TAC "upos" THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `val(sum_s401:int64) < 2` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
         `2 EXP 64 * x = y ==> y < 2 * 2 EXP 448 ==> x < 2 * 2 EXP 384`)) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
        REWRITE_TAC[NUM_AS_BITVAL_ALT; VAL_WORD_GALOIS]] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:bool` (SUBST_ALL_TAC o CONJUNCT2)) THEN
      SUBGOAL_THEN
       `&upos + &(val(w:int64)) * &p_384:int < &2 pow 448 <=> ~c`
      SUBST1_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        REWRITE_TAC[NOT_LT] THEN BOUNDER_TAC[];
        REWRITE_TAC[COND_SWAP]] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        rev o fst o chop_list 6) THEN
      REWRITE_TAC[WORD_SUB_LZERO; WORD_AND_MASK] THEN
      BOOL_CASES_TAC `c:bool` THEN
      REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist; p_384] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    (*** Biasing and Montgomery reduction of v ***)

    X86_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [423;426;428;430;432;434;436] (421--436) THEN
    ABBREV_TAC
     `vpos =
      bignum_of_wordlist
       [sum_s423;sum_s426;sum_s428;sum_s430;sum_s432;sum_s434;sum_s436]` THEN
    SUBGOAL_THEN
     `vpos < 2 EXP 446 /\ (&vpos:int == m10 * &u + m11 * &v) (mod (&p_384))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      SUBGOAL_THEN
       `&vpos:int = (m10 * &u + m11 * &v) + &2 pow 61 * &p_384`
      SUBST1_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[INTEGER_RULE `(x + k * p:int == x) (mod p)`] THEN
        UNDISCH_TAC `abs(m10 * &u + m11 * &v):int <= &2 pow 444` THEN
        REWRITE_TAC[p_384] THEN INT_ARITH_TAC] THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `vpos < 2 EXP 448` MP_TAC THENL
         [EXPAND_TAC "vpos" THEN BOUNDER_TAC[];
          UNDISCH_TAC `abs(m10 * &u + m11 * &v):int <= &2 pow 444`] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_384] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
       `(vup:int == vexp) (mod p)
        ==> (vpos == vup + c) (mod p)
            ==> (vpos == vexp + c) (mod p)`)) THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
      MAP_EVERY EXPAND_TAC ["vpos"; "vup"] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; bignum_of_wordlist; p_384;
                  GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
    X86_STEPS_TAC CORE_INV_P384_EXEC (437--439) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
    X86_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [442;445;446;447;448;449;450;451;452;453;454;456;457;
      465;467;469;471;473;475] (440--476) THEN
    RULE_ASSUM_TAC(fun th ->
      try MATCH_MP mmlemma_alt th with Failure _ -> th) THEN
    SUBGOAL_THEN
     `(&2 pow 64 *
       &(bignum_of_wordlist
          [sum_s465; sum_s467; sum_s469; sum_s471; sum_s473; sum_s475]):int ==
       m10 * &u + m11 * &v) (mod &p_384)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          INT_CONG_TRANS)) THEN
      ABBREV_TAC `w:int64 = word(4294967297 * val(sum_s423:int64))` THEN
      MATCH_MP_TAC INT_CONG_TRANS THEN EXISTS_TAC
       `if &vpos + &(val(w:int64)) * &p_384:int < &2 pow 448
        then &vpos + &(val w) * &p_384:int
        else (&vpos + &(val w) * &p_384) - &2 pow 64 * &p_384` THEN
      CONJ_TAC THENL [ALL_TAC; COND_CASES_TAC THEN CONV_TAC INTEGER_RULE] THEN
      MATCH_MP_TAC INT_EQ_IMP_CONG THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
        MATCH_MP_TAC(INT_ARITH
         `&0:int <= x /\ x < p /\ &0 <= y /\ y < p ==> abs(x - y) < p`) THEN
        REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
         [EXPAND_TAC "vpos" THEN REWRITE_TAC[p_384] THEN BOUNDER_TAC[];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [POP_ASSUM MP_TAC THEN REWRITE_TAC[p_384] THEN INT_ARITH_TAC;
          EXPAND_TAC "vpos" THEN REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `2 EXP 64 * bignum_of_wordlist
         [sum_s449;sum_s450;sum_s451;sum_s452;sum_s453;sum_s456;sum_s457] =
        vpos + val(w:int64) * p_384`
      ASSUME_TAC THENL
      [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 512` THEN
         REPLICATE_TAC 2 (CONJ_TAC THENL
         [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC]) THEN
        REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
        EXPAND_TAC "vpos" THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `val(sum_s457:int64) < 2` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
         `2 EXP 64 * x = y ==> y < 2 * 2 EXP 448 ==> x < 2 * 2 EXP 384`)) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
        REWRITE_TAC[NUM_AS_BITVAL_ALT; VAL_WORD_GALOIS]] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:bool` (SUBST_ALL_TAC o CONJUNCT2)) THEN
      SUBGOAL_THEN
       `&vpos + &(val(w:int64)) * &p_384:int < &2 pow 448 <=> ~c`
      SUBST1_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        REWRITE_TAC[NOT_LT] THEN BOUNDER_TAC[];
        REWRITE_TAC[COND_SWAP]] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        rev o fst o chop_list 6) THEN
      REWRITE_TAC[WORD_SUB_LZERO; WORD_AND_MASK] THEN
      BOOL_CASES_TAC `c:bool` THEN
      REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist; p_384] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    (*** Finish the simulation before proceeding ***)

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s476" THEN

    (*** Stepping mathematics for divstep ***)

    REWRITE_TAC[ARITH_RULE `59 * (i + 1) = 59 + 59 * i`] THEN
    REWRITE_TAC[DIVSTEP_DFG_ADD] THEN

    MP_TAC(SPECL
     [`divstep_d (59 * i) t`; `divstep_f (59 * i) t`; `divstep_g (59 * i) t`;
      `59`] DIVSTEP_MAT) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "t" THEN MATCH_MP_TAC DIVSTEP_F_ODD THEN
      REWRITE_TAC[p_384] THEN CONV_TAC INT_REDUCE_CONV;
      GEN_REWRITE_TAC LAND_CONV [CART_EQ]] THEN
    SIMP_TAC[DIMINDEX_2; FORALL_2; imat_vmul; VECTOR_2;
             ISUM_2; LAMBDA_BETA; ARITH] THEN

    SUBGOAL_THEN
     `divstep_mat 59
      (divstep_d (59 * i) t,divstep_f (59 * i) t,divstep_g (59 * i) t) =
      divstep_mat 59 (divstep_d (59 * i) t,ival(f_0:int64),ival(g_0:int64))`
    SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS
       `divstep_mat 59
         (divstep_d (59 * i) t,
          --(&1) pow i * ival(f_0:int64),
          --(&1) pow i * ival(g_0:int64))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC DIVSTEP_MAT_CONGRUENCE THEN CONJ_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
         `(z:int == i * y) (mod q)
          ==> !r. (p divides q /\ p divides r) /\ (z == x) (mod r) /\
                  i pow 2 = &1
                  ==> (y == i * x) (mod p)`)) THEN
        EXISTS_TAC `(&2:int) pow 64` THEN
        SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
        REWRITE_TAC[INT_POW_POW] THEN
        REWRITE_TAC[INT_POW_NEG; EVEN_MULT; ARITH_EVEN; INT_POW_ONE] THEN
        MAP_EVERY EXPAND_TAC ["f"; "g"] THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
        REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
        REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD] THEN
        REWRITE_TAC[GSYM DIMINDEX_64; GSYM INT_OF_NUM_POW] THEN
        REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG] THEN
        REWRITE_TAC[DIMINDEX_64; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
        SIMP_TAC[VAL_BOUND_64; MOD_LT];
        REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN
        COND_CASES_TAC THEN REWRITE_TAC[INT_MUL_LNEG; INT_MUL_LID] THEN
        ASM_SIMP_TAC[DIVSTEP_MAT_NEG]];
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [INT_ARITH `m * x + n * y:int = e * z <=>
                   --m * x + --n * y = e * --z`] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(STRIP_ASSUME_TAC o GSYM)] THEN

    (*** The two right-shifts are easy now ***)

    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [REWRITE_TAC[INT_POW_ADD; INT_ARITH
        `(p * --(&1) pow 1) * f:int = p * --f`] THEN
      REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP
       (MESON[INT_DIV_MUL; INT_POW_EQ_0; INT_REDUCE_CONV `&2:int = &0`]
         `&2 pow 59 * x = y ==> x = y div &2 pow 59`) o
        SPEC `--(&1:int) pow i` o MATCH_MP(INT_RING
         `!z:int. &2 pow 59 * x = y ==> &2 pow 59 * z * x = z * y`))) THEN
      MAP_EVERY UNDISCH_TAC
       [`(&fup:int ==
          --(&1) pow i *
          (m00 * divstep_f (59 * i) t + m01 * divstep_g (59 * i) t))
         (mod (&2 pow 448))`;
        `(&gup:int ==
          --(&1) pow i *
          (m10 * divstep_f (59 * i) t + m11 * divstep_g (59 * i) t))
         (mod (&2 pow 448))`] THEN
      MAP_EVERY EXPAND_TAC ["fup"; "gup"] THEN
      REPLICATE_TAC 2
       (DISCH_THEN(MP_TAC o MATCH_MP TWOS_COMPLEMENT_448_WEAK) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC(INT_ARITH
           `abs(i * a * x) <= &2 pow 59 * &2 pow 384 /\
            abs(i * b * y) <= &2 pow 59 * &2 pow 384
            ==> --(&2 pow 447):int <= i * (a * x + b * y) /\
                i * (a * x + b * y) < &2 pow 447`) THEN
          ONCE_REWRITE_TAC[INT_ABS_MUL] THEN
          REWRITE_TAC[INT_ABS_POW; INT_ABS_NEG; INT_ABS_NUM] THEN
          REWRITE_TAC[INT_POW_ONE; INT_MUL_LID] THEN
          SUBGOAL_THEN
           `(--(&2 pow 384) <= divstep_f (59 * i) t /\
             divstep_f (59 * i) t < &2 pow 384) /\
            (--(&2 pow 384) <= divstep_g (59 * i) t /\
             divstep_g (59 * i) t < &2 pow 384)`
          STRIP_ASSUME_TAC THENL
           [EXPAND_TAC "t" THEN CONJ_TAC THENL
             [MATCH_MP_TAC DIVSTEP_F_BOUNDS;
              MATCH_MP_TAC DIVSTEP_G_BOUNDS] THEN
            REWRITE_TAC[p_384] THEN CONV_TAC INT_REDUCE_CONV THEN
            REWRITE_TAC[INT_OF_NUM_REM; INT_ARITH `--(&m):int <= &n`] THEN
            REWRITE_TAC[INT_OF_NUM_LT] THEN ARITH_TAC;
            REWRITE_TAC[INT_ABS_MUL] THEN CONJ_TAC THEN
            MATCH_MP_TAC INT_LE_MUL2 THEN
            ASM_REWRITE_TAC[INT_ABS_POS; INT_ABS_BOUNDS] THEN
            ASM_SIMP_TAC[INT_LT_IMP_LE]];
          DISCH_THEN(SUBST1_TAC o MATCH_MP (INT_ARITH
           `a:int = b + c ==> b = a - c`))]) THEN
      REWRITE_TAC[INT_ARITH
       `x - &2 pow 448 * b:int =
        x + &2 pow 59 * (&2 pow 389 * --b)`] THEN
      SIMP_TAC[INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[INTEGER_RULE
       `(a:int == b + c * --d) (mod n) <=> (a + c * d == b) (mod n)`] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; GSYM num_congruent] THEN
      CONJ_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [bignum_of_wordlist] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 59 * 2 EXP 5`] THEN
      SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT_ADD; ARITH_EQ; EXP_EQ_0] THEN
      REWRITE_TAC[bignum_of_wordlist] THEN
      CONV_TAC(ONCE_DEPTH_CONV VAL_EXPAND_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_INTEGER_TAC;
      ALL_TAC] THEN

    (*** Final stepping mathematics ***)

    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [num_divides] THEN
    REWRITE_TAC[GSYM INT_CONG_0_DIVIDES] THEN
    SUBGOAL_THEN
     `!x y:int. (x == y) (mod &p_384) <=>
                (&2 pow 64 * x == &2 pow 64 * y) (mod &p_384)`
     (fun th -> ONCE_REWRITE_TAC[th])
    THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC(INTEGER_RULE
       `!e:int. coprime(e,p)
                ==> ((x == y) (mod p) <=> (e * x == e * y) (mod p))`) THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_coprime; COPRIME_LEXP] THEN
      REWRITE_TAC[COPRIME_2; p_384] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x:int. &2 pow 64 * &2 pow (843 - 5 * (i + 1)) * x =
              &2 pow (843 - 5 * i) * &2 pow 59 * x`
    (fun th -> REWRITE_TAC[th]) THENL
      [ASM_SIMP_TAC[INT_POW_ADD; ARITH_RULE
        `i < 14 ==> 843 - 5 * i = (843 - 5 * (i + 1)) + 5`] THEN
       INT_ARITH_TAC;
       ASM_REWRITE_TAC[INT_MUL_RZERO]] THEN
    ONCE_REWRITE_TAC[INT_ARITH
     `&2 pow 64 * x * y:int = x * &2 pow 64 * y`] THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(&2 pow 64 * x:int == &0) (mod p) <=>
      (&0 == &1 * &2 pow 64 * x) (mod p)`] THEN
    REPEAT(FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o
      MATCH_MP (INTEGER_RULE
        `(&2 pow 64 * x:int == y) (mod p)
         ==> !z. ((z == e * &2 pow 64 * x) (mod p) <=>
                 (z == e * y) (mod p))`))) THEN
    ASM_REWRITE_TAC[INT_POW_ADD; INT_ARITH
     `e * (i * --(&1) pow 1) * f:int = i * e * --f`] THEN
    ASM_SIMP_TAC[INTEGER_RULE
     `(e * i * f:int == n * f') (mod p) /\ (e * i * g == n * g') (mod p)
      ==> (e * i * (a * f + b * g) == n * (a * f' + b * g')) (mod p)`] THEN
    DISCH_TAC THEN MATCH_MP_TAC(INTEGER_RULE
     `p divides u /\ b = &0
      ==> (&0:int == &1 * (a * u + b * v)) (mod p)`) THEN
    ASM_SIMP_TAC[GSYM num_divides] THEN
    SUBST1_TAC(SYM(ASSUME `--((mm:int^2^2)$1$2) = m01`)) THEN
    REWRITE_TAC[INT_NEG_EQ_0] THEN EXPAND_TAC "mm" THEN
    MATCH_MP_TAC DIVSTEP_MAT_DIAGONAL_1 THEN
    SUBGOAL_THEN `g = 0` MP_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_EQ];
      EXPAND_TAC "g" THEN
      SIMP_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL; IVAL_WORD_0]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (MESON[INT_CONG_IMP_EQ;INT_SUB_RZERO]
      `(x == y) (mod n) ==> y:int = &0 /\ abs(x) < n ==> x = &0`)) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_ENTIRE] THEN DISJ2_TAC THEN
      EXPAND_TAC "t" THEN MATCH_MP_TAC DIVSTEP_G_ZERO THEN
      ASM_REWRITE_TAC[INT_REM_EQ_0; GSYM num_divides];
      REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_CLAUSES] THEN
      EXPAND_TAC "g" THEN BOUNDER_TAC[]];

    (*** Because of the peculiar loop structure, completely trivial ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC CORE_INV_P384_EXEC [] THEN ASM_REWRITE_TAC[];

    ALL_TAC] THEN

  (*** Start on the tail computation, with similar divstep reasoning ***)

  CONV_TAC(DEPTH_CONV NUM_SUB_CONV) THEN
  REWRITE_TAC[ARITH_RULE `59 * 14 = 826`] THEN
  GHOST_INTRO_TAC `f:num` `read (memory :> bytes (stackpointer,8 * 7))` THEN
  GHOST_INTRO_TAC `g:num`
   `read (memory :> bytes (word_add stackpointer (word 64),8 * 7))` THEN
  GHOST_INTRO_TAC `u:num`
   `read (memory :> bytes (word_add stackpointer (word 128),8 * 6))` THEN
  GHOST_INTRO_TAC `v:num`
   `read (memory :> bytes (word_add stackpointer (word 192),8 * 6))` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `7`) [`f:num`; `g:num`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "f_"
   `read (memory :> bytes(stackpointer,8 * 7)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "g_"
   `read (memory :> bytes(word_add stackpointer (word 64),8 * 7)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "u_"
   `read (memory :> bytes(word_add stackpointer (word 128),8 * 6)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "v_"
   `read (memory :> bytes(word_add stackpointer (word 192),8 * 6)) s0` THEN
  MP_TAC(SPECL
   [`iword (divstep_d 826 t):int64`;
    `f_0:int64`; `g_0:int64`; `stackpointer:int64`; `pc:num`]
   LOCAL_WORD_DIVSTEP59_CORRECT) THEN
  ASM_REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  X86_BIGSTEP_TAC CORE_INV_P384_EXEC "s1" THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN

  SUBGOAL_THEN `ival(f_0:int64) rem &2 = &1` ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS `(--(&1) pow 14 * divstep_f 826 t) rem &2` THEN
    EXPAND_TAC "t" THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[INT_REM_EQ];
      ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
      ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN
      CONV_TAC INT_REDUCE_CONV THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_POW_ONE; INT_MUL_LID] THEN
      MATCH_MP_TAC DIVSTEP_F_ODD THEN REWRITE_TAC[p_384] THEN
      CONV_TAC INT_REDUCE_CONV] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(z:int == y) (mod q)
      ==> !r. (p divides q /\ p divides r) /\ (z == x) (mod r)
              ==> (x == y) (mod p)`)) THEN
    EXISTS_TAC `(&2:int) pow 64` THEN REWRITE_TAC[GSYM INT_REM_EQ_0] THEN
    CONJ_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD] THEN
    REWRITE_TAC[GSYM DIMINDEX_64; GSYM INT_OF_NUM_POW] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG] THEN
    REWRITE_TAC[DIMINDEX_64; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    SIMP_TAC[VAL_BOUND_64; MOD_LT];
    ALL_TAC] THEN

  SUBGOAL_THEN `abs(divstep_d 826 t) < &2 pow 62` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN W(MP_TAC o
     PART_MATCH (lhand o rand o lhand) DIVSTEP_D_BOUND o lhand o snd) THEN
    MATCH_MP_TAC(INT_ARITH
     `e:int < &827
      ==> abs(x - abs(&1)) <= &2 * e ==> x < &2 pow 62`) THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(iword(divstep_d 826 t):int64) = divstep_d 826 t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[DIVSTEP_D_PARITY] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `divstep_d 59 (divstep_d 826 t,ival(f_0:int64),ival(g_0:int64)) =
    divstep_d 885 t`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `885 = 59 + 826`] THEN
    TRANS_TAC EQ_TRANS
     `divstep_d 59 (divstep_d 826 t,
                    --(&1) pow 14 * ival(f_0:int64),
                    --(&1) pow 14 * ival(g_0:int64))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN
      COND_CASES_TAC THEN REWRITE_TAC[INT_MUL_LNEG; INT_MUL_LID] THEN
      ASM_SIMP_TAC[DIVSTEP_D_NEG];
      ALL_TAC] THEN
    REWRITE_TAC[DIVSTEP_DFG_ADD] THEN
    MATCH_MP_TAC DIVSTEP_D_CONGRUENCE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(z:int == i * y) (mod q)
      ==> !r. (p divides q /\ p divides r) /\ (z == x) (mod r) /\
              i pow 2 = &1
              ==> (i * x == y) (mod p)`)) THEN
    EXISTS_TAC `(&2:int) pow 64` THEN
    SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[INT_POW_POW] THEN
    REWRITE_TAC[INT_POW_NEG; EVEN_MULT; ARITH_EVEN; INT_POW_ONE] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD] THEN
    REWRITE_TAC[GSYM DIMINDEX_64; GSYM INT_OF_NUM_POW] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG] THEN
    REWRITE_TAC[DIMINDEX_64; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    SIMP_TAC[VAL_BOUND_64; MOD_LT];
    ALL_TAC] THEN

  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV let_CONV)) THEN
  MAP_EVERY ABBREV_TAC
   [`mm = divstep_mat 59
           (divstep_d 826 t,ival(f_0:int64),ival(g_0:int64))`;
    `m00 = --((mm:int^2^2)$1$1)`;
    `m01 = --((mm:int^2^2)$1$2)`;
    `m10 = --((mm:int^2^2)$2$1)`;
    `m11 = --((mm:int^2^2)$2$2)`] THEN
  STRIP_TAC THEN

  (*** Complete all the simulation first ***)

  X86_ACCSTEPS_TAC CORE_INV_P384_EXEC
   [35;39;40;41;44;45;47;51;52;53;56;57;59;63;64;65;68;69;
    71;75;76;77;80;81;83;87;88;89;92;93;95;100;101;102;
    107;108;109;111;115;118;120;122;124;126;128;134;137;138;
    139;141;142;143;144;145;146;148;149;157;159;161;163;
    165;167;176;178;180;182;184;186]
   (2--199) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s199" THEN

  (*** Deploy the divstep bound to deduce g = 0 ***)

  MP_TAC(SPECL [`&p_384:int`; `&n rem &p_384`; `384`; `885`]
        IDIVSTEP_ENDTOEND_BITS_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[p_384] THEN INT_ARITH_TAC;
    STRIP_TAC] THEN

  (*** Sign-magnitude breakdown of matrix entries ***)

  RULE_ASSUM_TAC(REWRITE_RULE[IWORD_CASES_LEMMA]) THEN
  SUBGOAL_THEN
   `abs(m00:int) <= &2 pow 59 /\
    abs(m01:int) <= &2 pow 59 /\
    abs(m10:int) <= &2 pow 59 /\
    abs(m11:int) <= &2 pow 59`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m00"; "m01"; "m10"; "m11"; "mm"] THEN
    REWRITE_TAC[INT_ABS_NEG] THEN
    SIMP_TAC[INT_ABS_BOUNDS; DIVSTEP_MAT_BOUNDS; INT_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(iword m00:int64) = m00 /\
    ival(iword m01:int64) = m01 /\
    ival(iword m10:int64) = m10 /\
    ival(iword m11:int64) = m11`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN STRIP_ASSUME_TAC th)
  THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[INT_ARITH
     `abs(m:int) <= &2 pow 59 ==> --(&2 pow 63) <= m /\ m < &2 pow 63`];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `ival(word_neg(iword m00:int64)) = --m00 /\
    ival(word_neg(iword m01:int64)) = --m01 /\
    ival(word_neg(iword m10:int64)) = --m10 /\
    ival(word_neg(iword m11:int64)) = --m11`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN STRIP_ASSUME_TAC th)
  THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    MATCH_MP_TAC(WORD_ARITH
     `!x:N word. abs(ival(x)) < &2 pow (dimindex(:N) - 1)
                 ==> ival(word_neg x) = --ival x`) THEN
    ASM_REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    MATCH_MP_TAC(INT_ARITH `x:int <= &2 pow 59 ==> x < &2 pow 63`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  RULE_ASSUM_TAC(REWRITE_RULE[IWORD_CASES_ABS_ALT]) THEN

  SUBGOAL_THEN
   `val(iword(abs m00):int64) <= 2 EXP 59 /\
    val(iword(abs m01):int64) <= 2 EXP 59 /\
    val(iword(abs m10):int64) <= 2 EXP 59 /\
    val(iword(abs m11):int64) <= 2 EXP 59`
  (STRIP_ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THENL
   [REWRITE_TAC[iword] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC VAL_WORD_LE THEN
    SIMP_TAC[GSYM INT_OF_NUM_CLAUSES; INT_OF_NUM_OF_INT; INT_ABS_POS;
             INT_REM_POS_EQ] THEN
    REWRITE_TAC[DIMINDEX_64] THEN MATCH_MP_TAC INT_REM_LE THEN
    ASM_REWRITE_TAC[INT_ABS_POS];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `abs(real_of_int m00) = &(val(iword(abs m00):int64)) /\
    abs(real_of_int m01) = &(val(iword(abs m01):int64)) /\
    abs(real_of_int m10) = &(val(iword(abs m10):int64)) /\
    abs(real_of_int m11) = &(val(iword(abs m11):int64))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN REPEAT CONJ_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_VAL_IWORD THEN
    REWRITE_TAC[INT_ABS_POS; DIMINDEX_64] THEN
    ASM_SIMP_TAC[INT_ARITH `x:int <= &2 pow 59 ==> x < &2 pow 64`];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `word_ishr(iword m00:int64) 63 = word_neg(word(bitval(m00 < &0))) /\
    word_ishr(iword m01:int64) 63 = word_neg(word(bitval(m01 < &0))) /\
    word_ishr(iword m10:int64) 63 = word_neg(word(bitval(m10 < &0))) /\
    word_ishr(iword m11:int64) 63 = word_neg(word(bitval(m11 < &0)))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL
   [REWRITE_TAC[GSYM DIMINDEX_64; ARITH_RULE `63 = 64 - 1`] THEN
    REWRITE_TAC[WORD_ISHR_MSB; MSB_IVAL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Stepping mathematics for divstep ***)

  MP_TAC(SPECL
     [`divstep_d 826 t`; `divstep_f 826 t`; `divstep_g 826 t`;
      `59`] DIVSTEP_MAT) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC DIVSTEP_F_ODD THEN
    REWRITE_TAC[p_384] THEN CONV_TAC INT_REDUCE_CONV;
    GEN_REWRITE_TAC LAND_CONV [CART_EQ]] THEN
  SIMP_TAC[DIMINDEX_2; FORALL_2; imat_vmul; VECTOR_2;
           ISUM_2; LAMBDA_BETA; ARITH] THEN

  SUBGOAL_THEN
   `divstep_mat 59 (divstep_d 826 t,divstep_f 826 t,divstep_g 826 t) =
    mm`
  SUBST1_TAC THENL
   [EXPAND_TAC "mm" THEN MATCH_MP_TAC DIVSTEP_MAT_CONGRUENCE THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(z:int == i * y) (mod q)
      ==> !r. (p divides q /\ p divides r) /\ (z == x) (mod r) /\
              i = &1
              ==> (y == x) (mod p)`)) THEN
    EXISTS_TAC `(&2:int) pow 64` THEN
    SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[INT_POW_POW] THEN
    REWRITE_TAC[INT_POW_NEG; EVEN_MULT; ARITH_EVEN; INT_POW_ONE] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD] THEN
    REWRITE_TAC[GSYM DIMINDEX_64; GSYM INT_OF_NUM_POW] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG] THEN
    REWRITE_TAC[DIMINDEX_64; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    SIMP_TAC[VAL_BOUND_64; MOD_LT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM DIVSTEP_DFG_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC THEN

  (*** Final f sign in non-degenerate case ***)

  MP_TAC(GEN `x:int64` (ISPEC `x:int64` WORD_ISHR_MSB)) THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ABBREV_TAC
   `bsgn <=> bit 63 (word_add (word_mul f_0 (iword m00))
                              (word_mul g_0 (iword m01)):int64)` THEN

  (*** Accumulation of pre-reduction u value ***)

  ABBREV_TAC
   `uup = bignum_of_wordlist
     [sum_s45;sum_s57;sum_s69;sum_s81;sum_s93;sum_s109;sum_s111]` THEN

  SUBGOAL_THEN
   `(&uup:int ==
     --(&1) pow bitval bsgn *
     (m00 * &u + m01 * &v)) (mod (&2 pow 448))`
  ASSUME_TAC THENL
   [REWRITE_TAC[INT_POW_NEG; EVEN_BITVAL; COND_SWAP; INT_POW_ONE] THEN
    MAP_EVERY
     (SUBST1_TAC o C SPEC
       (INT_ARITH `!m:int. m = if m < &0 then --(abs m) else abs m`))
     [`m00:int`; `m01:int`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev o
        snd o chop_list 31) THEN
    REPLICATE_TAC 3 (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK; WORD_NOT_MASK] THEN
    REWRITE_TAC[WORD_AND_ISHR_CASES; WORD_SUB_LZERO; REAL_VAL_WORD_NOT;
      WORD_NEG_0; WORD_NEG_NEG; WORD_SUB_0; VAL_WORD_0; DIMINDEX_64] THEN
    STRIP_TAC THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
    MAP_EVERY EXPAND_TAC ["uup"; "u"; "v"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(fun ths ->
      ASSUM_LIST(fun cths ->
         let tts = filter (is_ratconst o rand o concl)
                          (GEN_DECARRY_RULE cths ths) in
         REWRITE_TAC tts)) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64; ARITH] THEN
    REWRITE_TAC[BIT_WORD_NOT; COND_SWAP; DIMINDEX_64; ARITH] THEN
    ASM_REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; REAL_VAL_WORD_NEG;
                    BITVAL_CLAUSES; DIMINDEX_64] THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev o
      fst o chop_list 31) THEN
    STRIP_TAC] THEN

  (*** Bound on the updated u value ***)

  ABBREV_TAC `fsgn:int = -- &1 pow bitval bsgn` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  SUBGOAL_THEN `abs(fsgn * (m00 * &u + m01 * &v):int) <= &2 pow 444`
  ASSUME_TAC THENL
   [EXPAND_TAC "fsgn" THEN
    REWRITE_TAC[INT_ABS_MUL; INT_ABS_POW; INT_ABS_NEG; INT_POW_ONE;
                INT_ABS_NUM; INT_MUL_LID] THEN
    MATCH_MP_TAC(INT_ARITH
     `abs(x) <= &2 pow 59 * &2 pow 384 /\
      abs(y) <= &2 pow 59 * &2 pow 384
      ==> abs(x + y:int) <= &2 pow 444`) THEN
    REWRITE_TAC[INT_ABS_MUL] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL2 THEN
    ASM_REWRITE_TAC[INT_ABS_NUM; INT_POS; INT_ABS_POS] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    MAP_EVERY EXPAND_TAC ["u"; "v"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Biasing and Montgomery reduction of u ***)

  ABBREV_TAC
   `upos =
    bignum_of_wordlist
     [sum_s115;sum_s118;sum_s120;sum_s122;sum_s124;sum_s126;sum_s128]` THEN
  SUBGOAL_THEN
   `upos < 2 EXP 446 /\
    (&upos:int == fsgn * (m00 * &u + m01 * &v)) (mod (&p_384))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    SUBGOAL_THEN
     `&upos:int = fsgn * (m00 * &u + m01 * &v) + &2 pow 61 * &p_384`
    SUBST1_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[INTEGER_RULE `(x + k * p:int == x) (mod p)`] THEN
      UNDISCH_TAC `abs(fsgn * (m00 * &u + m01 * &v)):int <= &2 pow 444` THEN
      REWRITE_TAC[p_384] THEN INT_ARITH_TAC] THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `upos < 2 EXP 448` MP_TAC THENL
       [EXPAND_TAC "upos" THEN BOUNDER_TAC[];
        UNDISCH_TAC `abs(fsgn * (m00 * &u + m01 * &v)):int <= &2 pow 444`] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_384] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(uup:int == uexp) (mod p)
      ==> (upos == uup + c) (mod p)
          ==> (upos == uexp + c) (mod p)`)) THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
    MAP_EVERY EXPAND_TAC ["upos"; "uup"] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        fst o chop_list 7 o rev) THEN
    REWRITE_TAC[REAL_BITVAL_NOT; bignum_of_wordlist; p_384;
                GSYM REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        snd o chop_list 7 o rev) THEN
    STRIP_TAC] THEN

  RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
  RULE_ASSUM_TAC(fun th ->
    try MATCH_MP mmlemma_alt th with Failure _ -> th) THEN
  SUBGOAL_THEN
   `(&2 pow 64 *
     &(bignum_of_wordlist
        [sum_s157;sum_s159;sum_s161;sum_s163;sum_s165;sum_s167]):int ==
     fsgn * (m00 * &u + m01 * &v)) (mod &p_384)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        INT_CONG_TRANS)) THEN
    ABBREV_TAC `w:int64 = word(4294967297 * val(sum_s115:int64))` THEN
    MATCH_MP_TAC INT_CONG_TRANS THEN EXISTS_TAC
     `if &upos + &(val(w:int64)) * &p_384:int < &2 pow 448
      then &upos + &(val w) * &p_384:int
      else (&upos + &(val w) * &p_384) - &2 pow 64 * &p_384` THEN
    CONJ_TAC THENL [ALL_TAC; COND_CASES_TAC THEN CONV_TAC INTEGER_RULE] THEN
    MATCH_MP_TAC INT_EQ_IMP_CONG THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC(INT_ARITH
       `&0:int <= x /\ x < p /\ &0 <= y /\ y < p ==> abs(x - y) < p`) THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [EXPAND_TAC "upos" THEN REWRITE_TAC[p_384] THEN BOUNDER_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [POP_ASSUM MP_TAC THEN REWRITE_TAC[p_384] THEN INT_ARITH_TAC;
        EXPAND_TAC "upos" THEN REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `2 EXP 64 * bignum_of_wordlist
       [sum_s141;sum_s142;sum_s143;sum_s144;sum_s145;sum_s148;sum_s149] =
      upos + val(w:int64) * p_384`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 512` THEN
       REPLICATE_TAC 2 (CONJ_TAC THENL
       [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC]) THEN
      REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
      EXPAND_TAC "upos" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(sum_s149:int64) < 2` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `2 EXP 64 * x = y ==> y < 2 * 2 EXP 448 ==> x < 2 * 2 EXP 384`)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
      REWRITE_TAC[NUM_AS_BITVAL_ALT; VAL_WORD_GALOIS]] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:bool` (SUBST_ALL_TAC o CONJUNCT2)) THEN
    SUBGOAL_THEN
     `&upos + &(val(w:int64)) * &p_384:int < &2 pow 448 <=> ~c`
    SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[NOT_LT] THEN BOUNDER_TAC[];
      REWRITE_TAC[COND_SWAP]] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        rev o fst o chop_list 12) THEN
    REWRITE_TAC[WORD_SUB_LZERO; WORD_AND_MASK] THEN
    BOOL_CASES_TAC `c:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist; p_384] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
   `pra = bignum_of_wordlist
     [sum_s157;sum_s159;sum_s161;sum_s163;sum_s165;sum_s167]` THEN
  TRANS_TAC EQ_TRANS `&(pra MOD p_384):int` THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN MAP_EVERY EXISTS_TAC
     [`64 * 6`; `if pra < p_384 then &pra else &pra - &p_384:real`] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[p_384] THEN ARITH_TAC;
      REWRITE_TAC[p_384] THEN ARITH_TAC;
      ALL_TAC;
      SIMP_TAC[GSYM NOT_LE; COND_SWAP; REAL_OF_NUM_SUB; GSYM COND_RAND] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN
      MATCH_MP_TAC MOD_CASES THEN REWRITE_TAC[p_384] THEN
      EXPAND_TAC "pra" THEN BOUNDER_TAC[]] THEN
    SUBGOAL_THEN `carry_s186 <=> pra < p_384` (SUBST1_TAC o SYM) THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `384` THEN
      EXPAND_TAC "pra" THEN
      REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD; p_384;
                  GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
        rev o fst o chop_list 6) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(BINOP_CONV(BINOP_CONV REAL_POLY_CONV)) THEN BOUNDER_TAC[];
      EXPAND_TAC "pra" THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE o
        rev o fst o chop_list 6) THEN
      REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES]] THEN

  (*** Now finally handle the degenerate case ***)

  ASM_CASES_TAC `p_384 divides n` THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM DIVIDES_MOD; num_divides] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(e * x:int == f * (a * u + b * v)) (mod p)
      ==> p divides u /\ b = &0 /\ coprime(p,e)
          ==> p divides x`)) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_divides; GSYM num_coprime;
                    COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM p_384] THEN
    SUBST1_TAC(SYM(ASSUME `--((mm:int^2^2)$1$2) = m01`)) THEN
    REWRITE_TAC[INT_NEG_EQ_0] THEN EXPAND_TAC "mm" THEN
    MATCH_MP_TAC DIVSTEP_MAT_DIAGONAL_1 THEN
    SUBGOAL_THEN `g = 0` MP_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_EQ];
      EXPAND_TAC "g" THEN
      SIMP_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL; IVAL_WORD_0]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (MESON[INT_CONG_IMP_EQ;INT_SUB_RZERO]
      `(x == y) (mod n) ==> y:int = &0 /\ abs(x) < n ==> x = &0`)) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_ENTIRE] THEN DISJ2_TAC THEN
      EXPAND_TAC "t" THEN MATCH_MP_TAC DIVSTEP_G_ZERO THEN
      ASM_REWRITE_TAC[INT_REM_EQ_0; GSYM num_divides];
      REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_CLAUSES] THEN
      EXPAND_TAC "g" THEN BOUNDER_TAC[]];
    ASM_REWRITE_TAC[]] THEN

  (*** Deploy non-triviality ***)

  SUBGOAL_THEN `coprime(p_384,n)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P384]; ALL_TAC] THEN
  SUBGOAL_THEN `gcd(&p_384,&n rem &p_384) = &1` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM INT_COPRIME_GCD; INT_COPRIME_RREM] THEN
    ASM_SIMP_TAC[GSYM num_coprime];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(&(val(word_add (word_mul f_0 (iword m00))
                    (word_mul g_0 (iword m01)):int64)) ==
     --(&2 pow 59 * divstep_f 885 t)) (mod (&2 pow 64))`
  MP_TAC THENL
   [REWRITE_TAC[GSYM DIMINDEX_64; GSYM IWORD_EQ] THEN
    CONV_TAC WORD_VAL_CONG_CONV THEN REWRITE_TAC[DIMINDEX_64] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [INT_MUL_SYM] THEN
    FIRST_X_ASSUM(fun th ->
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    ASM_REWRITE_TAC[INT_NEG_ADD; GSYM INT_MUL_LNEG] THEN
    MATCH_MP_TAC INT_CONG_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC INT_CONG_LMUL THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (INTEGER_RULE
       `(f:int == --(&1) pow 14 * df) (mod q)
        ==> p divides q /\ (f == f0) (mod p) ==> (f0 == df) (mod p)`)) THEN
    SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
    REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC NUMBER_RULE;
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        TWOS_COMPLEMENT))] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[VAL_BOUND_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `abs (divstep_f 885 t) = &1` THEN INT_ARITH_TAC;
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; GSYM MSB_VAL] THEN
  ASM_REWRITE_TAC[DIMINDEX_64; NUM_SUB_CONV `64 - 1`] THEN
  REWRITE_TAC[INT_ARITH `--(&2 pow 59 * x) < &0 <=> &0:int < x`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN

  (*** Final part of mathematics ***)

  REWRITE_TAC[GSYM CONG; GSYM(NUM_EXP_CONV `2 EXP 768`)] THEN
  MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `n:num` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(n * i == 1) (mod p) /\ (n * pra == x) (mod p)
    ==> (n * pra == n * x * i) (mod p)`) THEN
  ASM_REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; num_congruent] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
   `(e * pra:int == f * x) (mod p)
    ==> coprime(e,p) /\ f * f = &1 /\
        (q * e * f == n * x) (mod p)
        ==> (n * pra == q) (mod p)`)) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_coprime] THEN
    REWRITE_TAC[COPRIME_LEXP; COPRIME_2; p_384] THEN CONV_TAC NUM_REDUCE_CONV;
    EXPAND_TAC "fsgn" THEN REWRITE_TAC[bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 pow 64 * fsgn:int =
    (&2 pow 5) * (m00 * divstep_f 826 t + m01 * divstep_g 826 t)`
  SUBST1_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `--((mm:int^2^2)$1$1) = m00`)) THEN
    SUBST1_TAC(SYM(ASSUME `--((mm:int^2^2)$1$2) = m01`)) THEN
    ASM_REWRITE_TAC[INT_ARITH `--x * y + --w * z:int = --(x * y + w * z)`] THEN
    EXPAND_TAC "fsgn" THEN UNDISCH_TAC `abs(divstep_f 885 t) = &1` THEN
    REWRITE_TAC[INT_ARITH `abs x:int = &1 <=> x = &1 \/ x = --(&1)`] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `((d * e) * -- &1 pow 14 * f:int == n * u) (mod p) /\
    ((d * e) * -- &1 pow 14 * g:int == n * v) (mod p)
    ==> (d * e * (a * f + b * g) == n * (a * u + b * v)) (mod p)`) THEN
  REWRITE_TAC[GSYM INT_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NUM_REDUCE_CONV `843 - 5 * 14`]) THEN
  ASM_REWRITE_TAC[]);;

let BIGNUM_MONTINV_P384_CORRECT = time prove
 (`!z x n pc stackpointer.
        ALL (nonoverlapping (stackpointer,336))
            [(word pc,0x19cd); (z,8 * 6); (x,8 * 6)] /\
        nonoverlapping (word pc,0x19cd) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_montinv_p384_tmc) /\
                  read RIP s = word(pc + 0x11) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = word (pc + 0x19bb) /\
                  bignum_from_memory(z,6) s =
                  (if p_384 divides n then 0
                   else (2 EXP 768 * inverse_mod p_384 n) MOD p_384))
          (MAYCHANGE [RIP; RDI; RSI; RAX; RBX; RCX; RDX; RBP;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(z,8 * 6);
                      memory :> bytes(stackpointer,336)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  X86_SUBROUTINE_SIM_TAC
      ((GEN_REWRITE_CONV RAND_CONV [bignum_montinv_p384_tmc] THENC
        REWRITE_CONV[BUTLAST_CLAUSES])
       `BUTLAST bignum_montinv_p384_tmc`,
       BIGNUM_MONTINV_P384_EXEC,
       0x11,
       (GEN_REWRITE_CONV RAND_CONV [bignum_montinv_p384_tmc] THENC TRIM_LIST_CONV)
       `TRIM_LIST (17,18) bignum_montinv_p384_tmc`,
       CORE_INV_P384_CORRECT)
      [`read RDI s`; `read RSI s`;
       `read (memory :> bytes(read RSI s,8 * 6)) s`;
       `pc + 0x11`; `stackpointer:int64`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let BIGNUM_MONTINV_P384_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 384),384))
            [(word pc,LENGTH bignum_montinv_p384_tmc); (x,8 * 6)] /\
        ALL (nonoverlapping (z,8 * 6))
            [(word_sub stackpointer (word 384),392); (word pc,LENGTH bignum_montinv_p384_tmc)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montinv_p384_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,6) s =
                  (if p_384 divides n then 0
                   else (2 EXP 768 * inverse_mod p_384 n) MOD p_384))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                    memory :> bytes(word_sub stackpointer (word 384),384)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_montinv_p384_tmc
     BIGNUM_MONTINV_P384_CORRECT
      `[RBX; RBP; R12; R13; R14; R15]` 384);;

let BIGNUM_MONTINV_P384_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 384),384))
            [(word pc,LENGTH bignum_montinv_p384_mc); (x,8 * 6)] /\
        ALL (nonoverlapping (z,8 * 6))
            [(word_sub stackpointer (word 384),392); (word pc,LENGTH bignum_montinv_p384_mc)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montinv_p384_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,6) s =
                  (if p_384 divides n then 0
                   else (2 EXP 768 * inverse_mod p_384 n) MOD p_384))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                    memory :> bytes(word_sub stackpointer (word 384),384)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTINV_P384_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_montinv_p384_windows_mc = define_from_elf "bignum_montinv_p384_windows_mc"
      "x86/p384/bignum_montinv_p384.obj";;

let bignum_montinv_p384_windows_tmc = define_trimmed "bignum_montinv_p384_windows_tmc" bignum_montinv_p384_windows_mc;;

let BIGNUM_MONTINV_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 400),400))
            [(word pc,LENGTH bignum_montinv_p384_windows_tmc); (x,8 * 6)] /\
        ALL (nonoverlapping (z,8 * 6))
            [(word_sub stackpointer (word 400),408); (word pc,LENGTH bignum_montinv_p384_windows_tmc)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montinv_p384_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,6) s =
                  (if p_384 divides n then 0
                   else (2 EXP 768 * inverse_mod p_384 n) MOD p_384))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                    memory :> bytes(word_sub stackpointer (word 400),400)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_montinv_p384_windows_tmc bignum_montinv_p384_tmc
     BIGNUM_MONTINV_P384_CORRECT
      `[RBX; RBP; R12; R13; R14; R15]` 384);;

let BIGNUM_MONTINV_P384_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 400),400))
            [(word pc,LENGTH bignum_montinv_p384_windows_mc); (x,8 * 6)] /\
        ALL (nonoverlapping (z,8 * 6))
            [(word_sub stackpointer (word 400),408); (word pc,LENGTH bignum_montinv_p384_windows_mc)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montinv_p384_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,6) s =
                  (if p_384 divides n then 0
                   else (2 EXP 768 * inverse_mod p_384 n) MOD p_384))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                    memory :> bytes(word_sub stackpointer (word 400),400)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTINV_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

