(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Double (fresh and basepoint) scalar multiplication for edwards25519.      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/bignum_inv_p25519.ml";;
needs "common/ecencoding.ml";;

needs "EC/edwards25519.ml";;
needs "EC/exprojective.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The code; however, the text segment here contains data at the end         *)
(* so we manually split that off to avoid confusing the decoder.             *)
(* ------------------------------------------------------------------------- *)

(**** print_coda_from_elf (-1) "x86/curve25519/edwards25519_scalarmuldouble_alt.o";;
 ****)

let edwards25519_scalarmuldouble_alt_mc,edwards25519_scalarmuldouble_alt_data =
  define_coda_literal_from_elf
  "edwards25519_scalarmuldouble_alt_mc" "edwards25519_scalarmuldouble_alt_data"
  "x86/curve25519/edwards25519_scalarmuldouble_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xc0; 0x05; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 1472)) *)
  0x48; 0x89; 0xbc; 0x24; 0xb8; 0x05; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,1464))) (% rdi) *)
  0x4c; 0x8b; 0x01;        (* MOV (% r8) (Memop Quadword (%% (rcx,0))) *)
  0x4c; 0x8b; 0x49; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rcx,8))) *)
  0x4c; 0x8b; 0x51; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rcx,16))) *)
  0x4c; 0x8b; 0x59; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0xbc; 0x20; 0xe9; 0xd9; 0xa0; 0xb5; 0x6f; 0xf5; 0xc7;
                           (* MOV (% r12) (Imm64 (word 14408545408720169248)) *)
  0x49; 0xbd; 0xd5; 0xa1; 0xcb; 0x70; 0x93; 0xb9; 0x90; 0xe1;
                           (* MOV (% r13) (Imm64 (word 16253695098083844565)) *)
  0x49; 0xbe; 0x87; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88;
                           (* MOV (% r14) (Imm64 (word 9838263505978427527)) *)
  0x49; 0xbf; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88;
                           (* MOV (% r15) (Imm64 (word 9838263505978427528)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x80;
                           (* MOV (% rax) (Imm64 (word 9223372036854775808)) *)
  0x48; 0xbb; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88; 0x08;
                           (* MOV (% rbx) (Imm64 (word 614891469123651720)) *)
  0x4c; 0x39; 0xd8;        (* CMP (% rax) (% r11) *)
  0x4d; 0x0f; 0x43; 0xe7;  (* CMOVAE (% r12) (% r15) *)
  0x4d; 0x0f; 0x43; 0xef;  (* CMOVAE (% r13) (% r15) *)
  0x4d; 0x0f; 0x43; 0xf7;  (* CMOVAE (% r14) (% r15) *)
  0x4c; 0x0f; 0x43; 0xfb;  (* CMOVAE (% r15) (% rbx) *)
  0x4d; 0x01; 0xe0;        (* ADD (% r8) (% r12) *)
  0x4d; 0x11; 0xe9;        (* ADC (% r9) (% r13) *)
  0x4d; 0x11; 0xf2;        (* ADC (% r10) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r11) *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0xbc; 0x20; 0xe9; 0xd9; 0xa0; 0xb5; 0x6f; 0xf5; 0xc7;
                           (* MOV (% r12) (Imm64 (word 14408545408720169248)) *)
  0x49; 0xbd; 0xd5; 0xa1; 0xcb; 0x70; 0x93; 0xb9; 0x90; 0xe1;
                           (* MOV (% r13) (Imm64 (word 16253695098083844565)) *)
  0x49; 0xbe; 0x87; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88;
                           (* MOV (% r14) (Imm64 (word 9838263505978427527)) *)
  0x49; 0xbf; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88;
                           (* MOV (% r15) (Imm64 (word 9838263505978427528)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x80;
                           (* MOV (% rax) (Imm64 (word 9223372036854775808)) *)
  0x48; 0xbb; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88; 0x88; 0x08;
                           (* MOV (% rbx) (Imm64 (word 614891469123651720)) *)
  0x4c; 0x39; 0xd8;        (* CMP (% rax) (% r11) *)
  0x4d; 0x0f; 0x43; 0xe7;  (* CMOVAE (% r12) (% r15) *)
  0x4d; 0x0f; 0x43; 0xef;  (* CMOVAE (% r13) (% r15) *)
  0x4d; 0x0f; 0x43; 0xf7;  (* CMOVAE (% r14) (% r15) *)
  0x4c; 0x0f; 0x43; 0xfb;  (* CMOVAE (% r15) (% rbx) *)
  0x4d; 0x01; 0xe0;        (* ADD (% r8) (% r12) *)
  0x4d; 0x11; 0xe9;        (* ADC (% r9) (% r13) *)
  0x4d; 0x11; 0xf2;        (* ADC (% r10) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x02;        (* MOV (% r8) (Memop Quadword (%% (rdx,0))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x8b; 0x4a; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rdx,8))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x8b; 0x52; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rdx,16))) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x4c; 0x8b; 0x5a; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rdx,24))) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x4c; 0x11; 0xcb;        (* ADC (% rbx) (% r9) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x11; 0xde;        (* ADC (% rsi) (% r11) *)
  0x49; 0x0f; 0x43; 0xc0;  (* CMOVAE (% rax) (% r8) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,416))) (% rax) *)
  0x49; 0x0f; 0x43; 0xd9;  (* CMOVAE (% rbx) (% r9) *)
  0x48; 0x89; 0x9c; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,424))) (% rbx) *)
  0x49; 0x0f; 0x43; 0xca;  (* CMOVAE (% rcx) (% r10) *)
  0x48; 0x89; 0x8c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,432))) (% rcx) *)
  0x49; 0x0f; 0x43; 0xf3;  (* CMOVAE (% rsi) (% r11) *)
  0x48; 0x89; 0xb4; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,440))) (% rsi) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x42; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rdx,32))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x8b; 0x4a; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rdx,40))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x8b; 0x52; 0x30;  (* MOV (% r10) (Memop Quadword (%% (rdx,48))) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x4c; 0x8b; 0x5a; 0x38;  (* MOV (% r11) (Memop Quadword (%% (rdx,56))) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x4c; 0x11; 0xcb;        (* ADC (% rbx) (% r9) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x11; 0xde;        (* ADC (% rsi) (% r11) *)
  0x49; 0x0f; 0x43; 0xc0;  (* CMOVAE (% rax) (% r8) *)
  0x48; 0x89; 0x84; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,448))) (% rax) *)
  0x49; 0x0f; 0x43; 0xd9;  (* CMOVAE (% rbx) (% r9) *)
  0x48; 0x89; 0x9c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,456))) (% rbx) *)
  0x49; 0x0f; 0x43; 0xca;  (* CMOVAE (% rcx) (% r10) *)
  0x48; 0x89; 0x8c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,464))) (% rcx) *)
  0x49; 0x0f; 0x43; 0xf3;  (* CMOVAE (% rsi) (% r11) *)
  0x48; 0x89; 0xb4; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,472))) (% rsi) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x89; 0x84; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,480))) (% rax) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x89; 0x84; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,488))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0xf0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,496))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,504))) (% rax) *)
  0x48; 0x8d; 0xbc; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,512)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,416)) *)
  0x48; 0x8d; 0xac; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,448)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x65; 0x00;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,0))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x65; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,8))) *)
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
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,544)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,416)) *)
  0xe8; 0xff; 0x2c; 0x00; 0x00;
                           (* CALL (Imm32 (word 11519)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,672)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,416)) *)
  0x48; 0x8d; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,544)) *)
  0xe8; 0x6c; 0x49; 0x00; 0x00;
                           (* CALL (Imm32 (word 18796)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x03; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,800)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,544)) *)
  0xe8; 0xcd; 0x2c; 0x00; 0x00;
                           (* CALL (Imm32 (word 11469)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xa0; 0x03; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,928)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,416)) *)
  0x48; 0x8d; 0xac; 0x24; 0x20; 0x03; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,800)) *)
  0xe8; 0x3a; 0x49; 0x00; 0x00;
                           (* CALL (Imm32 (word 18746)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x04; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,1056)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,672)) *)
  0xe8; 0x9b; 0x2c; 0x00; 0x00;
                           (* CALL (Imm32 (word 11419)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xa0; 0x04; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,1184)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,416)) *)
  0x48; 0x8d; 0xac; 0x24; 0x20; 0x04; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,1056)) *)
  0xe8; 0x08; 0x49; 0x00; 0x00;
                           (* CALL (Imm32 (word 18696)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x05; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,1312)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x20; 0x03; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,800)) *)
  0xe8; 0x69; 0x2c; 0x00; 0x00;
                           (* CALL (Imm32 (word 11369)) *)
  0x48; 0xc7; 0xc0; 0xfc; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm32 (word 252)) *)
  0x48; 0x89; 0x84; 0x24; 0xb0; 0x05; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,1456))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xc1; 0xe8; 0x3c;  (* SHR (% rax) (Imm8 (word 60)) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x05; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,1440))) (% rax) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x41; 0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 1)) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0x8d; 0x2d; 0x38; 0x6b; 0x00; 0x00;
                           (* LEA (% rbp) (Riprel (word 27448)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x01;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 1)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x02;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 2)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x03;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 3)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x04;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 4)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x05;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 5)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x06;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 6)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x07;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 7)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x08;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 8)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x89; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rax) *)
  0x48; 0x89; 0x9c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% rbx) *)
  0x48; 0x89; 0x8c; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% rdx) *)
  0x4c; 0x89; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xc1; 0xe8; 0x3c;  (* SHR (% rax) (Imm8 (word 60)) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x05; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,1440))) (% rax) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x41; 0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 1)) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x48; 0x8d; 0xac; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,448)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x01;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 1)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x02;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 2)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x03;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 3)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x04;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 4)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x05;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 5)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x06;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 6)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x07;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 7)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x08;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 8)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x48; 0x89; 0x5c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rbx) *)
  0x48; 0x89; 0x4c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rcx) *)
  0x48; 0x89; 0x54; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rdx) *)
  0x4c; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r11) *)
  0x48; 0x8d; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,416)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x01;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 1)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x02;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 2)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x03;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 3)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x04;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 4)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x05;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 5)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x06;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 6)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x07;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 7)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x08;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 8)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x48; 0x89; 0x5c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rbx) *)
  0x48; 0x89; 0x4c; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rcx) *)
  0x48; 0x89; 0x54; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rdx) *)
  0x4c; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r11) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0xac; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,192)) *)
  0xe8; 0xb2; 0x52; 0x00; 0x00;
                           (* CALL (Imm32 (word 21170)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x05; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,1456))) *)
  0x48; 0x83; 0xe8; 0x04;  (* SUB (% rax) (Imm8 (word 4)) *)
  0x48; 0x89; 0x84; 0x24; 0xb0; 0x05; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,1456))) (% rax) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,288)) *)
  0xe8; 0xa8; 0x31; 0x00; 0x00;
                           (* CALL (Imm32 (word 12712)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x05; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,1456))) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0xc1; 0xe8; 0x06;  (* SHR (% rax) (Imm8 (word 6)) *)
  0x48; 0x8b; 0x44; 0xc4; 0x20;
                           (* MOV (% rax) (Memop Quadword (%%%% (rsp,3,rax,&32))) *)
  0x48; 0xd3; 0xe8;        (* SHR (% rax) (% cl) *)
  0x48; 0x83; 0xe0; 0x0f;  (* AND (% rax) (Imm8 (word 15)) *)
  0x48; 0x83; 0xe8; 0x08;  (* SUB (% rax) (Imm8 (word 8)) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x31; 0xc8;        (* XOR (% rax) (% rcx) *)
  0x48; 0x29; 0xc8;        (* SUB (% rax) (% rcx) *)
  0x48; 0x89; 0x8c; 0x24; 0xa8; 0x05; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,1448))) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x05; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,1440))) (% rax) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x41; 0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 1)) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0x8d; 0x2d; 0x23; 0x61; 0x00; 0x00;
                           (* LEA (% rbp) (Riprel (word 24867)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x01;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 1)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x02;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 2)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x03;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 3)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x04;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 4)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x05;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 5)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x06;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 6)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x07;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 7)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x08;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 8)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x8b; 0xbc; 0x24; 0xa8; 0x05; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,1448))) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x48; 0x89; 0xc6;        (* MOV (% rsi) (% rax) *)
  0x49; 0x0f; 0x45; 0xf0;  (* CMOVNE (% rsi) (% r8) *)
  0x4c; 0x0f; 0x45; 0xc0;  (* CMOVNE (% r8) (% rax) *)
  0x48; 0x89; 0xb4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rsi) *)
  0x4c; 0x89; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% r8) *)
  0x48; 0x89; 0xde;        (* MOV (% rsi) (% rbx) *)
  0x49; 0x0f; 0x45; 0xf1;  (* CMOVNE (% rsi) (% r9) *)
  0x4c; 0x0f; 0x45; 0xcb;  (* CMOVNE (% r9) (% rbx) *)
  0x48; 0x89; 0xb4; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% rsi) *)
  0x4c; 0x89; 0x8c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% r9) *)
  0x48; 0x89; 0xce;        (* MOV (% rsi) (% rcx) *)
  0x49; 0x0f; 0x45; 0xf2;  (* CMOVNE (% rsi) (% r10) *)
  0x4c; 0x0f; 0x45; 0xd1;  (* CMOVNE (% r10) (% rcx) *)
  0x48; 0x89; 0xb4; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% rsi) *)
  0x4c; 0x89; 0x94; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% r10) *)
  0x48; 0x89; 0xd6;        (* MOV (% rsi) (% rdx) *)
  0x49; 0x0f; 0x45; 0xf3;  (* CMOVNE (% rsi) (% r11) *)
  0x4c; 0x0f; 0x45; 0xda;  (* CMOVNE (% r11) (% rdx) *)
  0x48; 0x89; 0xb4; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% rsi) *)
  0x4c; 0x89; 0x9c; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% r11) *)
  0x49; 0x31; 0xfc;        (* XOR (% r12) (% rdi) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0x49; 0x31; 0xfe;        (* XOR (% r14) (% rdi) *)
  0x49; 0x31; 0xff;        (* XOR (% r15) (% rdi) *)
  0x48; 0x83; 0xe7; 0x25;  (* AND (% rdi) (Imm8 (word 37)) *)
  0x49; 0x29; 0xfc;        (* SUB (% r12) (% rdi) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x05; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,1456))) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0xc1; 0xe8; 0x06;  (* SHR (% rax) (Imm8 (word 6)) *)
  0x48; 0x8b; 0x04; 0xc4;  (* MOV (% rax) (Memop Quadword (%%% (rsp,3,rax))) *)
  0x48; 0xd3; 0xe8;        (* SHR (% rax) (% cl) *)
  0x48; 0x83; 0xe0; 0x0f;  (* AND (% rax) (Imm8 (word 15)) *)
  0x48; 0x83; 0xe8; 0x08;  (* SUB (% rax) (Imm8 (word 8)) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x31; 0xc8;        (* XOR (% rax) (% rcx) *)
  0x48; 0x29; 0xc8;        (* SUB (% rax) (% rcx) *)
  0x48; 0x89; 0x8c; 0x24; 0xa8; 0x05; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,1448))) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x05; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,1440))) (% rax) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x41; 0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 1)) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x48; 0x8d; 0xac; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,448)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x01;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 1)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x02;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 2)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x03;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 3)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x04;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 4)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x05;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 5)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x06;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 6)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x07;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 7)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x08;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 8)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x48; 0x89; 0x5c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rbx) *)
  0x48; 0x89; 0x4c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rcx) *)
  0x48; 0x89; 0x54; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rdx) *)
  0x4c; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r11) *)
  0x48; 0x8d; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,416)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x01;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 1)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x02;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 2)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x03;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 3)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x04;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 4)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x05;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 5)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x06;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 6)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x07;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 7)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x81; 0xc5; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 128)) *)
  0x48; 0x83; 0xbc; 0x24; 0xa0; 0x05; 0x00; 0x00; 0x08;
                           (* CMP (Memop Quadword (%% (rsp,1440))) (Imm8 (word 8)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x60;  (* MOV (% rsi) (Memop Quadword (%% (rbp,96))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x68;  (* MOV (% rsi) (Memop Quadword (%% (rbp,104))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x70;  (* MOV (% rsi) (Memop Quadword (%% (rbp,112))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x78;  (* MOV (% rsi) (Memop Quadword (%% (rbp,120))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0xbc; 0x24; 0xa8; 0x05; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,1448))) *)
  0x48; 0x31; 0xf8;        (* XOR (% rax) (% rdi) *)
  0x48; 0x31; 0xfb;        (* XOR (% rbx) (% rdi) *)
  0x48; 0x31; 0xf9;        (* XOR (% rcx) (% rdi) *)
  0x48; 0x31; 0xfa;        (* XOR (% rdx) (% rdi) *)
  0x49; 0x31; 0xf8;        (* XOR (% r8) (% rdi) *)
  0x49; 0x31; 0xf9;        (* XOR (% r9) (% rdi) *)
  0x49; 0x31; 0xfa;        (* XOR (% r10) (% rdi) *)
  0x49; 0x31; 0xfb;        (* XOR (% r11) (% rdi) *)
  0x48; 0x83; 0xe7; 0x25;  (* AND (% rdi) (Imm8 (word 37)) *)
  0x48; 0x29; 0xf8;        (* SUB (% rax) (% rdi) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x48; 0x89; 0x5c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rbx) *)
  0x48; 0x89; 0x4c; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rcx) *)
  0x48; 0x89; 0x54; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rdx) *)
  0x49; 0x29; 0xf8;        (* SUB (% r8) (% rdi) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r11) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,288)) *)
  0xe8; 0x03; 0x27; 0x00; 0x00;
                           (* CALL (Imm32 (word 9987)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0xac; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,192)) *)
  0xe8; 0xcd; 0x47; 0x00; 0x00;
                           (* CALL (Imm32 (word 18381)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,288)) *)
  0xe8; 0xd7; 0x26; 0x00; 0x00;
                           (* CALL (Imm32 (word 9943)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,288)) *)
  0xe8; 0x86; 0x17; 0x00; 0x00;
                           (* CALL (Imm32 (word 6022)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,288)) *)
  0x48; 0x8d; 0x6c; 0x24; 0x40;
                           (* LEA (% rbp) (%% (rsp,64)) *)
  0xe8; 0xf6; 0x33; 0x00; 0x00;
                           (* CALL (Imm32 (word 13302)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x05; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,1456))) *)
  0x48; 0x85; 0xc0;        (* TEST (% rax) (% rax) *)
  0x0f; 0x85; 0xc6; 0xf4; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294964422)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,416)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,352)) *)
  0x48; 0x89; 0xbc; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rdi) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x8d; 0x48; 0xed;  (* LEA (% rcx) (%% (rax,18446744073709551597)) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x89; 0x0c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rax) *)
  0x48; 0x0f; 0xba; 0xf0; 0x3f;
                           (* BTR (% rax) (Imm8 (word 63)) *)
  0x48; 0x89; 0x44; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rax) *)
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
  0x48; 0x89; 0x54; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rdx) *)
  0x48; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r9) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x48; 0xb8; 0x99; 0x20; 0x02; 0x75; 0x23; 0x9e; 0xf9; 0xa0;
                           (* MOV (% rax) (Imm64 (word 11599476190393540761)) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x48; 0xb8; 0x95; 0x25; 0x13; 0x1d; 0x3f; 0x8f; 0xc6; 0xa8;
                           (* MOV (% rax) (Imm64 (word 12161565344994108821)) *)
  0x48; 0x89; 0x44; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rax) *)
  0x48; 0xb8; 0x42; 0x52; 0xac; 0x05; 0x38; 0x89; 0x6c; 0x6c;
                           (* MOV (% rax) (Imm64 (word 7812770327287321154)) *)
  0x48; 0x89; 0x44; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rax) *)
  0x48; 0xb8; 0x15; 0x06; 0x77; 0x41; 0xb2; 0x08; 0x65; 0x27;
                           (* MOV (% rax) (Imm64 (word 2838684701822486037)) *)
  0x48; 0x89; 0x44; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rax) *)
  0x48; 0xc7; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00; 0x0a; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (Imm32 (word 10)) *)
  0x48; 0xc7; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (Imm32 (word 1)) *)
  0xe9; 0x07; 0x04; 0x00; 0x00;
                           (* JMP (Imm32 (word 1031)) *)
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
  0x48; 0x89; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rdi) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x4c; 0x21; 0xe8;        (* AND (% rax) (% r13) *)
  0x4c; 0x89; 0xf6;        (* MOV (% rsi) (% r14) *)
  0x4c; 0x21; 0xfe;        (* AND (% rsi) (% r15) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x89; 0xb4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rsi) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd7;        (* ADC (% rdi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xee; 0x3b;
                           (* SHRD (% rsi) (% rbp) (Imm8 (word 59)) *)
  0x48; 0x89; 0x74; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x0f; 0xac; 0xfd; 0x3b;
                           (* SHRD (% rbp) (% rdi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0xc1; 0xfd; 0x3f;  (* SAR (% rbp) (Imm8 (word 63)) *)
  0x4c; 0x21; 0xc5;        (* AND (% rbp) (% r8) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0xc1; 0xfa; 0x3f;  (* SAR (% rdx) (Imm8 (word 63)) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x89; 0x74; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rsi) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x48; 0x89; 0xc6;        (* MOV (% rsi) (% rax) *)
  0x48; 0xc1; 0xfe; 0x3f;  (* SAR (% rsi) (Imm8 (word 63)) *)
  0x4c; 0x21; 0xe6;        (* AND (% rsi) (% r12) *)
  0x48; 0xf7; 0xde;        (* NEG (% rsi) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0xc1; 0xfa; 0x3f;  (* SAR (% rdx) (Imm8 (word 63)) *)
  0x4c; 0x21; 0xf2;        (* AND (% rdx) (% r14) *)
  0x48; 0x29; 0xd6;        (* SUB (% rsi) (% rdx) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xdf; 0x3b;
                           (* SHRD (% rdi) (% rbx) (Imm8 (word 59)) *)
  0x48; 0x89; 0x7c; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rdi) *)
  0x48; 0x0f; 0xac; 0xf3; 0x3b;
                           (* SHRD (% rbx) (% rsi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x5c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rbx) *)
  0x48; 0x8b; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x8b; 0xac; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,136))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x5c; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rbx) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x89; 0x6c; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rbp) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rcx) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x89; 0x74; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rsi) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x89; 0x6c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x4c; 0x21; 0xc3;        (* AND (% rbx) (% r8) *)
  0x48; 0xf7; 0xdb;        (* NEG (% rbx) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x48; 0x29; 0xd3;        (* SUB (% rbx) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x48; 0x89; 0xd3;        (* MOV (% rbx) (% rdx) *)
  0x48; 0x0f; 0xa4; 0xca; 0x01;
                           (* SHLD (% rdx) (% rcx) (Imm8 (word 1)) *)
  0x48; 0xc1; 0xfb; 0x3f;  (* SAR (% rbx) (Imm8 (word 63)) *)
  0x48; 0x01; 0xda;        (* ADD (% rdx) (% rbx) *)
  0xb8; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 19)) *)
  0x48; 0xf7; 0xea;        (* IMUL2 (% rdx,% rax) (% rdx) *)
  0x4c; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4c; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x11; 0xd8;        (* ADC (% r8) (% rbx) *)
  0x4c; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r8) *)
  0x48; 0x11; 0xd9;        (* ADC (% rcx) (% rbx) *)
  0x48; 0xc1; 0xe0; 0x3f;  (* SHL (% rax) (Imm8 (word 63)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x89; 0x4c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rcx) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x4c; 0x89; 0xe9;        (* MOV (% rcx) (% r13) *)
  0x4c; 0x21; 0xe1;        (* AND (% rcx) (% r12) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x4c; 0x89; 0xfa;        (* MOV (% rdx) (% r15) *)
  0x4c; 0x21; 0xf2;        (* AND (% rdx) (% r14) *)
  0x48; 0x29; 0xd1;        (* SUB (% rcx) (% rdx) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xca;        (* ADC (% rdx) (% rcx) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x0f; 0xa4; 0xf2; 0x01;
                           (* SHLD (% rdx) (% rsi) (Imm8 (word 1)) *)
  0x48; 0xc1; 0xf9; 0x3f;  (* SAR (% rcx) (Imm8 (word 63)) *)
  0xb8; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 19)) *)
  0x48; 0x01; 0xca;        (* ADD (% rdx) (% rcx) *)
  0x48; 0xf7; 0xea;        (* IMUL2 (% rdx,% rax) (% rdx) *)
  0x4c; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4c; 0x89; 0x44; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r8) *)
  0x48; 0x11; 0xce;        (* ADC (% rsi) (% rcx) *)
  0x48; 0xc1; 0xe0; 0x3f;  (* SHL (% rax) (Imm8 (word 63)) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x89; 0x74; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rsi) *)
  0x48; 0x8b; 0xb4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x8b; 0x14; 0x24;  (* MOV (% rdx) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x20;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,32))) *)
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
  0x48; 0x89; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rdx) *)
  0x48; 0x89; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% rbx) *)
  0x48; 0x89; 0xbc; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% rdi) *)
  0x48; 0x89; 0x8c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% rcx) *)
  0x4c; 0x8b; 0x24; 0x24;  (* MOV (% r12) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x0f; 0xaf; 0xfc;  (* IMUL (% rdi) (% r12) *)
  0x4c; 0x0f; 0xaf; 0xe2;  (* IMUL (% r12) (% rdx) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x20;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,32))) *)
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
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% r8) *)
  0x48; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x0f; 0xaf; 0xd7;  (* IMUL (% rdx) (% r15) *)
  0x4c; 0x0f; 0xaf; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* IMUL (% r8) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x0f; 0xaf; 0xbc; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* IMUL (% r15) (Memop Quadword (%% (rsp,184))) *)
  0x4d; 0x01; 0xc7;        (* ADD (% r15) (% r8) *)
  0x4c; 0x8d; 0x0c; 0x10;  (* LEA (% r9) (%%% (rax,0,rdx)) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% r10) *)
  0x48; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% r11) *)
  0x4c; 0x0f; 0xaf; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* IMUL (% r10) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x0f; 0xaf; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* IMUL (% r11) (Memop Quadword (%% (rsp,184))) *)
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
  0x48; 0x89; 0xb4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rsi) *)
  0x48; 0xff; 0x8c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* DEC (Memop Quadword (%% (rsp,144))) *)
  0x0f; 0x85; 0xc1; 0xee; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294962881)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x20;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,32))) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x49; 0x29; 0xd1;        (* SUB (% r9) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4c; 0x0f; 0xa4; 0xf8; 0x01;
                           (* SHLD (% rax) (% r15) (Imm8 (word 1)) *)
  0x49; 0xc1; 0xf9; 0x3f;  (* SAR (% r9) (Imm8 (word 63)) *)
  0xbb; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 19)) *)
  0x4a; 0x8d; 0x44; 0x08; 0x01;
                           (* LEA (% rax) (%%%% (rax,0,r9,&1)) *)
  0x48; 0xf7; 0xeb;        (* IMUL2 (% rdx,% rax) (% rbx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xce;        (* ADC (% r14) (% r9) *)
  0x4d; 0x11; 0xcf;        (* ADC (% r15) (% r9) *)
  0x48; 0xc1; 0xe0; 0x3f;  (* SHL (% rax) (Imm8 (word 63)) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x48; 0x0f; 0x49; 0xdd;  (* CMOVNS (% rbx) (% rbp) *)
  0x49; 0x29; 0xdc;        (* SUB (% r12) (% rbx) *)
  0x49; 0x19; 0xed;        (* SBB (% r13) (% rbp) *)
  0x49; 0x19; 0xee;        (* SBB (% r14) (% rbp) *)
  0x49; 0x19; 0xef;        (* SBB (% r15) (% rbp) *)
  0x49; 0x0f; 0xba; 0xf7; 0x3f;
                           (* BTR (% r15) (Imm8 (word 63)) *)
  0x48; 0x8b; 0xbc; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,192))) *)
  0x4c; 0x89; 0x27;        (* MOV (Memop Quadword (%% (rdi,0))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r13) *)
  0x4c; 0x89; 0x77; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r15) *)
  0x48; 0x8b; 0xbc; 0x24; 0xb8; 0x05; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,1464))) *)
  0x48; 0x8d; 0xb4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,288)) *)
  0x48; 0x8d; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,416)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x65; 0x00;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,0))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x65; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,8))) *)
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
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x8b; 0xbc; 0x24; 0xb8; 0x05; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,1464))) *)
  0x48; 0x83; 0xc7; 0x20;  (* ADD (% rdi) (Imm8 (word 32)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,320)) *)
  0x48; 0x8d; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* LEA (% rbp) (%% (rsp,416)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x65; 0x00;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,0))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x65; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,8))) *)
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
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x81; 0xc4; 0xc0; 0x05; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 1472)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x48; 0x81; 0xec; 0xa0; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 160)) *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x46; 0x20;  (* ADD (% r8) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x13; 0x4e; 0x28;  (* ADC (% r9) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x13; 0x56; 0x30;  (* ADC (% r10) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x13; 0x5e; 0x38;  (* ADC (% r11) (Memop Quadword (%% (rsi,56))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x66; 0x48;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x66; 0x50;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x66; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0x66; 0x50;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0x66; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0x66; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x66; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r11) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x66; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x66; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x66; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r11) *)
  0x4c; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,32))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4d; 0x01; 0xc0;        (* ADD (% r8) (% r8) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x28;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,40))) *)
  0x4d; 0x11; 0xc9;        (* ADC (% r9) (% r9) *)
  0x4c; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,48))) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x38;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,56))) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
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
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x08;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x4c; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x44; 0x24; 0x60;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x68;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x13; 0x54; 0x24; 0x70;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x58;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x78;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,120))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r11) *)
  0x4c; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x44; 0x24; 0x60;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x68;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,104))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x70;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x1b; 0x44; 0x24; 0x78;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x4c; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,32))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x44; 0x24; 0x40;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x28;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x48;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x13; 0x54; 0x24; 0x50;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x38;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x58;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,88))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r11) *)
  0x4c; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x04; 0x24;  (* SUB (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x08;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,8))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x10;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x1b; 0x44; 0x24; 0x18;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r10) *)
  0x48; 0x89; 0x44; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r9) *)
  0x4c; 0x89; 0x57; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% r9) *)
  0x4c; 0x89; 0x57; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x47; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% r9) *)
  0x4c; 0x89; 0x57; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x81; 0xc4; 0xa0; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 160)) *)
  0xc3;                    (* RET *)
  0x48; 0x81; 0xec; 0xa0; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 160)) *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x46; 0x20;  (* ADD (% r8) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x13; 0x4e; 0x28;  (* ADC (% r9) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x13; 0x56; 0x30;  (* ADC (% r10) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x13; 0x5e; 0x38;  (* ADC (% r11) (Memop Quadword (%% (rsi,56))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x66; 0x48;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x66; 0x50;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x66; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0x66; 0x50;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0x66; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0x66; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x66; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r11) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x66; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x66; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x66; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r11) *)
  0x4c; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,32))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4d; 0x01; 0xc0;        (* ADD (% r8) (% r8) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x28;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,40))) *)
  0x4d; 0x11; 0xc9;        (* ADC (% r9) (% r9) *)
  0x4c; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,48))) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x38;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,56))) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
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
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x08;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x4c; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x44; 0x24; 0x60;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x68;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x13; 0x54; 0x24; 0x70;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x58;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x78;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,120))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r11) *)
  0x4c; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x44; 0x24; 0x60;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x68;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,104))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x70;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x1b; 0x44; 0x24; 0x78;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x4c; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,32))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x44; 0x24; 0x40;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x28;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x48;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x13; 0x54; 0x24; 0x50;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x38;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x58;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,88))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r11) *)
  0x4c; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x04; 0x24;  (* SUB (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x08;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,8))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x10;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x1b; 0x44; 0x24; 0x18;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r10) *)
  0x48; 0x89; 0x44; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r9) *)
  0x4c; 0x89; 0x57; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% r9) *)
  0x4c; 0x89; 0x57; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x81; 0xc4; 0xa0; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 160)) *)
  0xc3;                    (* RET *)
  0x48; 0x81; 0xec; 0xc0; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 192)) *)
  0x48; 0x8b; 0x46; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0xf7; 0x65; 0x60;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,96))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0xf7; 0x65; 0x68;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,104))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0xf7; 0x65; 0x60;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,96))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0xf7; 0x65; 0x70;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,112))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0xf7; 0x65; 0x68;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,104))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0xf7; 0x65; 0x60;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,96))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0xf7; 0x65; 0x78;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,120))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0xf7; 0x65; 0x70;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,112))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0xf7; 0x65; 0x68;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,104))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0x65; 0x60;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,96))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0xf7; 0x65; 0x78;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,120))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0xf7; 0x65; 0x70;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,112))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0x65; 0x68;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,104))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0xf7; 0x65; 0x78;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,120))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0x65; 0x70;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,112))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0x65; 0x78;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,120))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x4c; 0x8b; 0x46; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rsi,32))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x06;        (* SUB (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x1b; 0x4e; 0x08;  (* SBB (% r9) (Memop Quadword (%% (rsi,8))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x56; 0x30;  (* MOV (% r10) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x1b; 0x56; 0x10;  (* SBB (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x1b; 0x46; 0x18;  (* SBB (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r10) *)
  0x48; 0x89; 0x44; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rax) *)
  0x4c; 0x8b; 0x45; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rbp,32))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x45; 0x00;  (* SUB (% r8) (Memop Quadword (%% (rbp,0))) *)
  0x4c; 0x8b; 0x4d; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x1b; 0x4d; 0x08;  (* SBB (% r9) (Memop Quadword (%% (rbp,8))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x55; 0x30;  (* MOV (% r10) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x1b; 0x55; 0x10;  (* SBB (% r10) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x8b; 0x45; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rbp,56))) *)
  0x48; 0x1b; 0x45; 0x18;  (* SBB (% rax) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x4c; 0x8b; 0x46; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rsi,32))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x06;        (* ADD (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x13; 0x4e; 0x08;  (* ADC (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x56; 0x30;  (* MOV (% r10) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x13; 0x56; 0x10;  (* ADC (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x5e; 0x38;  (* MOV (% r11) (Memop Quadword (%% (rsi,56))) *)
  0x4c; 0x13; 0x5e; 0x18;  (* ADC (% r11) (Memop Quadword (%% (rsi,24))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r11) *)
  0x4c; 0x8b; 0x45; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rbp,32))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x45; 0x00;  (* ADD (% r8) (Memop Quadword (%% (rbp,0))) *)
  0x4c; 0x8b; 0x4d; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x13; 0x4d; 0x08;  (* ADC (% r9) (Memop Quadword (%% (rbp,8))) *)
  0x4c; 0x8b; 0x55; 0x30;  (* MOV (% r10) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x13; 0x55; 0x10;  (* ADC (% r10) (Memop Quadword (%% (rbp,16))) *)
  0x4c; 0x8b; 0x5d; 0x38;  (* MOV (% r11) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x13; 0x5d; 0x18;  (* ADC (% r11) (Memop Quadword (%% (rbp,24))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r11) *)
  0x4c; 0x8b; 0x45; 0x40;  (* MOV (% r8) (Memop Quadword (%% (rbp,64))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4d; 0x01; 0xc0;        (* ADD (% r8) (% r8) *)
  0x4c; 0x8b; 0x4d; 0x48;  (* MOV (% r9) (Memop Quadword (%% (rbp,72))) *)
  0x4d; 0x11; 0xc9;        (* ADC (% r9) (% r9) *)
  0x4c; 0x8b; 0x55; 0x50;  (* MOV (% r10) (Memop Quadword (%% (rbp,80))) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4c; 0x8b; 0x5d; 0x58;  (* MOV (% r11) (Memop Quadword (%% (rbp,88))) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x40;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x48;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x50;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x58;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r11) *)
  0x48; 0xb8; 0x59; 0xf1; 0xb2; 0x26; 0x94; 0x9b; 0xd6; 0xeb;
                           (* MOV (% rax) (Imm64 (word 16993941304535871833)) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x48; 0xb8; 0x56; 0xb1; 0x83; 0x82; 0x9a; 0x14; 0xe0; 0x00;
                           (* MOV (% rax) (Imm64 (word 63073048630374742)) *)
  0x48; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rax) *)
  0x48; 0xb8; 0x30; 0xd1; 0xf3; 0xee; 0xf2; 0x80; 0x8e; 0x19;
                           (* MOV (% rax) (Imm64 (word 1841551078520508720)) *)
  0x48; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rax) *)
  0x48; 0xb8; 0xe7; 0xfc; 0xdf; 0x56; 0xdc; 0xd9; 0x06; 0x24;
                           (* MOV (% rax) (Imm64 (word 2596001775599221991)) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x24; 0x24;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x64; 0x24; 0x08;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x24; 0x24;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x64; 0x24; 0x08;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x24; 0x24;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x64; 0x24; 0x08;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x24; 0x24;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x64; 0x24; 0x08;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r11) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r11) *)
  0x4c; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,96))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x44; 0x24; 0x20;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x68;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x28;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,40))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x54; 0x24; 0x70;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x30;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x1b; 0x44; 0x24; 0x38;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x48; 0x89; 0x44; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rax) *)
  0x4c; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,96))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x44; 0x24; 0x20;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x68;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x28;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x70;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x13; 0x54; 0x24; 0x30;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x78;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x38;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,56))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r11) *)
  0x4c; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x44; 0x24; 0x40;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x48;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,72))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x50;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x1b; 0x44; 0x24; 0x58;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r10) *)
  0x48; 0x89; 0x44; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rax) *)
  0x4c; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x44; 0x24; 0x40;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x48;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x13; 0x54; 0x24; 0x50;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x58;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,88))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r11) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x47; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% r9) *)
  0x4c; 0x89; 0x57; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% r11) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,184))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r9) *)
  0x4c; 0x89; 0x57; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x60;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x68;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x70;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xf7; 0x64; 0x24; 0x78;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% r9) *)
  0x4c; 0x89; 0x57; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r11) *)
  0x48; 0x81; 0xc4; 0xc0; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 192)) *)
  0xc3;                    (* RET *)
  0x48; 0x81; 0xec; 0xc0; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 192)) *)
  0x4c; 0x8b; 0x46; 0x40;  (* MOV (% r8) (Memop Quadword (%% (rsi,64))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4d; 0x01; 0xc0;        (* ADD (% r8) (% r8) *)
  0x4c; 0x8b; 0x4e; 0x48;  (* MOV (% r9) (Memop Quadword (%% (rsi,72))) *)
  0x4d; 0x11; 0xc9;        (* ADC (% r9) (% r9) *)
  0x4c; 0x8b; 0x56; 0x50;  (* MOV (% r10) (Memop Quadword (%% (rsi,80))) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4c; 0x8b; 0x5e; 0x58;  (* MOV (% r11) (Memop Quadword (%% (rsi,88))) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x4c; 0x8b; 0x46; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rsi,32))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x06;        (* SUB (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x1b; 0x4e; 0x08;  (* SBB (% r9) (Memop Quadword (%% (rsi,8))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x56; 0x30;  (* MOV (% r10) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x1b; 0x56; 0x10;  (* SBB (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x1b; 0x46; 0x18;  (* SBB (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r10) *)
  0x48; 0x89; 0x44; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rax) *)
  0x4c; 0x8b; 0x46; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rsi,32))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x06;        (* ADD (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x13; 0x4e; 0x08;  (* ADC (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x56; 0x30;  (* MOV (% r10) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x13; 0x56; 0x10;  (* ADC (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x5e; 0x38;  (* MOV (% r11) (Memop Quadword (%% (rsi,56))) *)
  0x4c; 0x13; 0x5e; 0x18;  (* ADC (% r11) (Memop Quadword (%% (rsi,24))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r11) *)
  0x48; 0x8b; 0x46; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0xf7; 0x65; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,64))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0xf7; 0x65; 0x48;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,72))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0xf7; 0x65; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,64))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0xf7; 0x65; 0x50;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,80))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0xf7; 0x65; 0x48;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,72))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0xf7; 0x65; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,64))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0xf7; 0x65; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,88))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0xf7; 0x65; 0x50;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,80))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0xf7; 0x65; 0x48;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,72))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0x65; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,64))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0xf7; 0x65; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,88))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0xf7; 0x65; 0x50;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,80))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0x65; 0x48;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,72))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0xf7; 0x65; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,88))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0x65; 0x50;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,80))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0xf7; 0x65; 0x58;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,88))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r11) *)
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
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x65; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,32))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x65; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,40))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x65; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,32))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x65; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,48))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x65; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,40))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x65; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,32))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xf7; 0x65; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,56))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x65; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,48))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x65; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,40))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x65; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,32))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0xf7; 0x65; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,56))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x65; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,48))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x65; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,40))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0xf7; 0x65; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,56))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x65; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,48))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0xf7; 0x65; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rbp,56))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r11) *)
  0x4c; 0x8b; 0x04; 0x24;  (* MOV (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x44; 0x24; 0x60;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x68;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,104))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x54; 0x24; 0x10;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x70;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x1b; 0x44; 0x24; 0x78;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r10) *)
  0x48; 0x89; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rax) *)
  0x4c; 0x8b; 0x04; 0x24;  (* MOV (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x44; 0x24; 0x60;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x68;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x10;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x13; 0x54; 0x24; 0x70;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x18;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x78;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,120))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x4c; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x44; 0x24; 0x20;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x28;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,40))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x30;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x1b; 0x44; 0x24; 0x38;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r10) *)
  0x48; 0x89; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% rax) *)
  0x4c; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x44; 0x24; 0x20;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x28;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x13; 0x54; 0x24; 0x30;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x58;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x38;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,56))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
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
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0xf7; 0x24; 0x24;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0xf7; 0x64; 0x24; 0x08;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0xf7; 0x24; 0x24;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0xf7; 0x64; 0x24; 0x08;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0xf7; 0x24; 0x24;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0xf7; 0x64; 0x24; 0x08;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0xf7; 0x24; 0x24;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0xf7; 0x64; 0x24; 0x08;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0xf7; 0x64; 0x24; 0x10;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0xf7; 0x64; 0x24; 0x18;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,24))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% r9) *)
  0x4c; 0x89; 0x57; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,128))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,136))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,144))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0xa4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r9) *)
  0x4c; 0x89; 0x57; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0x64; 0x24; 0x20;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0x64; 0x24; 0x28;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0x64; 0x24; 0x30;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0xf7; 0x64; 0x24; 0x38;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
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
  0x4c; 0x89; 0x47; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% r9) *)
  0x4c; 0x89; 0x57; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% r11) *)
  0x48; 0x81; 0xc4; 0xc0; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 192)) *)
  0xc3                     (* RET *)
]
[62; 145; 64; 215; 5; 57; 16; 157; 179; 190; 64; 209; 5; 159; 57; 253; 9;
 138; 143; 104; 52; 132; 193; 165; 103; 18; 248; 152; 146; 47; 253; 68; 133;
 59; 140; 245; 198; 147; 188; 47; 25; 14; 140; 251; 198; 45; 147; 207; 194;
 66; 61; 100; 152; 72; 11; 39; 101; 186; 212; 51; 58; 157; 207; 7; 104; 170;
 122; 135; 5; 18; 201; 171; 158; 196; 170; 204; 35; 232; 217; 38; 140; 89;
 67; 221; 203; 125; 27; 90; 168; 101; 12; 159; 104; 123; 17; 111; 168; 213;
 180; 66; 96; 165; 153; 138; 246; 172; 96; 78; 12; 129; 43; 143; 170; 55;
 110; 177; 107; 35; 158; 224; 85; 37; 201; 105; 166; 149; 181; 107; 215; 113;
 60; 147; 252; 231; 36; 146; 181; 245; 15; 122; 150; 157; 70; 159; 2; 7; 214;
 225; 101; 154; 166; 90; 46; 46; 125; 168; 63; 6; 12; 89; 95; 122; 155; 165;
 179; 168; 250; 67; 120; 207; 154; 93; 221; 107; 193; 54; 49; 106; 61; 11;
 132; 160; 15; 80; 115; 11; 165; 62; 177; 245; 26; 112; 101; 210; 252; 164;
 232; 31; 97; 86; 125; 186; 193; 229; 253; 83; 211; 59; 189; 214; 75; 33; 26;
 243; 49; 129; 98; 218; 91; 85; 135; 21; 185; 42; 48; 151; 238; 76; 168; 176;
 37; 175; 138; 75; 134; 232; 48; 132; 90; 2; 50; 103; 1; 159; 2; 80; 27; 193;
 244; 248; 128; 154; 27; 78; 22; 122; 137; 216; 208; 13; 63; 147; 174; 20;
 98; 218; 53; 28; 34; 35; 148; 88; 76; 219; 242; 140; 69; 229; 112; 209; 198;
 180; 185; 18; 175; 38; 40; 90; 191; 24; 104; 5; 10; 5; 254; 149; 169; 250;
 96; 86; 113; 137; 126; 50; 115; 80; 160; 6; 205; 227; 232; 195; 154; 164;
 69; 116; 76; 63; 147; 39; 159; 9; 252; 142; 185; 81; 115; 40; 56; 37; 253;
 125; 244; 198; 101; 103; 101; 146; 10; 251; 61; 141; 52; 202; 39; 135; 229;
 33; 3; 145; 14; 104; 9; 255; 118; 196; 233; 251; 19; 90; 114; 193; 92; 123;
 69; 57; 158; 110; 148; 68; 43; 16; 249; 220; 219; 93; 43; 62; 85; 99; 191;
 12; 157; 127; 186; 214; 71; 164; 195; 130; 145; 127; 183; 41; 39; 75; 209;
 20; 0; 213; 135; 160; 100; 184; 28; 241; 60; 227; 243; 85; 27; 235; 115;
 126; 74; 21; 51; 187; 165; 8; 68; 188; 18; 162; 2; 237; 94; 199; 195; 72;
 80; 141; 68; 236; 191; 90; 12; 235; 27; 221; 235; 6; 226; 70; 241; 204; 69;
 41; 133; 130; 42; 129; 241; 219; 187; 188; 252; 209; 189; 208; 7; 8; 14; 39;
 45; 167; 189; 27; 11; 103; 27; 180; 154; 182; 59; 107; 105; 190; 170; 67;
 164; 140; 125; 123; 182; 6; 152; 73; 57; 39; 210; 39; 132; 226; 91; 87; 185;
 83; 69; 32; 231; 92; 8; 187; 132; 120; 65; 174; 65; 76; 182; 56; 49; 113;
 21; 119; 235; 238; 12; 58; 136; 175; 200; 0; 137; 21; 39; 155; 54; 167; 89;
 218; 104; 182; 101; 128; 189; 56; 204; 162; 182; 123; 229; 81; 113; 75; 234;
 2; 103; 50; 172; 133; 1; 187; 161; 65; 3; 224; 112; 190; 68; 193; 59; 8; 75;
 162; 228; 83; 227; 97; 13; 159; 26; 233; 184; 16; 177; 33; 50; 170; 154; 44;
 111; 186; 167; 35; 186; 59; 83; 33; 160; 108; 58; 44; 25; 146; 79; 118; 234;
 157; 224; 23; 83; 46; 93; 221; 110; 29; 191; 163; 78; 148; 208; 92; 26; 107;
 210; 192; 157; 179; 58; 53; 112; 116; 73; 46; 84; 40; 130; 82; 178; 113;
 126; 146; 60; 40; 105; 234; 27; 70; 162; 179; 184; 1; 200; 109; 131; 241;
 154; 164; 62; 5; 71; 95; 3; 179; 243; 173; 119; 88; 186; 65; 156; 82; 167;
 144; 15; 106; 28; 187; 159; 122; 217; 52; 146; 243; 237; 93; 167; 226; 249;
 88; 181; 225; 128; 118; 61; 150; 251; 35; 60; 110; 172; 65; 39; 44; 195; 1;
 14; 50; 161; 36; 144; 58; 143; 62; 221; 4; 102; 89; 183; 89; 44; 112; 136;
 226; 119; 3; 179; 108; 35; 195; 217; 94; 102; 156; 51; 177; 47; 229; 188;
 97; 96; 231; 21; 9; 26; 145; 162; 201; 217; 245; 193; 231; 215; 167; 204;
 139; 120; 113; 163; 184; 50; 42; 182; 14; 25; 18; 100; 99; 149; 78; 204; 46;
 92; 124; 144; 38];;

let edwards25519_scalarmuldouble_alt_tmc = define_trimmed "edwards25519_scalarmuldouble_alt_tmc" edwards25519_scalarmuldouble_alt_mc;;

let EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC =
  X86_MK_EXEC_RULE edwards25519_scalarmuldouble_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Actually proving that the tables are correct.                             *)
(* ------------------------------------------------------------------------- *)

let edwards25519_projective = define
 `edwards25519_projective P (X,Y,Z) <=>
        projective (integer_mod_ring p_25519) P (&X,&Y,&Z)`;;

let edwards25519_projective2 = define
 `edwards25519_projective2 P (X,Y,Z) <=>
        X < 2 * p_25519 /\ Y < 2 * p_25519 /\ Z < 2 * p_25519 /\
        edwards25519_projective P
         (X MOD p_25519,Y MOD p_25519,Z MOD p_25519)`;;

let EDWARDS25519_PROJECTIVE_IMP_PROJECTIVE2 = prove
 (`!P X Y Z.
        edwards25519_projective P (X,Y,Z)
        ==> edwards25519_projective2 P (X,Y,Z)`,
  REWRITE_TAC[edwards25519_projective; edwards25519_projective2] THEN
  SIMP_TAC[PROJECTIVE_ALT; FORALL_PAIR_THM;
           FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_25519] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SIMP_TAC[INT_REM_LT; INT_POS] THEN INT_ARITH_TAC);;

let EDWARDS25519_PROJECTIVE_BOUND = prove
 (`!x y X Y Z.
        edwards25519_projective (x,y) (X,Y,Z)
        ==> x < &p_25519 /\ y < &p_25519 /\
            X < p_25519 /\ Y < p_25519 /\ Z < p_25519`,
  REWRITE_TAC[edwards25519_projective; projective] THEN
  REWRITE_TAC[p_25519; IN_INTEGER_MOD_RING_CARRIER; INT_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let edwards25519_exprojective = define
 `edwards25519_exprojective P (X,Y,Z,W) <=>
        exprojective (integer_mod_ring p_25519) P (&X,&Y,&Z,&W)`;;

let edwards25519_exprojective2 = define
 `edwards25519_exprojective2 P (X,Y,Z,W) <=>
        X < 2 * p_25519 /\ Y < 2 * p_25519 /\
        Z < 2 * p_25519 /\ W < 2 * p_25519 /\
        edwards25519_exprojective P
         (X MOD p_25519,Y MOD p_25519,Z MOD p_25519, W MOD p_25519)`;;

let edwards25519_epprojective = define
 `edwards25519_epprojective (x,y) (YMX,XPY,KXY) <=>
        x < &p_25519 /\ y < &p_25519 /\
        &YMX = (y - x) rem &p_25519 /\
        &XPY = (x + y) rem &p_25519 /\
        &KXY = (&2 * &d_25519 * x * y) rem &p_25519`;;

let edwards25519_epprojectivew = define
 `edwards25519_epprojectivew (x,y) (YMX,XPY,KXY) <=>
        edwards25519_epprojective (x,y)
          (YMX MOD p_25519,XPY MOD p_25519,KXY MOD p_25519)`;;

let edwards25519_exprojective2w = define
 `edwards25519_exprojective2w P (X,Y,Z,W) <=>
        X <= 2 * p_25519 /\ Y < 2 * p_25519 /\ Z < 2 * p_25519 /\
        edwards25519_exprojective P
         (X MOD p_25519,Y MOD p_25519,Z MOD p_25519, W MOD p_25519)`;;

let EDWARDS25519_EXPROJECTIVE_IMP_EXPROJECTIVE2 = prove
 (`!P X Y Z W.
        edwards25519_exprojective P (X,Y,Z,W)
        ==> edwards25519_exprojective2 P (X,Y,Z,W)`,
  REWRITE_TAC[edwards25519_exprojective; edwards25519_exprojective2] THEN
  SIMP_TAC[EXPROJECTIVE_ALT; FORALL_PAIR_THM;
           FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_25519] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SIMP_TAC[INT_REM_LT; INT_POS] THEN INT_ARITH_TAC);;

let EDWARDS25519_EXPROJECTIVE2_IMP_EXPROJECTIVE2W = prove
 (`!P X Y Z W.
        edwards25519_exprojective2 P (X,Y,Z,W)
        ==> edwards25519_exprojective2w P (X,Y,Z,W)`,
  REWRITE_TAC[edwards25519_exprojective2; edwards25519_exprojective2w] THEN
  SIMP_TAC[LT_IMP_LE]);;

let EDWARDS25519_EPPROJECTIVE_BOUND = prove
 (`!P X Y Z.
        edwards25519_epprojective P (X,Y,Z)
        ==> X < p_25519 /\ Y < p_25519 /\ Z < p_25519`,
  REWRITE_TAC[FORALL_PAIR_THM; edwards25519_epprojective] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC INT_LT_REM THEN REWRITE_TAC[p_25519] THEN INT_ARITH_TAC);;

let EDWARDS25519_EPPROJECTIVE_IMP_EPPROJECTIVEW = prove
 (`!P X Y Z.
        edwards25519_epprojective P (X,Y,Z)
        ==> edwards25519_epprojectivew P (X,Y,Z)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[edwards25519_epprojective; edwards25519_epprojectivew] THEN
  SIMP_TAC[GSYM INT_OF_NUM_REM; INT_REM_REM]);;

let EDWARDS25519_EXPROJECTIVE2W_NEG = prove
 (`!P X Y Z W X' W'.
        edwards25519_exprojective2 P (X,Y,Z,W) /\
        X' < 2 EXP 256 /\ W' < 2 EXP 256 /\
        (X + X' == 2 * p_25519) (mod (2 EXP 256)) /\
        (W + W' == 2 * p_25519) (mod (2 EXP 256))
        ==> edwards25519_exprojective2w
             (group_inv edwards25519_group P) (X',Y,Z,W')`,
  REWRITE_TAC[edwards25519_exprojective2w; FORALL_PAIR_THM;
              edwards25519_exprojective2; edwards25519_exprojective;
              EDWARDS25519_GROUP; edwards_neg; INTEGER_MOD_RING_CLAUSES] THEN
  SIMP_TAC[EXPROJECTIVE_ALT; FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CARRIER_REM; GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    INT_CONG_IMP_EQ))) THEN
  REPEAT(ANTS_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `(&0:int <= y /\ y < p) /\ (&0 <= q - x /\ q - x < p)
      ==> abs((x + y) - q) < p`) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[p_25519] THEN INT_ARITH_TAC;
    DISCH_TAC]) THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (INT_ARITH
   `x + y:int = p ==> y = p - x`))) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INT_REM_EQ])) THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  CONV_TAC INTEGER_RULE);;

let EDWARDS25519_EPPROJECTIVEW_NEG = prove
 (`!P X Y Z Z'.
        edwards25519_epprojectivew P (X,Y,Z) /\ p_25519 divides (Z + Z')
        ==> edwards25519_epprojectivew (group_inv edwards25519_group P)
                                       (Y,X,Z')`,
  REWRITE_TAC[edwards25519_epprojectivew; FORALL_PAIR_THM;
              edwards25519_epprojective; EDWARDS25519_GROUP;
              edwards_neg; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INTEGER_RULE `p divides (a + b:int) <=> (b == --a) (mod p)`] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; GSYM INT_OF_NUM_REM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC INT_LT_REM THEN
      REWRITE_TAC[p_25519] THEN INT_ARITH_TAC) THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  REWRITE_TAC[INTEGER_RULE
   `(--x:int == y) (mod p) <=> (x == --y) (mod p)`] THEN
  ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let EDWARDS25519_EXPROJECTIVE_BOUND = prove
 (`!x y X Y Z W.
        edwards25519_exprojective (x,y) (X,Y,Z,W)
        ==> x < &p_25519 /\ y < &p_25519 /\
            X < p_25519 /\ Y < p_25519 /\ Z < p_25519 /\ W < p_25519`,
  REWRITE_TAC[edwards25519_exprojective; exprojective] THEN
  REWRITE_TAC[p_25519; IN_INTEGER_MOD_RING_CARRIER; INT_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 = prove
 (`!P X Y Z W.
        edwards25519_exprojective2 P (X,Y,Z,W)
        ==> edwards25519_projective2 P (X,Y,Z)`,
  SIMP_TAC[edwards25519_exprojective2; edwards25519_projective2] THEN
  SIMP_TAC[FORALL_PAIR_THM; EXPROJECTIVE_PROJECTIVE; edwards25519_exprojective;
           edwards25519_projective; FIELD_INTEGER_MOD_RING; PRIME_P25519]);;

let GE25519_POW_1 = prove
 (`group_pow edwards25519_group E_25519 1 =
    (&15112221349535400772501151409588531511454012693041857206046113283949847762202,
     &46316835694926478169428394003475163141307993866256225615783033603165251855960)`,
  REWRITE_TAC[E_25519] THEN
  MATCH_MP_TAC GROUP_POW_1 THEN
  REWRITE_TAC[GSYM E_25519; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]);;

let GE25519_GROUPER =
  let pth = prove
   (`group_pow edwards25519_group E_25519 m = x /\
     group_pow edwards25519_group E_25519 n = y
     ==> group_pow edwards25519_group E_25519 (m + n) =
         group_mul edwards25519_group x y`,
    MESON_TAC[GROUP_POW_ADD; GROUP_POW; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]) in
  fun th1 th2 ->
    CONV_RULE
     (BINOP2_CONV (RAND_CONV NUM_ADD_CONV) ECGROUP_MUL_CONV)
     (MATCH_MP pth (CONJ th1 th2));;

let BYTES_LOADED_DATA = prove
 (`bytes_loaded s (word (pc + 0x6fc9)) edwards25519_scalarmuldouble_alt_data <=>
   read (memory :> bytes(word (pc + 0x6fc9),768)) s =
   num_of_bytelist edwards25519_scalarmuldouble_alt_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num` edwards25519_scalarmuldouble_alt_data)]);;

let EDWARDS25519DOUBLEBASE_TABLE_LEMMA = prove
 (`read (memory :> bytes(word (pc + 0x6fc9),768)) s =
   num_of_bytelist edwards25519_scalarmuldouble_alt_data
   ==> !i. i < 8
           ==> edwards25519_epprojective
                (group_pow edwards25519_group E_25519 (i + 1))
         (bignum_from_memory(word(pc + 0x6fc9 + 96 * i),4) s,
          bignum_from_memory(word(pc + 0x6fc9 + 96 * i + 32),4) s,
          bignum_from_memory(word(pc + 0x6fc9 + 96 * i + 64),4) s) /\
         ~(bignum_from_memory(word(pc + 0x6fc9 + 96 * i + 64),4) s =
           0)`,
  let GE25519_POWERS =
    end_itlist CONJ
    (funpow 7 (fun l -> GE25519_GROUPER GE25519_POW_1 (hd l)::l)
                          [GE25519_POW_1]) in
  REWRITE_TAC[GSYM BYTES_LOADED_DATA;
              edwards25519_scalarmuldouble_alt_data] THEN
  CONV_TAC(LAND_CONV DATA64_CONV) THEN STRIP_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bignum_of_wordlist] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[GE25519_POWERS] THEN
  REWRITE_TAC[p_25519; edwards25519_exprojective; edwards25519_epprojective;
              exprojective; d_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Common lemmas and tactics for the component proofs.                       *)
(* ------------------------------------------------------------------------- *)

let DESUM_RULE' = cache DESUM_RULE and DECARRY_RULE' = cache DECARRY_RULE;;

let p25519redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_25519 - 1)
       ==> let q = n DIV 2 EXP 255 + 1 in
           q < 2 EXP 64 /\
           q * p_25519 <= n + p_25519 /\
           n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let lvs =
 [
  (*** These are for the toplevel function, and not used often ***)

  "resx",[`RBP`;`0`];
  "resy",[`RBP`;`32`];
  "scalar",[`RSP`;`0`];
  "bscalar",[`RSP`;`32`];
  "tabent",[`RSP`;`64`];
  "btabent",[`RSP`;`192`];
  "acc",[`RSP`;`288`];
  "acc_x",[`RSP`;`288`];
  "acc_y",[`RSP`;`296`];
  "acc_z",[`RSP`;`328`];
  "acc_w",[`RSP`;`360`];
  "tab",[`RSP`;`416`];

  (*** These are local for the subroutines ***)

  "x_0",[`RDI`;`0`];
  "y_0",[`RDI`;`32`];
  "z_0",[`RDI`;`64`];
  "w_0",[`RDI`;`96`];
  "x_1",[`RSI`;`0`];
  "y_1",[`RSI`;`32`];
  "z_1",[`RSI`;`64`];
  "w_1",[`RSI`;`96`];
  "x_2",[`RBP`;`0`];
  "y_2",[`RBP`;`32`];
  "z_2",[`RBP`;`64`];
  "w_2",[`RBP`;`96`];
  "t0",[`RSP`;`0`];
  "t1",[`RSP`;`32`];
  "t2",[`RSP`;`64`];
  "t3",[`RSP`;`96`];
  "t4",[`RSP`;`128`];
  "t5",[`RSP`;`160`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_p25519.                                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P25519_TAC =
  X86_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_tmc 129 lvs
   `!(t:x86state) pcin pcout q3 n3 q1 n1 q2 n2.
      !m. read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x72c9) (word_add (read q3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_tmc /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDI s = read RDI t /\
                read RSI s = read RSI t /\
                read RBP s = read RBP t /\
                read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s =
                (m * n) MOD p_25519)
         (MAYCHANGE [RIP; RSI; RAX; RBX; RCX; RDX;
                     R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(word_add (read q3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s1" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiplication block, similar to bignum_mul_4_8_alt ***)

  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
   [3;9;10;11;13;14;15;19;20;21;24;25;26;27;29;30;31;
    32;35;36;37;40;41;42;43;45;46;47;48;50;51;52;53;56;57;58;
    61;62;63;64;66;67;68;69;72;73;74;77;78;79;80;82;83;84]
   (2--84) THEN
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
    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
     (if mem n [87;88;89;92;93;94;95;98;99;100;101;104;105;107;109]
      then ACCUMULATE_ARITH_TAC("s"^string_of_int n)
      else ALL_TAC))
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

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (110--114) THEN
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

  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
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
(* Instances of mul_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_4_TAC =
  X86_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_tmc 120 lvs
   `!(t:x86state) pcin pcout q3 n3 q1 n1 q2 n2.
      !m. read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x72c9) (word_add (read q3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_tmc /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDI s = read RDI t /\
                read RSI s = read RSI t /\
                read RBP s = read RBP t /\
                read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s
                < 2 * p_25519 /\
                (read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s ==
                 m * n) (mod p_25519))
           (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                       R8; R9; R10; R11; R12; R13; R14; R15] ,,
            MAYCHANGE [memory :> bytes(word_add (read q3 t) (word n3),8 * 4)] ,,
            MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s1" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiplication block, similar to bignum_mul_4_8_alt ***)

  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
   [3;9;10;11;13;14;15;19;20;21;24;25;26;27;29;30;31;
    32;35;36;37;40;41;42;43;45;46;47;48;50;51;52;53;56;57;58;
    61;62;63;64;66;67;68;69;72;73;74;77;78;79;80;82;83;84]
   (2--84) THEN
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
    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
     (if mem n [87;88;89;92;93;94;95;98;99;100;101;104;105;107;109]
      then ACCUMULATE_ARITH_TAC("s"^string_of_int n)
      else ALL_TAC))
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

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (110--113) THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s109 sum_s107) (63,64)` THEN
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

  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
   (114--117) (114--121) THEN
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
(* Instances of sqr_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_4_TAC =
  X86_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_tmc 109 lvs
   `!(t:x86state) pcin pcout p3 n3 p1 n1.
      !n.
      read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x72c9) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_tmc /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDI s = read RDI t /\
                read RSI s = read RSI t /\
                read RBP s = read RBP t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                < 2 * p_25519 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                 n EXP 2)
                (mod p_25519))
        (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                    R8; R9; R10; R11; R12; R13; R14; R15] ,,
         MAYCHANGE
          [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8_alt ***)

  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--72) (1--72) THEN
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
    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC [n] THEN
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

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (98--101) THEN
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

  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (102--105) (102--109) THEN
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
(* Instances of add_twice4 (slightly sharper disjunctive hypothesis).        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_TWICE4_TAC =
  X86_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_tmc 19 lvs
   `!(t:x86state) pcin pcout q3 n3 q1 n1 q2 n2.
      !m. read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x72c9) (word_add (read q3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_tmc /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDI s = read RDI t /\
                read RSI s = read RSI t /\
                read RBP s = read RBP t /\
                read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                (m < 2 * p_25519 \/ n < 2 * p_25519
                 ==> (read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s ==
                      m + n) (mod p_25519)))
        (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
         MAYCHANGE [memory :> bytes(word_add (read q3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC [3;5;7;9] (1--11) THEN
  SUBGOAL_THEN `carry_s9 <=> 2 EXP 256 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (12--15) (12--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x = x'
             ==> (x:int == a) (mod p)`) THEN
  EXISTS_TAC
   `if 2 EXP 256 <= m + n then (&m + &n) - &2 * &p_25519:int else &m + &n` THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `2 EXP 256` o MATCH_MP (ARITH_RULE
     `m < p \/ n < p
      ==> !e:num. p < e /\ m < e /\ n < e ==> m + n < e + p`)) THEN
    ANTS_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NOT_LE; SYM(NUM_EXP_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `bb <=> 2 EXP 256 <= m + n` THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of double_twice4.                                               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_DOUBLE_TWICE4_TAC =
  X86_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_tmc 19 lvs
   `!(t:x86state) pcin pcout q3 n3 q1 n1.
      !n. read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x72c9) (word_add (read q3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_tmc /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDI s = read RDI t /\
                read RSI s = read RSI t /\
                read RBP s = read RBP t /\
                read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                (n < 2 * p_25519
                 ==> (read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s ==
                      2 * n) (mod p_25519)))
        (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
         MAYCHANGE [memory :> bytes(word_add (read q3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC [3;5;7;9] (1--11) THEN
  SUBGOAL_THEN `carry_s9 <=> 2 EXP 256 <= 2 * n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (12--15) (12--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x = x'
             ==> (x:int == a) (mod p)`) THEN
  EXISTS_TAC
   `if 2 EXP 256 <= 2 * n then (&2 * &n) - &2 * &p_25519:int else &2 * &n` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    COND_CASES_TAC THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NOT_LE; SYM(NUM_EXP_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `bb <=> 2 EXP 256 <= 2 * n` THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub_twice4 (slightly sharper hypothesis distinctions).       *)
(* This version also has <= not < for n, to allow imprecise negations of 0.  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_TWICE4_TAC =
  X86_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_tmc 19 lvs
   `!(t:x86state) pcin pcout q3 n3 q1 n1 q2 n2.
      !m. read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x72c9) (word_add (read q3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_tmc /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDI s = read RDI t /\
                read RSI s = read RSI t /\
                read RBP s = read RBP t /\
                read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                (m < 2 * p_25519 /\ n <= 2 * p_25519
                 ==> read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s
                     < 2 * p_25519) /\
                (n <= 2 * p_25519
                 ==> (&(bignum_from_memory
                         (word_add (read q3 t) (word n3),4) s):int ==
                      &m - &n) (mod (&p_25519))))
        (MAYCHANGE [RIP; RAX; RBX; RCX; R8; R9; R10] ,,
         MAYCHANGE [memory :> bytes(word_add (read q3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--10) (1--10) THEN
  SUBGOAL_THEN `carry_s10 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (12--15) (11--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT; INT_OF_NUM_LE]
   `!x':int. (x' == &m - &n) (mod p) /\
             (m < p2 /\ n <= p2 ==> x' < &p2) /\
             (n <= p2 ==> &x = x')
             ==> (m < p2 /\ n <= p2 ==> x < p2) /\
                 (n:num <= p2 ==> (&x:int == &m - &n) (mod p))`) THEN
  EXISTS_TAC `if m < n then &m - &n + &2 * &p_25519:int else &m - &n` THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC INTEGER_RULE;
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
      SUBGOAL_THEN `m < 2 EXP 256` MP_TAC THENL
       [EXPAND_TAC "m" THEN BOUNDER_TAC[];
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN REAL_ARITH_TAC]];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NOT_LT]) THEN
  ABBREV_TAC `bb <=> m:num < n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of modular inverse inlining                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MODINV_TAC =
 X86_SUBROUTINE_SIM_TAC
  (edwards25519_scalarmuldouble_alt_tmc,
   EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC,
   0x1962,
   (GEN_REWRITE_CONV RAND_CONV [bignum_inv_p25519_tmc] THENC TRIM_LIST_CONV)
   `TRIM_LIST (17,18) bignum_inv_p25519_tmc`,
   CORE_INV_P25519_CORRECT)
  [`read RDI s`; `read RSI s`;
   `read (memory :> bytes(read RSI s,8 * 4)) s`;
   `pc + 0x1962`; `word_add stackpointer (word 200):int64`];;

(* ------------------------------------------------------------------------- *)
(* Embedded subroutine correctness.                                          *)
(* ------------------------------------------------------------------------- *)

let LOCAL_EPDOUBLE_CORRECT = time prove
 (`!p3 p1 T1 pc stackpointer.
    ALL (nonoverlapping (stackpointer,160))
        [(word pc,0x72c9); (p3,128); (p1,96)] /\
    nonoverlapping (p3,128) (word pc,0x72c9)
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                 edwards25519_scalarmuldouble_alt_tmc /\
              read RIP s = word(pc + 0x30b4) /\
              read RSP s = stackpointer /\
              read RDI s = p3 /\
              read RSI s = p1 /\
              bignum_triple_from_memory(p1,4) s = T1)
         (\s. read RIP s = word (pc + 0x3fe1) /\
              !P1. P1 IN group_carrier edwards25519_group /\
                   edwards25519_projective2 P1 T1
                      ==> edwards25519_exprojective2
                           (edwards_add edwards25519 P1 P1)
                           (bignum_quadruple_from_memory(p3,4) s))
          (MAYCHANGE [RIP;  RAX; RBX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,128);
                      memory :> bytes(stackpointer,160)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `X_1:num`; `Y_1:num`; `Z_1:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ;
              bignum_quadruple_from_memory; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t0"; "x_1"; "y_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t1"; "z_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t2"; "x_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t3"; "y_1"] THEN
  LOCAL_DOUBLE_TWICE4_TAC 0 ["t1"; "t1"] THEN
  LOCAL_SQR_4_TAC 0 ["t0"; "t0"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t4"; "t2"; "t3"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t2"; "t2"; "t3"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t3"; "t1"; "t2"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t1"; "t4"; "t0"] THEN
  LOCAL_MUL_4_TAC 0 ["y_0"; "t2"; "t4"] THEN
  LOCAL_MUL_4_TAC 0 ["z_0"; "t3"; "t2"] THEN
  LOCAL_MUL_4_TAC 0 ["w_0"; "t1"; "t4"] THEN
  LOCAL_MUL_4_TAC 0 ["x_0"; "t1"; "t3"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[edwards25519_projective2; edwards25519_exprojective2] THEN
  MAP_EVERY X_GEN_TAC [`x1:int`; `y1:int`] THEN STRIP_TAC THEN
  DISCARD_STATE_TAC "s14" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  ASM_SIMP_TAC[LT_IMP_LE] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_imp o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `&e_25519:int`; `&d_25519:int`;
    `x1:int`; `y1:int`;
    `&X_1 rem &p_25519`; `&Y_1 rem &p_25519`; `&Z_1 rem &p_25519`]
   EDWARDS_PREXPROJDOUBLEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM edwards25519_projective; INT_OF_NUM_REM] THEN
    REWRITE_TAC[EDWARDS_NONSINGULAR_25519] THEN
    SIMP_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN])) THEN
    SIMP_TAC[EDWARDS25519_GROUP] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519; e_25519; d_25519] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM edwards25519; edwards25519_exprojective] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[edwards_prexprojdoublen; edwards_prexprojdouble;
              edwards25519] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  SUBGOAL_THEN `&e_25519 = (-- &1) rem &p_25519` SUBST_ALL_TAC THENL
   [REWRITE_TAC[e_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[PAIR_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_EPDOUBLE_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_quadruple_from_memory]
         LOCAL_EPDOUBLE_CORRECT) in
  X86_SUBROUTINE_SIM_TAC
   (edwards25519_scalarmuldouble_alt_tmc,EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC,
    0x0,edwards25519_scalarmuldouble_alt_tmc,th)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 64),8 * 4)) s`;
   `pc:num`; `read RSP s`];;

let LOCAL_PDOUBLE_CORRECT = time prove
 (`!p3 p1 T1 pc stackpointer.
    ALL (nonoverlapping (stackpointer,160))
        [(word pc,0x72c9); (p3,96); (p1,96)] /\
    nonoverlapping (p3,96) (word pc,0x72c9)
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                 edwards25519_scalarmuldouble_alt_tmc /\
              read RIP s = word(pc + 0x3ff0) /\
              read RSP s = stackpointer /\
              read RDI s = p3 /\
              read RSI s = p1 /\
              bignum_triple_from_memory(p1,4) s = T1)
         (\s. read RIP s = word (pc + 0x4d2f) /\
              !P1. P1 IN group_carrier edwards25519_group /\
                   edwards25519_projective2 P1 T1
                      ==> edwards25519_projective2
                           (edwards_add edwards25519 P1 P1)
                           (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [RIP;  RAX; RBX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,160)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `X_1:num`; `Y_1:num`; `Z_1:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ;
              bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t0"; "x_1"; "y_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t1"; "z_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t2"; "x_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t3"; "y_1"] THEN
  LOCAL_DOUBLE_TWICE4_TAC 0 ["t1"; "t1"] THEN
  LOCAL_SQR_4_TAC 0 ["t0"; "t0"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t4"; "t2"; "t3"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t2"; "t2"; "t3"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t3"; "t1"; "t2"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t1"; "t4"; "t0"] THEN
  LOCAL_MUL_4_TAC 0 ["y_0"; "t2"; "t4"] THEN
  LOCAL_MUL_4_TAC 0 ["z_0"; "t3"; "t2"] THEN
  LOCAL_MUL_4_TAC 0 ["x_0"; "t1"; "t3"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[edwards25519_projective2] THEN
  MAP_EVERY X_GEN_TAC [`x1:int`; `y1:int`] THEN STRIP_TAC THEN
  DISCARD_STATE_TAC "s13" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  ASM_SIMP_TAC[LT_IMP_LE] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_imp o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `&e_25519:int`; `&d_25519:int`;
    `x1:int`; `y1:int`;
    `&X_1 rem &p_25519`; `&Y_1 rem &p_25519`; `&Z_1 rem &p_25519`]
   EDWARDS_PREXPROJDOUBLEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM edwards25519_projective; INT_OF_NUM_REM] THEN
    REWRITE_TAC[EDWARDS_NONSINGULAR_25519] THEN
    SIMP_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN])) THEN
    SIMP_TAC[EDWARDS25519_GROUP] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519; e_25519; d_25519] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV;
    SIMP_TAC[REWRITE_RULE[GSYM FORALL_PAIR_THM] EXPROJECTIVE_PROJECTIVE;
             FIELD_INTEGER_MOD_RING; PRIME_P25519;
             edwards_prexprojdoublen; LET_DEF; LET_END_DEF;
             edwards_prexprojdouble] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[edwards25519; edwards25519_projective] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[edwards_prexprojdoublen; edwards_prexprojdouble;
              edwards25519] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  SUBGOAL_THEN `&e_25519 = (-- &1) rem &p_25519` SUBST_ALL_TAC THENL
   [REWRITE_TAC[e_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[PAIR_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_PDOUBLE_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory]
         LOCAL_PDOUBLE_CORRECT) in
  X86_SUBROUTINE_SIM_TAC
   (edwards25519_scalarmuldouble_alt_tmc,EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC,
    0x0,edwards25519_scalarmuldouble_alt_tmc,th)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 64),8 * 4)) s`;
   `pc:num`; `read RSP s`];;

let LOCAL_EPADD_CORRECT = time prove
 (`!p3 p1 Q1 p2 Q2 pc stackpointer.
    ALL (nonoverlapping (stackpointer,192))
        [(word pc,0x72c9); (p3,128); (p1,128); (p2,128)] /\
    nonoverlapping (p3,128) (word pc,0x72c9)
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                 edwards25519_scalarmuldouble_alt_tmc /\
              read RIP s = word(pc + 0x4d3e) /\
              read RSP s = stackpointer /\
              read RDI s = p3 /\
              read RSI s = p1 /\
              read RBP s = p2 /\
              bignum_quadruple_from_memory(p1,4) s = Q1 /\
              bignum_quadruple_from_memory(p2,4) s = Q2)
         (\s. read RIP s = word (pc + 0x60c2) /\
              !P1 P2. P1 IN group_carrier edwards25519_group /\
                      P2 IN group_carrier edwards25519_group /\
                      edwards25519_exprojective2 P1 Q1 /\
                      edwards25519_exprojective2 P2 Q2
                      ==> edwards25519_exprojective2
                           (edwards_add edwards25519 P1 P2)
                           (bignum_quadruple_from_memory(p3,4) s))
          (MAYCHANGE [RIP;  RAX; RBX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,128);
                      memory :> bytes(stackpointer,192)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `X_1:num`; `Y_1:num`; `Z_1:num`; `W_1:num`;
    `p2:int64`; `X_2:num`; `Y_2:num`; `Z_2:num`; `W_2:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; bignum_quadruple_from_memory;
              bignum_pair_from_memory; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  LOCAL_MUL_4_TAC 0 ["t0"; "w_1"; "w_2"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t1"; "y_1"; "x_1"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t2"; "y_2"; "x_2"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t3"; "y_1"; "x_1"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t4"; "y_2"; "x_2"] THEN
  LOCAL_DOUBLE_TWICE4_TAC 0 ["t5"; "z_2"] THEN
  LOCAL_MUL_4_TAC 0 ["t1"; "t1"; "t2"] THEN
  LOCAL_MUL_4_TAC 0 ["t3"; "t3"; "t4"] THEN
  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (9--16) THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add stackpointer (word 64),8 * 4)) s16 =
    16295367250680780974490674513165176452449235426866156013048779062215315747161`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  LOCAL_MUL_4_TAC 0 ["t2"; "t2"; "t0"] THEN
  LOCAL_MUL_4_TAC 0 ["t4"; "z_1"; "t5"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t0"; "t3"; "t1"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t5"; "t3"; "t1"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t1"; "t4"; "t2"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t3"; "t4"; "t2"] THEN
  LOCAL_MUL_4_TAC 0 ["w_0"; "t0"; "t5"] THEN
  LOCAL_MUL_4_TAC 0 ["x_0"; "t0"; "t1"] THEN
  LOCAL_MUL_4_TAC 0 ["y_0"; "t3"; "t5"] THEN
  LOCAL_MUL_4_TAC 0 ["z_0"; "t1"; "t3"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[edwards25519_exprojective2] THEN
  MAP_EVERY X_GEN_TAC [`x1:int`; `y1:int`; `x2:int`; `y2:int`] THEN
  STRIP_TAC THEN  DISCARD_STATE_TAC "s26" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `&e_25519:int`; `&d_25519:int`;
    `x1:int`; `y1:int`;
    `&X_1 rem &p_25519`; `&Y_1 rem &p_25519`; `&Z_1 rem &p_25519`; `&W_1 rem &p_25519`;
    `x2:int`; `y2:int`;
    `&X_2 rem &p_25519`; `&Y_2 rem &p_25519`; `&Z_2 rem &p_25519`; `&W_2 rem &p_25519`]
   EDWARDS_EXPROJADD4) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EDWARDS_NONSINGULAR_25519; INT_OF_NUM_REM] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN])) THEN
    SIMP_TAC[EDWARDS25519_GROUP] THEN
    REWRITE_TAC[edwards_curve] THEN STRIP_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [edwards25519_exprojective])) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[exprojective] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CHAR; IN_INTEGER_MOD_RING_CARRIER;
                INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519; e_25519; d_25519] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[GSYM p_25519] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC(MESON[RING_DIV_1]
     `x IN ring_carrier f /\ y = ring_1 f ==> ring_div f x y = x`) THEN
    ASM_REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; p_25519] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM edwards25519; edwards25519_exprojective] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [edwards25519_exprojective]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[edwards_exprojadd4; edwards_exprojadd; edwards25519;
              INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `&e_25519 = (-- &1) rem &p_25519` SUBST_ALL_TAC THENL
   [REWRITE_TAC[e_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[GSYM p_25519; GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES; GSYM
   (CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[p_25519]
     (AP_TERM `\x. (2 * x) MOD p_25519` d_25519)))] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[PAIR_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_EPADD_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_quadruple_from_memory]
         LOCAL_EPADD_CORRECT) in
  X86_SUBROUTINE_SIM_TAC
   (edwards25519_scalarmuldouble_alt_tmc,EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC,
    0x0,edwards25519_scalarmuldouble_alt_tmc,th)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 64),8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 96),8 * 4)) s`;
   `read RBP s`;
   `read(memory :> bytes(read RBP s,8 * 4)) s,
    read(memory :> bytes(word_add (read RBP s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read RBP s) (word 64),8 * 4)) s,
    read(memory :> bytes(word_add (read RBP s) (word 96),8 * 4)) s`;
   `pc:num`; `read RSP s`];;

let LOCAL_PEPADD_CORRECT = time prove
 (`!p3 p1 Q1 p2 T2 pc stackpointer.
    ALL (nonoverlapping (stackpointer,192))
        [(word pc,0x72c9); (p3,128); (p1,128); (p2,96)] /\
    nonoverlapping (p3,128) (word pc,0x72c9)
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                 edwards25519_scalarmuldouble_alt_tmc /\
              read RIP s = word(pc + 0x60d1) /\
              read RSP s = stackpointer /\
              read RDI s = p3 /\
              read RSI s = p1 /\
              read RBP s = p2 /\
              bignum_quadruple_from_memory(p1,4) s = Q1 /\
              bignum_triple_from_memory(p2,4) s = T2)
         (\s. read RIP s = word (pc + 0x6fc1) /\
              !P1 P2. P1 IN group_carrier edwards25519_group /\
                      P2 IN group_carrier edwards25519_group /\
                      edwards25519_exprojective2w P1 Q1 /\
                      edwards25519_epprojectivew P2 T2
                      ==> edwards25519_exprojective2
                           (edwards_add edwards25519 P1 P2)
                           (bignum_quadruple_from_memory(p3,4) s))
          (MAYCHANGE [RIP;  RAX; RBX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,128);
                      memory :> bytes(stackpointer,192)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `X_1:num`; `Y_1:num`; `Z_1:num`; `W_1:num`;
    `p2:int64`; `YMX_2:num`; `XPY_2:num`; `KXY_2:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS;
              bignum_quadruple_from_memory; bignum_triple_from_memory;
              bignum_pair_from_memory; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  LOCAL_DOUBLE_TWICE4_TAC 0 ["t0"; "z_1"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t1"; "y_1"; "x_1"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t2"; "y_1"; "x_1"] THEN
  LOCAL_MUL_4_TAC 0 ["t3"; "w_1"; "z_2"] THEN
  LOCAL_MUL_4_TAC 0 ["t1"; "t1"; "x_2"] THEN
  LOCAL_MUL_4_TAC 0 ["t2"; "t2"; "y_2"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t4"; "t0"; "t3"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t0"; "t0"; "t3"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t5"; "t2"; "t1"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t1"; "t2"; "t1"] THEN
  LOCAL_MUL_4_TAC 0 ["z_0"; "t4"; "t0"] THEN
  LOCAL_MUL_4_TAC 0 ["x_0"; "t5"; "t4"] THEN
  LOCAL_MUL_4_TAC 0 ["y_0"; "t0"; "t1"] THEN
  LOCAL_MUL_4_TAC 0 ["w_0"; "t5"; "t1"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[edwards25519_exprojective2; edwards25519_exprojective2w;
              edwards25519_epprojectivew] THEN
  MAP_EVERY X_GEN_TAC [`x1:int`; `y1:int`; `x2:int`; `y2:int`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP EDWARDS25519_EXPROJECTIVE_BOUND) THEN
  DISCARD_STATE_TAC "s14" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(
   (ANTS_TAC THENL[ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC]) ORELSE
   DISCH_THEN(K ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `&e_25519:int`; `&d_25519:int`;
    `x1:int`; `y1:int`;
    `&X_1 rem &p_25519`; `&Y_1 rem &p_25519`;
    `&Z_1 rem &p_25519`; `&W_1 rem &p_25519`;
    `x2:int`; `y2:int`;
    `x2:int`; `y2:int`; `&1:int`; `(x2 * y2) rem &p_25519`]
   EDWARDS_EXPROJADD4) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EDWARDS_NONSINGULAR_25519; INT_OF_NUM_REM] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN])) THEN
    SIMP_TAC[EDWARDS25519_GROUP] THEN
    REWRITE_TAC[edwards_curve] THEN STRIP_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [edwards25519_exprojective]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[exprojective] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CHAR; IN_INTEGER_MOD_RING_CARRIER;
                INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519; e_25519; d_25519] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[GSYM p_25519] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC(MESON[RING_DIV_1]
     `x IN ring_carrier f /\ y = ring_1 f ==> ring_div f x y = x`) THEN
    ASM_REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; p_25519] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM edwards25519; edwards25519_exprojective] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [edwards25519_epprojective]) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[edwards_exprojadd4; edwards_exprojadd; edwards25519;
              INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `&e_25519 = (-- &1) rem &p_25519` SUBST_ALL_TAC THENL
   [REWRITE_TAC[e_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[PAIR_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_PEPADD_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_quadruple_from_memory]
         LOCAL_PEPADD_CORRECT) in
  X86_SUBROUTINE_SIM_TAC
   (edwards25519_scalarmuldouble_alt_tmc,EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC,
    0x0,edwards25519_scalarmuldouble_alt_tmc,th)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 64),8 * 4)) s,
    read(memory :> bytes(word_add (read RSI s) (word 96),8 * 4)) s`;
   `read RBP s`;
   `read(memory :> bytes(read RBP s,8 * 4)) s,
    read(memory :> bytes(word_add (read RBP s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read RBP s) (word 64),8 * 4)) s`;
   `pc:num`; `read RSP s`];;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let EDWARDS25519_SCALARMULDOUBLE_ALT_CORRECT = time prove
 (`!res scalar point bscalar n xy m pc stackpointer.
    ALL (nonoverlapping (stackpointer,1672))
        [(word pc,0x72c9); (res,64); (scalar,32); (point,64); (bscalar,32)] /\
    nonoverlapping (res,64) (word pc,0x72c9)
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
               (APPEND edwards25519_scalarmuldouble_alt_tmc
                       edwards25519_scalarmuldouble_alt_data) /\
              read RIP s = word(pc + 0x11) /\
              read RSP s = word_add stackpointer (word 200) /\
              C_ARGUMENTS [res; scalar; point; bscalar] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_pair_from_memory (point,4) s = xy /\
              bignum_from_memory (bscalar,4) s = m)
         (\s. read RIP s = word (pc + 0x309b) /\
              !P. P IN group_carrier edwards25519_group /\
                  paired (modular_decode (256,p_25519)) xy = P
                  ==> bignum_pair_from_memory(res,4) s =
                      paired (modular_encode (256,p_25519))
                             (group_mul edwards25519_group
                                 (group_pow edwards25519_group P n)
                                 (group_pow edwards25519_group E_25519 m)))
         (MAYCHANGE [RIP; RDI; RSI; RAX; RBX; RCX; RDX; RBP;
                     R8; R9; R10; R11; R12; R13; R14; R15] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(res,64);
                     memory :> bytes(stackpointer,1672)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`res:int64`; `scalar:int64`; `point:int64`; `bscalar:int64`;
    `n_input:num`; `x:num`; `y:num`; `m_input:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[bignum_pair_from_memory; PAIR_EQ] THEN
  REWRITE_TAC[WORD_RULE `word(8 * 4) = word 32`; GSYM FORALL_PAIR_THM] THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN
  REWRITE_TAC[BYTES_LOADED_APPEND_CLAUSE] THEN
  REWRITE_TAC[fst EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC] THEN
  REWRITE_TAC[BYTES_LOADED_DATA] THEN

  (*** The recoded forms of the inputs, mathematically ***)

  BIGNUM_TERMRANGE_TAC `4` `n_input:num` THEN
  BIGNUM_TERMRANGE_TAC `4` `m_input:num` THEN
  ABBREV_TAC
   `recoder =
    0x0888888888888888888888888888888888888888888888888888888888888888` THEN
  ABBREV_TAC
   `n = if n_input DIV 2 EXP 192 > 2 EXP 63
        then (n_input + recoder) - 8 * n_25519
        else n_input + recoder` THEN
  SUBGOAL_THEN `n < 9 * 2 EXP 252` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["n"; "recoder"] THEN REWRITE_TAC[n_25519] THEN
    UNDISCH_TAC `n_input < 2 EXP (64 * 4)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `m = if m_input DIV 2 EXP 192 > 2 EXP 63
        then (m_input + recoder) - 8 * n_25519
        else m_input + recoder` THEN
  SUBGOAL_THEN `m < 9 * 2 EXP 252` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "recoder"] THEN REWRITE_TAC[n_25519] THEN
    UNDISCH_TAC `m_input < 2 EXP (64 * 4)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. P IN group_carrier edwards25519_group
        ==> group_pow edwards25519_group P n_input =
            group_zpow edwards25519_group P (&n - &recoder) /\
            group_pow edwards25519_group P m_input =
            group_zpow edwards25519_group P (&m - &recoder)`
   (fun th -> SIMP_TAC[th; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519])
  THENL
   [SIMP_TAC[GROUP_ZPOW_EQ; GSYM GROUP_NPOW] THEN
    REPEAT STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["n"; "m"; "recoder"] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    TRY(W(MP_TAC o PART_MATCH (rand o rand) INT_OF_NUM_SUB o
          lhand o lhand o snd) THEN
        ANTS_TAC THENL
        [REWRITE_TAC[n_25519] THEN ASM_ARITH_TAC;
         DISCH_THEN(SUBST1_TAC o SYM)]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_ARITH `(x + y) - y:int = x`; INT_CONG_REFL]THEN
    REWRITE_TAC[INTEGER_RULE
     `(n:int == (n + x) - m - x) (mod p) <=> p divides m`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_divides] THEN
    REWRITE_TAC[GSYM(REWRITE_RULE[HAS_SIZE] SIZE_EDWARDS25519_GROUP)] THEN
    MATCH_MP_TAC GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER THEN
    ASM_REWRITE_TAC[FINITE_GROUP_CARRIER_EDWARDS25519];
    ALL_TAC] THEN

  (*** Setup of the main loop ***)

  ENSURES_WHILE_DOWN_TAC `63` `pc + 0xe18` `pc + 0x1941`
   `\i s.
      read (memory :> bytes(word(pc + 0x6fc9),768)) s =
      num_of_bytelist edwards25519_scalarmuldouble_alt_data /\
      read RSP s = word_add stackpointer (word 200) /\
      read (memory :> bytes64(word_add stackpointer (word 1664))) s = res /\
      read (memory :> bytes64(word_add stackpointer (word 1656))) s =
      word (4 * i) /\
      bignum_from_memory(word_add stackpointer (word 200),4) s = n /\
      bignum_from_memory(word_add stackpointer (word 232),4) s = m /\
      !P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> (!j. j < 8
                   ==> edwards25519_exprojective2
                        (group_pow edwards25519_group P (j + 1))
                      (bignum_quadruple_from_memory
                        (word_add stackpointer (word (616 + 128 * j)),4) s)) /\
              edwards25519_exprojective2
               (group_mul edwards25519_group
                  (group_zpow edwards25519_group P
                    (&(n DIV 2 EXP (4 * i)) - &(recoder DIV 2 EXP (4 * i))))
                  (group_zpow edwards25519_group E_25519
                    (&(m DIV 2 EXP (4 * i)) - &(recoder DIV 2 EXP (4 * i)))))
               (bignum_quadruple_from_memory
                 (word_add stackpointer (word 488),4) s)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Recoding of m ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (bscalar,8 * 4)) s0` THEN
    X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (17--20) (1--24) THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word 232),8 * 4)) s24 = m`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * 4)` THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND] THEN
      ASM_SIMP_TAC[ARITH_RULE `n < 9 * 2 EXP 252 ==> n < 2 EXP (64 * 4)`] THEN
      EXPAND_TAC "m" THEN
      REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      SUBGOAL_THEN
       `m_input DIV 2 EXP 192 > 2 EXP 63 ==> 8 * n_25519 <= m_input + recoder`
      MP_TAC THENL
       [EXPAND_TAC "recoder" THEN
        REWRITE_TAC[n_25519] THEN ARITH_TAC;
        SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN DISCH_THEN(K ALL_TAC)] THEN
      EXPAND_TAC "m_input" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      EXPAND_TAC "recoder" THEN REWRITE_TAC[real_gt; n_25519] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[GSYM REAL_NOT_LE; COND_SWAP] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      EXPAND_TAC "recoder" THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    (*** Recoding of n ***)

    BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (scalar,8 * 4)) s24` THEN
    X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (40--43) (25--47) THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word 200),8 * 4)) s47 = n`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * 4)` THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND] THEN
      ASM_SIMP_TAC[ARITH_RULE `n < 9 * 2 EXP 252 ==> n < 2 EXP (64 * 4)`] THEN
      EXPAND_TAC "n" THEN
      REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      SUBGOAL_THEN
       `n_input DIV 2 EXP 192 > 2 EXP 63 ==> 8 * n_25519 <= n_input + recoder`
      MP_TAC THENL
       [EXPAND_TAC "recoder" THEN
        REWRITE_TAC[n_25519] THEN ARITH_TAC;
        SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN DISCH_THEN(K ALL_TAC)] THEN
      EXPAND_TAC "n_input" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      EXPAND_TAC "recoder" THEN REWRITE_TAC[real_gt; n_25519] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[GSYM REAL_NOT_LE; COND_SWAP] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      EXPAND_TAC "recoder" THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    (*** Modular reduction of x ***)

    BIGNUM_LDIGITIZE_TAC "x_" `read(memory :> bytes(point,8 * 4)) s47` THEN
    X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (56--59) (48--67) THEN
    ABBREV_TAC
     `X =
      read(memory :> bytes(word_add stackpointer (word 616),8 * 4)) s67` THEN
    SUBGOAL_THEN `x MOD (2 * p_25519) = X` MP_TAC THENL
     [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN MAP_EVERY EXISTS_TAC
       [`256`;
       `(if x < 2 * p_25519 then &x else &x - &2 * &p_25519):real`] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "X" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[ARITH_RULE `256 = 64 * 4`; BIGNUM_FROM_MEMORY_BOUND];
        ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM NOT_LE; COND_SWAP];
        SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
        ONCE_REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC MOD_CASES THEN
        EXPAND_TAC "x" THEN REWRITE_TAC[p_25519] THEN
        CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]] THEN
      SUBGOAL_THEN `carry_s59 <=> 2 * p_25519 <= x` (SUBST1_TAC o SYM) THENL
       [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
        EXPAND_TAC "x" THEN REWRITE_TAC[p_25519] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_POP_ASSUM_LIST
         (MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        MAP_EVERY EXPAND_TAC ["X"; "x"] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_25519] THEN
        ASM_REWRITE_TAC[] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
      GEN_REWRITE_TAC LAND_CONV [MOD_UNIQUE] THEN
      REWRITE_TAC[MULT_EQ_0; ARITH_EQ; p_25519] THEN
      REWRITE_TAC[GSYM p_25519] THEN STRIP_TAC] THEN

    (*** Modular reduction of y ***)

    BIGNUM_LDIGITIZE_TAC
      "y_" `read(memory :> bytes(word_add point (word 32),8 * 4)) s67` THEN
    X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (76--79) (68--87) THEN
    ABBREV_TAC
     `Y =
      read(memory :> bytes(word_add stackpointer (word 648),8 * 4)) s87` THEN
    SUBGOAL_THEN `y MOD (2 * p_25519) = Y` MP_TAC THENL
     [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN MAP_EVERY EXISTS_TAC
       [`256`;
       `(if y < 2 * p_25519 then &y else &y - &2 * &p_25519):real`] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "Y" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[ARITH_RULE `256 = 64 * 4`; BIGNUM_FROM_MEMORY_BOUND];
        ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM NOT_LE; COND_SWAP];
        SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
        ONCE_REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC MOD_CASES THEN
        EXPAND_TAC "y" THEN REWRITE_TAC[p_25519] THEN
        CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]] THEN
      SUBGOAL_THEN `carry_s79 <=> 2 * p_25519 <= y` (SUBST1_TAC o SYM) THENL
       [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
        EXPAND_TAC "y" THEN REWRITE_TAC[p_25519] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        MAP_EVERY EXPAND_TAC ["Y"; "y"] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_25519] THEN
        ASM_REWRITE_TAC[] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
      GEN_REWRITE_TAC LAND_CONV [MOD_UNIQUE] THEN
      REWRITE_TAC[MULT_EQ_0; ARITH_EQ; p_25519] THEN
      REWRITE_TAC[GSYM p_25519] THEN STRIP_TAC] THEN

    (*** Creation of point multiple 1 ****)

    LOCAL_MUL_4_TAC 9 ["x_0"; "x_1"; "x_2"] THEN
    REABBREV_TAC
     `W =
      read(memory :> bytes(word_add stackpointer (word 712),8 * 4)) s97` THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    ABBREV_TAC
     `Z =
      read(memory :> bytes(word_add stackpointer (word 680),8 * 4)) s97` THEN
    SUBGOAL_THEN `Z < 2 * p_25519 /\ (Z == 1) (mod (2 * p_25519))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Z" THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
      ASM_REWRITE_TAC[VAL_WORD_0; VAL_WORD_1; p_25519; CONG] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 1) (X,Y,Z,W)`
    ASSUME_TAC THENL
     [X_GEN_TAC `P:int#int` THEN SIMP_TAC[GROUP_POW_1] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
      ASM_REWRITE_TAC[paired; modular_decode; edwards25519_exprojective2] THEN
      SIMP_TAC[edwards25519_exprojective; EXPROJECTIVE_ALT;
                FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
      REWRITE_TAC[INTEGER_MOD_RING_CARRIER_REM; INTEGER_MOD_RING_CLAUSES;
                  GSYM INT_OF_NUM_REM] THEN
      REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD p_25519` o
             GEN_REWRITE_RULE I [CONG])) THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] MOD_MOD; MOD_MOD_REFL] THEN
      REPEAT(DISCH_THEN SUBST1_TAC) THEN CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC[MULT_CLAUSES] THEN
      REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [CONG]))] THEN

    (*** Creation of point multiple 2 ****)

    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (98--101) THEN
    LOCAL_EPDOUBLE_TAC 102 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_2 = read(memory :> bytes(word_add stackpointer (word 744),8 * 4)) s102`;
      `Y_2 = read(memory :> bytes(word_add stackpointer (word 776),8 * 4)) s102`;
      `Z_2 = read(memory :> bytes(word_add stackpointer (word 808),8 * 4)) s102`;
      `W_2 = read(memory :> bytes(word_add stackpointer (word 840),8 * 4)) s102`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 2) (X_2,Y_2,Z_2,W_2)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `group_pow edwards25519_group P 1`) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 THEN
      EXISTS_TAC `W:num` THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 3 ****)

    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (103--109) THEN
    LOCAL_EPADD_TAC 110 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_3 = read(memory :> bytes(word_add stackpointer (word 872),8 * 4)) s110`;
      `Y_3 = read(memory :> bytes(word_add stackpointer (word 904),8 * 4)) s110`;
      `Z_3 = read(memory :> bytes(word_add stackpointer (word 936),8 * 4)) s110`;
      `W_3 = read(memory :> bytes(word_add stackpointer (word 968),8 * 4)) s110`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 3) (X_3,Y_3,Z_3,W_3)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`group_pow edwards25519_group P 1`;
        `group_pow edwards25519_group P 2`]) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 4 ****)

    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (111--116) THEN
    LOCAL_EPDOUBLE_TAC 117 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_4 = read(memory :> bytes(word_add stackpointer (word 1000),8 * 4)) s117`;
      `Y_4 = read(memory :> bytes(word_add stackpointer (word 1032),8 * 4)) s117`;
      `Z_4 = read(memory :> bytes(word_add stackpointer (word 1064),8 * 4)) s117`;
      `W_4 = read(memory :> bytes(word_add stackpointer (word 1096),8 * 4)) s117`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 4) (X_4,Y_4,Z_4,W_4)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `group_pow edwards25519_group P 2`) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 THEN
      EXISTS_TAC `W_2:num` THEN
      RULE_ASSUM_TAC(SIMP_RULE[GROUP_POW_1]) THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 5 ****)

    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (118--124) THEN
    LOCAL_EPADD_TAC 125 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_5 = read(memory :> bytes(word_add stackpointer (word 1128),8 * 4)) s125`;
      `Y_5 = read(memory :> bytes(word_add stackpointer (word 1160),8 * 4)) s125`;
      `Z_5 = read(memory :> bytes(word_add stackpointer (word 1192),8 * 4)) s125`;
      `W_5 = read(memory :> bytes(word_add stackpointer (word 1224),8 * 4)) s125`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 5) (X_5,Y_5,Z_5,W_5)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`group_pow edwards25519_group P 1`;
        `group_pow edwards25519_group P 4`]) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 6 ****)

    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (126--131) THEN
    LOCAL_EPDOUBLE_TAC 132 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_6 = read(memory :> bytes(word_add stackpointer (word 1256),8 * 4)) s132`;
      `Y_6 = read(memory :> bytes(word_add stackpointer (word 1288),8 * 4)) s132`;
      `Z_6 = read(memory :> bytes(word_add stackpointer (word 1320),8 * 4)) s132`;
      `W_6 = read(memory :> bytes(word_add stackpointer (word 1352),8 * 4)) s132`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 6) (X_6,Y_6,Z_6,W_6)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `group_pow edwards25519_group P 3`) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 THEN
      EXISTS_TAC `W_3:num` THEN
      RULE_ASSUM_TAC(SIMP_RULE[GROUP_POW_1]) THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 7 ****)

    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (133--139) THEN
    LOCAL_EPADD_TAC 140 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_7 = read(memory :> bytes(word_add stackpointer (word 1384),8 * 4)) s140`;
      `Y_7 = read(memory :> bytes(word_add stackpointer (word 1416),8 * 4)) s140`;
      `Z_7 = read(memory :> bytes(word_add stackpointer (word 1448),8 * 4)) s140`;
      `W_7 = read(memory :> bytes(word_add stackpointer (word 1480),8 * 4)) s140`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 7) (X_7,Y_7,Z_7,W_7)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`group_pow edwards25519_group P 1`;
        `group_pow edwards25519_group P 6`]) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 8 ****)

    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (141--146) THEN
    LOCAL_EPDOUBLE_TAC 147 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_8 = read(memory :> bytes(word_add stackpointer (word 1512),8 * 4)) s147`;
      `Y_8 = read(memory :> bytes(word_add stackpointer (word 1544),8 * 4)) s147`;
      `Z_8 = read(memory :> bytes(word_add stackpointer (word 1576),8 * 4)) s147`;
      `W_8 = read(memory :> bytes(word_add stackpointer (word 1608),8 * 4)) s147`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 8) (X_8,Y_8,Z_8,W_8)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `group_pow edwards25519_group P 4`) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 THEN
      EXISTS_TAC `W_4:num` THEN
      RULE_ASSUM_TAC(SIMP_RULE[GROUP_POW_1]) THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN
    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (148--149) THEN

    (*** Top nybble of bscalar ***)

    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (150--154) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m DIV 2 EXP 252` o MATCH_MP (MESON[]
     `read (memory :> bytes64 (word_add stackpointer (word 1640))) s = x
      ==> !m. x = word m
              ==> read (memory :> bytes64 (word_add stackpointer (word 1640))) s =
                  word m`)) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "m" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[word_ushr];
      DISCH_TAC] THEN

    (*** Address the precomputed table separately ***)

    FIRST_ASSUM(MP_TAC o
      MATCH_MP EDWARDS25519DOUBLEBASE_TABLE_LEMMA) THEN
    REWRITE_TAC[ARITH_RULE `pc + 0x6fc9 + x = (pc + 0x6fc9) + x`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD] THEN
    ABBREV_TAC `wpc:int64 = word(pc + 0x6fc9)` THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV)) THEN
    BIGNUM_LDIGITIZE_TAC "tab_" `read(memory :> bytes(wpc,8 * 96)) s154` THEN
    CLARIFY_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `nonoverlapping_modulo (2 EXP 64) (val(stackpointer:int64),1672)
                                       (val(wpc:int64),768)`
    ASSUME_TAC THENL [EXPAND_TAC "wpc" THEN NONOVERLAPPING_TAC; ALL_TAC] THEN

    (*** Constant-time indexing into the precomputed table ***)

    ABBREV_TAC `ix = m DIV 2 EXP 252` THEN
    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (155--167) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `wpc:int64` o MATCH_MP (MESON[]
     `read RBP s = x ==> !w. x = w ==> read RBP s = w`)) THEN
    ANTS_TAC THENL [EXPAND_TAC "wpc" THEN CONV_TAC WORD_RULE; DISCH_TAC] THEN
    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (168--386) THEN
    MAP_EVERY ABBREV_TAC
     [`XPY = read(memory :> bytes(word_add stackpointer (word 392),8 * 4)) s386`;
      `YMX = read(memory :> bytes(word_add stackpointer (word 424),8 * 4)) s386`;
      `KXY = read(memory :> bytes(word_add stackpointer (word 456),8 * 4)) s386`]
    THEN
    SUBGOAL_THEN
     `edwards25519_epprojective (group_pow edwards25519_group E_25519 ix)
                                (XPY,YMX,KXY)`
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["XPY"; "YMX"; "KXY"] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `m DIV 2 EXP 252 < 9` MP_TAC THENL
       [UNDISCH_TAC `m < 9 * 2 EXP 252` THEN ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      SPEC_TAC(`ix:num`,`ix:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[CONJUNCT1 group_pow] THEN
      REWRITE_TAC[EDWARDS25519_GROUP; edwards25519_epprojective;
                  edwards_0; INTEGER_MOD_RING_CLAUSES] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[d_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV;
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o
        check(free_in `word_add (wpc:int64)` o concl))) THEN
      UNDISCH_THEN `m DIV 2 EXP 252 = ix` (SUBST_ALL_TAC o SYM) THEN
      DISCARD_MATCHING_ASSUMPTIONS [`read c s = if x then y else z`] THEN
      CLARIFY_TAC] THEN

    (*** Top nybble of scalar ***)

    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (387--389) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n DIV 2 EXP 252` o MATCH_MP (MESON[]
     `read (memory :> bytes64 (word_add stackpointer (word 1640))) s = x
      ==> !m. x = word m
              ==> read (memory :> bytes64 (word_add stackpointer (word 1640))) s =
                  word m`)) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "n" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[word_ushr];
      DISCH_TAC] THEN

    (*** Constant-time indexing in the fresh-point table ***)

    ABBREV_TAC `iy = n DIV 2 EXP 252` THEN
    BIGNUM_LDIGITIZE_TAC "fab_"
     `read(memory :> bytes(word_add stackpointer (word 616),8 * 128)) s389` THEN
    CLARIFY_TAC THEN
    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (390--709) THEN
    MAP_EVERY ABBREV_TAC
     [`Xt = read(memory :> bytes(word_add stackpointer (word 264),8 * 4)) s709`;
      `Yt = read(memory :> bytes(word_add stackpointer (word 296),8 * 4)) s709`;
      `Zt = read(memory :> bytes(word_add stackpointer (word 328),8 * 4)) s709`;
      `Wt = read(memory :> bytes(word_add stackpointer (word 360),8 * 4)) s709`]
    THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P iy) (Xt,Yt,Zt,Wt)`
    ASSUME_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `P:int#int`)) THEN
      ASM_REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN DISCH_TAC THEN
      MAP_EVERY EXPAND_TAC ["Xt";"Yt";"Zt";"Wt"] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `n DIV 2 EXP 252 < 9` MP_TAC THENL
       [UNDISCH_TAC `n < 9 * 2 EXP 252` THEN ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      SPEC_TAC(`iy:num`,`iy:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[CONJUNCT1 group_pow] THEN
        REWRITE_TAC[EDWARDS25519_GROUP; edwards25519_exprojective2;
         edwards25519_exprojective; edwards_0; INTEGER_MOD_RING_CLAUSES] THEN
        SIMP_TAC[EXPROJECTIVE_ALT; FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
        REWRITE_TAC[bignum_of_wordlist; INTEGER_MOD_RING_CLAUSES;
                    IN_INTEGER_MOD_RING_CARRIER;
                    GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        REWRITE_TAC[d_25519; p_25519] THEN
        CONV_TAC INT_REDUCE_CONV;
        FIRST_X_ASSUM(MP_TAC o check (is_conj o concl))] THEN
      REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[];
      UNDISCH_THEN `n DIV 2 EXP 252 = iy` (SUBST_ALL_TAC o SYM) THEN
      DISCARD_MATCHING_ASSUMPTIONS [`read c s = if x then y else z`]] THEN

    (*** The table entry addition ***)

    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (710--714) THEN
    LOCAL_PEPADD_TAC 715 THEN
    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (716--717) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    (*** Final proof of the invariant ***)

    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[] THEN X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`group_pow edwards25519_group P (n DIV 2 EXP 252)`;
      `group_pow edwards25519_group E_25519 (m DIV 2 EXP 252)`]) THEN
    ASM_SIMP_TAC[GENERATOR_IN_GROUP_CARRIER_EDWARDS25519; GROUP_POW] THEN
    ASM_SIMP_TAC[EDWARDS25519_EXPROJECTIVE2_IMP_EXPROJECTIVE2W;
                 EDWARDS25519_EPPROJECTIVE_IMP_EPPROJECTIVEW] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    EXPAND_TAC "recoder" THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[INT_SUB_RZERO; GROUP_NPOW] THEN
    REWRITE_TAC[EDWARDS25519_GROUP; edwards25519] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(K ALL_TAC o SPEC `P:int#int`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `P:int#int`)) THEN
    ASM_REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[];

    (*** Defer the main invariant proof to below ***)

    ALL_TAC;

    (*** The trivial loop-back subgoal ***)

    REPEAT STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    X86_SIM_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--3) THEN
    VAL_INT64_TAC `4 * i` THEN
    ASM_REWRITE_TAC[ARITH_RULE `4 * i = 0 <=> ~(0 < i)`];

    (*** The finale with the modular inverse ***)

    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    REWRITE_TAC[bignum_quadruple_from_memory] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN

    (*** Ghost up the still-relevant parts of the state ***)

    FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[]
     `(!x. P x ==> Q x /\ R x) ==> (!x. P x ==> R x)`)) THEN
    MAP_EVERY ABBREV_TAC
     [`X = read(memory :> bytes(word_add stackpointer (word 488),8 * 4)) s0`;
      `Y = read(memory :> bytes(word_add stackpointer (word 520),8 * 4)) s0`;
      `Z = read(memory :> bytes(word_add stackpointer (word 552),8 * 4)) s0`;
      `W = read(memory :> bytes(word_add stackpointer (word 584),8 * 4)) s0`]
    THEN DISCH_TAC THEN

    (*** Call the modular inverse ***)

    X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--5) THEN
    LOCAL_MODINV_TAC 6 THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP(MESON[PRIME_COPRIME_EQ; PRIME_P25519]
     `(bnx = if p_25519 divides n then 0 else inverse_mod p_25519 n)
      ==> coprime(p_25519,n) ==> bnx = inverse_mod p_25519 n`)) THEN
    ABBREV_TAC
     `Z' =
      read(memory :> bytes(word_add stackpointer (word 616),8 * 4)) s6` THEN

    (*** Final multiplications ***)

    LOCAL_MUL_P25519_TAC 3 ["x_0"; "x_1"; "x_2"] THEN
    LOCAL_MUL_P25519_TAC 4 ["x_0"; "x_1"; "x_2"] THEN

    (*** Finishing mathematics ***)

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:int#int`) THEN
    ASM_REWRITE_TAC[edwards25519_exprojective2] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SPEC_TAC
     (`group_mul edwards25519_group
        (group_zpow edwards25519_group P (&n - &recoder))
        (group_zpow edwards25519_group E_25519 (&m - &recoder))`,
      `Q:int#int`) THEN
    REWRITE_TAC[edwards25519_exprojective; edwards25519_exprojective] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    SIMP_TAC[EXPROJECTIVE_ALT; FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REWRITE_TAC[paired; modular_encode; PAIR_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
    REWRITE_TAC[p_25519; GSYM INT_OF_NUM_REM] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS_EQ; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM p_25519; GSYM INT_OF_NUM_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ_0; INT_REM_EQ] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `Z' < p_25519 /\ (Z * Z' == 1) (mod p_25519)`
    MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN MATCH_MP_TAC(TAUT
        `p /\ (q ==> r) /\ (p /\ q ==> s) ==> (p ==> q) ==> r /\ s`) THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519; num_divides];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INVERSE_MOD_BOUND] THEN
        REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
        MESON_TAC[INVERSE_MOD_RMUL]];
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; num_congruent]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(x * z:int == X) (mod p) /\ (y * z == Y) (mod p)
      ==> (z * z' == &1) (mod p)
          ==> (X * z' == x) (mod p) /\ (Y * z' == y) (mod p)`) THEN
    ASM_REWRITE_TAC[]] THEN

  (*** The preservation of the loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [MESON[] `(!x. P x ==> Q x /\ R x) <=>
             (!x. P x ==> Q x) /\ (!x. P x ==> R x)`] THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [bignum_quadruple_from_memory] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  GHOST_INTRO_TAC `Xa:num`
   `bignum_from_memory (word_add stackpointer (word 488),4)` THEN
  GHOST_INTRO_TAC `Ya:num`
   `bignum_from_memory (word_add stackpointer (word 520),4)` THEN
  GHOST_INTRO_TAC `Za:num`
   `bignum_from_memory (word_add stackpointer (word 552),4)` THEN
  GHOST_INTRO_TAC `Wa:num`
   `bignum_from_memory(word_add stackpointer (word 584),4)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  (*** Doubling to acc' = 2 * acc ***)

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word (4 * (i + 1))) (word 4) = word(4 * i)`]) THEN
  LOCAL_PDOUBLE_TAC 8 THEN MAP_EVERY ABBREV_TAC
   [`X2a = read(memory :> bytes(word_add stackpointer (word 488),8 * 4)) s8`;
    `Y2a = read(memory :> bytes(word_add stackpointer (word 520),8 * 4)) s8`;
    `Z2a = read(memory :> bytes(word_add stackpointer (word 552),8 * 4)) s8`
   ] THEN
  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (9--10) THEN

  (*** Selection of btable nybble ***)

  SUBGOAL_THEN
   `read(memory :> bytes64 (word_add stackpointer
         (word(200 + 8 * val(word_ushr (word (4 * i)) 6:int64) + 32)))) s10 =
    word(m DIV 2 EXP (64 * (4 * i) DIV 64) MOD 2 EXP (64 * 1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `200 + x + 32 = 232 + x`] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `i < 63 ==> MIN (4 - (4 * i) DIV 64) 1 = 1`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_THM_TAC THEN REPLICATE_TAC 7 AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Recoding offset to get indexing and negation flag ***)

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (11--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOD_64_CLAUSES]) THEN
  ABBREV_TAC `bf = (m DIV (2 EXP (4 * i))) MOD 16` THEN
  SUBGOAL_THEN
   `word_and
     (word_ushr
        (word ((m DIV 2 EXP (64 * (4 * i) DIV 64)) MOD 2 EXP 64))
        ((4 * i) MOD 64))
     (word 15):int64 = word bf`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD;
                ARITH_RULE `15 = 2 EXP 4 - 1`] THEN
    REWRITE_TAC[word_jushr; VAL_WORD_USHR; DIMINDEX_64; MOD_64_CLAUSES] THEN
    EXPAND_TAC "bf" THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `16 = 2 EXP 4`] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
    REWRITE_TAC[DIV_MOD; MOD_MOD_EXP_MIN; GSYM EXP_ADD; DIV_DIV] THEN
    REWRITE_TAC[ADD_ASSOC; ARITH_RULE `64 * i DIV 64 + i MOD 64 = i`] THEN
    AP_THM_TAC THEN REPLICATE_TAC 3 AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN
    REWRITE_TAC[ARITH_RULE
     `x <= 64 * y DIV 64 + z <=> x + y MOD 64 <= y + z`] THEN
    REWRITE_TAC[ARITH_RULE `64 = 4 * 16`; MOD_MULT2] THEN
    UNDISCH_TAC `i < 63` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word bf:int64) = bf` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    EXPAND_TAC "bf" THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ix = if bf < 8 then 8 - bf else bf - 8` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word ix:int64` o MATCH_MP (MESON[]
   `read c s = word_sub a b
    ==> !x'. word_sub a b = x' ==> read c s = x'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "ix" THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_SUB; WORD_NEG_0;
     WORD_SUB_0; WORD_RULE
     `word_sub (word_not x) (word_neg(word 1)) = word_neg x`] THEN
    ASM_REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN

  (*** Address the precomputed table separately ***)

  FIRST_ASSUM(MP_TAC o
    MATCH_MP EDWARDS25519DOUBLEBASE_TABLE_LEMMA) THEN
  REWRITE_TAC[ARITH_RULE `pc + 0x6fc9 + x = (pc + 0x6fc9) + x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD] THEN
  ABBREV_TAC `wpc:int64 = word(pc + 0x6fc9)` THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV)) THEN
  BIGNUM_LDIGITIZE_TAC "tab_" `read(memory :> bytes(wpc,8 * 96)) s22` THEN
  CLARIFY_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64) (val(stackpointer:int64),1672)
                                     (val(wpc:int64),768)`
  ASSUME_TAC THENL [EXPAND_TAC "wpc" THEN NONOVERLAPPING_TAC; ALL_TAC] THEN

  (*** Constant-time indexing into the precomputed table ***)

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (23--35) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `wpc:int64` o MATCH_MP (MESON[]
   `read RBP s = x ==> !w. x = w ==> read RBP s = w`)) THEN
  ANTS_TAC THENL [EXPAND_TAC "wpc" THEN CONV_TAC WORD_RULE; DISCH_TAC] THEN
  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (36--242) THEN

  MAP_EVERY REABBREV_TAC
   [`tab0 = read RAX s242`;
    `tab1 = read RBX s242`;
    `tab2 = read RCX s242`;
    `tab3 = read RDX s242`;
    `tab4 = read R8 s242`;
    `tab5 = read R9 s242`;
    `tab6 = read R10 s242`;
    `tab7 = read R11 s242`;
    `tab8 = read R12 s242`;
    `tab9 = read R13 s242`;
    `tab10 = read R14 s242`;
    `tab11 = read R15 s242`] THEN
  SUBGOAL_THEN
   `edwards25519_epprojective (group_pow edwards25519_group E_25519 ix)
     (bignum_of_wordlist[tab0; tab1; tab2; tab3],
      bignum_of_wordlist[tab4; tab5; tab6; tab7],
      bignum_of_wordlist[tab8; tab9; tab10; tab11])`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC
     (map (fun n -> "tab"^string_of_int n) (0--11)) THEN
    SUBGOAL_THEN `ix < 9` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["ix"; "bf"] THEN ARITH_TAC;
      SPEC_TAC(`ix:num`,`ix:num`)] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[CONJUNCT1 group_pow] THEN
    REWRITE_TAC[EDWARDS25519_GROUP; edwards25519_epprojective;
                edwards_0; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[d_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV;
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o
        check(free_in `word_add (wpc:int64)` o concl))) THEN
    CLARIFY_TAC] THEN

  (*** Optional negation of the table entry ***)

  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (270--273) (243--277) THEN
  MAP_EVERY ABBREV_TAC
   [`XPY = read(memory :> bytes(word_add stackpointer (word 392),8 * 4)) s277`;
    `YMX = read(memory :> bytes(word_add stackpointer (word 424),8 * 4)) s277`;
    `KXY = read(memory :> bytes(word_add stackpointer (word 456),8 * 4)) s277`]
  THEN
  SUBGOAL_THEN
   `edwards25519_epprojectivew
     (group_zpow edwards25519_group E_25519 (&bf - &8)) (XPY,YMX,KXY)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["XPY"; "YMX"; "KXY"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&bf - &8:int = if bf < 8 then --(&ix) else &ix`
    SUBST1_TAC THENL
     [EXPAND_TAC "ix" THEN
      SUBGOAL_THEN `bf < 16` MP_TAC THENL
       [EXPAND_TAC "bf" THEN ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM NOT_LT] THEN
      ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[GROUP_ZPOW_POW] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP
        EDWARDS25519_EPPROJECTIVE_IMP_EPPROJECTIVEW)
    THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
       EDWARDS25519_EPPROJECTIVEW_NEG);
      MATCH_MP_TAC EQ_IMP THEN REPLICATE_TAC 3 AP_TERM_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THENL
     [REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64];
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC] THEN
    DISCH_THEN(MAP_EVERY ASSUME_TAC o rev o CONJUNCTS) THEN
    REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(INTEGER_RULE `y:int = &2 * p - x ==> p divides (x + y)`) THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `(&0:int <= x /\ x < p) /\ (&0 <= y /\ y < p) ==> abs(x - y) < p`) THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_25519] THEN INT_ARITH_TAC] THEN
      REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP EDWARDS25519_EPPROJECTIVE_BOUND) THEN
      ARITH_TAC;
      REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `ix:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
     (free_in `edwards25519_epprojective` o concl))) THEN
    CLARIFY_TAC] THEN

  (*** Selection of fresh table nybble ***)

  SUBGOAL_THEN
   `read(memory :> bytes64 (word_add stackpointer
         (word(200 + 8 * val(word_ushr (word (4 * i)) 6:int64))))) s277 =
    word(n DIV 2 EXP (64 * (4 * i) DIV 64) MOD 2 EXP (64 * 1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `i < 63 ==> MIN (4 - (4 * i) DIV 64) 1 = 1`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_THM_TAC THEN REPLICATE_TAC 7 AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Recoding offset to get indexing and negation flag ***)

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (278--289) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOD_64_CLAUSES]) THEN
  ABBREV_TAC `cf = (n DIV (2 EXP (4 * i))) MOD 16` THEN
  SUBGOAL_THEN
   `word_and
     (word_ushr
        (word ((n DIV 2 EXP (64 * (4 * i) DIV 64)) MOD 2 EXP 64))
        ((4 * i) MOD 64))
     (word 15):int64 = word cf`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD;
                ARITH_RULE `15 = 2 EXP 4 - 1`] THEN
    REWRITE_TAC[word_jushr; VAL_WORD_USHR; DIMINDEX_64; MOD_64_CLAUSES] THEN
    EXPAND_TAC "cf" THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `16 = 2 EXP 4`] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
    REWRITE_TAC[DIV_MOD; MOD_MOD_EXP_MIN; GSYM EXP_ADD; DIV_DIV] THEN
    REWRITE_TAC[ADD_ASSOC; ARITH_RULE `64 * i DIV 64 + i MOD 64 = i`] THEN
    AP_THM_TAC THEN REPLICATE_TAC 3 AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN
    REWRITE_TAC[ARITH_RULE
     `x <= 64 * y DIV 64 + z <=> x + y MOD 64 <= y + z`] THEN
    REWRITE_TAC[ARITH_RULE `64 = 4 * 16`; MOD_MULT2] THEN
    UNDISCH_TAC `i < 63` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word cf:int64) = cf` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    EXPAND_TAC "cf" THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `iy = if cf < 8 then 8 - cf else cf - 8` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word iy:int64` o MATCH_MP (MESON[]
   `read c s = word_sub a b
    ==> !x'. word_sub a b = x' ==> read c s = x'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "iy" THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_SUB; WORD_NEG_0;
     WORD_SUB_0; WORD_RULE
     `word_sub (word_not x) (word_neg(word 1)) = word_neg x`] THEN
    ASM_REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN

  (*** Constant-time indexing in the fresh-point table ***)

  BIGNUM_LDIGITIZE_TAC "fab_"
   `read(memory :> bytes(word_add stackpointer (word 616),8 * 128)) s289` THEN
  CLARIFY_TAC THEN
  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (290--601) THEN

  MAP_EVERY REABBREV_TAC
   [`fab0 = read RAX s601`;
    `fab1 = read RBX s601`;
    `fab2 = read RCX s601`;
    `fab3 = read RDX s601`;
    `fab4 = read (memory :> bytes64(word_add stackpointer (word 296))) s601`;
    `fab5 = read (memory :> bytes64(word_add stackpointer (word 304))) s601`;
    `fab6 = read (memory :> bytes64(word_add stackpointer (word 312))) s601`;
    `fab7 = read (memory :> bytes64(word_add stackpointer (word 320))) s601`;
    `fab8 = read (memory :> bytes64(word_add stackpointer (word 328))) s601`;
    `fab9 = read (memory :> bytes64(word_add stackpointer (word 336))) s601`;
    `fab10 = read (memory :> bytes64(word_add stackpointer (word 344))) s601`;
    `fab11 = read (memory :> bytes64(word_add stackpointer (word 352))) s601`;
    `fab12 = read R8 s601`;
    `fab13 = read R9 s601`;
    `fab14 = read R10 s601`;
    `fab15 = read R11 s601`] THEN
  SUBGOAL_THEN
   `!P. P IN group_carrier edwards25519_group /\
        paired (modular_decode (256,p_25519)) (x,y) = P
        ==> edwards25519_exprojective2
             (group_pow edwards25519_group P iy)
             (bignum_of_wordlist[fab0; fab1; fab2; fab3],
              bignum_of_wordlist[fab4; fab5; fab6; fab7],
              bignum_of_wordlist[fab8; fab9; fab10; fab11],
              bignum_of_wordlist[fab12; fab13; fab14; fab15])`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `P:int#int`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC
     (map (fun n -> "fab"^string_of_int n) (0--15)) THEN
    SUBGOAL_THEN `iy < 9` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["iy"; "cf"] THEN ARITH_TAC;
      SPEC_TAC(`iy:num`,`iy:num`)] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[CONJUNCT1 group_pow] THEN
    REWRITE_TAC[EDWARDS25519_GROUP; edwards25519_exprojective2;
     edwards25519_exprojective; edwards_0; INTEGER_MOD_RING_CLAUSES] THEN
    SIMP_TAC[EXPROJECTIVE_ALT; FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REWRITE_TAC[bignum_of_wordlist; INTEGER_MOD_RING_CLAUSES;
                IN_INTEGER_MOD_RING_CARRIER;
                GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[d_25519; p_25519] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Optional negation of the table entry ***)

  X86_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
    [612;613;614;615;620;621;622;623] (602--627) THEN
  MAP_EVERY ABBREV_TAC
   [`Xb = read(memory :> bytes(word_add stackpointer (word 264),8 * 4)) s627`;
    `Yb = read(memory :> bytes(word_add stackpointer (word 296),8 * 4)) s627`;
    `Zb = read(memory :> bytes(word_add stackpointer (word 328),8 * 4)) s627`;
    `Wb = read(memory :> bytes(word_add stackpointer (word 360),8 * 4)) s627`]
  THEN
  SUBGOAL_THEN
   `!P. P IN group_carrier edwards25519_group /\
        paired (modular_decode (256,p_25519)) (x,y) = P
        ==> edwards25519_exprojective2w
              (group_zpow edwards25519_group P (&cf - &8)) (Xb,Yb,Zb,Wb)`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(K ALL_TAC o SPEC `P:int#int`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `P:int#int`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["Xb"; "Yb"; "Zb"; "Wb"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&cf - &8:int = if cf < 8 then --(&iy) else &iy`
    SUBST1_TAC THENL
     [EXPAND_TAC "iy" THEN
      SUBGOAL_THEN `cf < 16` MP_TAC THENL
       [EXPAND_TAC "cf" THEN ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM NOT_LT] THEN
      ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[GROUP_ZPOW_POW] THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (ONCE_REWRITE_RULE[IMP_CONJ] EDWARDS25519_EXPROJECTIVE2W_NEG)) THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
      REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
      REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THEN REAL_INTEGER_TAC;
      FIRST_ASSUM(MP_TAC o MATCH_MP
        EDWARDS25519_EXPROJECTIVE2_IMP_EXPROJECTIVE2W) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[PAIR_EQ] THEN
      REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
      REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `iy:num` o concl))) THEN
    CLARIFY_TAC] THEN

  (*** Doubling to acc' = 4 * acc ***)

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (628--631) THEN
  LOCAL_PDOUBLE_TAC 632 THEN MAP_EVERY ABBREV_TAC
   [`X4a = read(memory :> bytes(word_add stackpointer (word 488),8 * 4)) s632`;
    `Y4a = read(memory :> bytes(word_add stackpointer (word 520),8 * 4)) s632`;
    `Z4a = read(memory :> bytes(word_add stackpointer (word 552),8 * 4)) s632`
   ] THEN
  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (633--634) THEN

  (*** Addition of precomputed and fresh table entries ***)

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (635--639) THEN
  LOCAL_PEPADD_TAC 640 THEN MAP_EVERY ABBREV_TAC
   [`Xc = read(memory :> bytes(word_add stackpointer (word 264),8 * 4)) s640`;
    `Yc = read(memory :> bytes(word_add stackpointer (word 296),8 * 4)) s640`;
    `Zc = read(memory :> bytes(word_add stackpointer (word 328),8 * 4)) s640`;
    `Wc = read(memory :> bytes(word_add stackpointer (word 360),8 * 4)) s640`
   ] THEN
  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (641--642) THEN

  (*** Doubling to acc' = 8 * acc ***)

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (643--646) THEN
  LOCAL_PDOUBLE_TAC 647 THEN MAP_EVERY ABBREV_TAC
   [`X8a = read(memory :> bytes(word_add stackpointer (word 488),8 * 4)) s647`;
    `Y8a = read(memory :> bytes(word_add stackpointer (word 520),8 * 4)) s647`;
    `Z8a = read(memory :> bytes(word_add stackpointer (word 552),8 * 4)) s647`
   ] THEN
  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (648--649) THEN

  (*** Doubling to acc' = 16 * acc ***)

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (650--653) THEN
  LOCAL_EPDOUBLE_TAC 654 THEN MAP_EVERY ABBREV_TAC
   [`Xha = read(memory :> bytes(word_add stackpointer (word 488),8 * 4)) s654`;
    `Yha = read(memory :> bytes(word_add stackpointer (word 520),8 * 4)) s654`;
    `Zha = read(memory :> bytes(word_add stackpointer (word 552),8 * 4)) s654`;
    `Wha = read(memory :> bytes(word_add stackpointer (word 584),8 * 4)) s654`
   ] THEN
  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (655--656) THEN

  (*** The final addition acc' = 16 * acc + tables ***)

  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (657--661) THEN
  LOCAL_EPADD_TAC 662 THEN MAP_EVERY ABBREV_TAC
   [`Xf = read(memory :> bytes(word_add stackpointer (word 488),8 * 4)) s662`;
    `Yf = read(memory :> bytes(word_add stackpointer (word 520),8 * 4)) s662`;
    `Zf = read(memory :> bytes(word_add stackpointer (word 552),8 * 4)) s662`;
    `Wf = read(memory :> bytes(word_add stackpointer (word 584),8 * 4)) s662`
   ] THEN
  X86_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (663--664) THEN

  (*** The final mathematics of adding the points up ***)

  FIRST_X_ASSUM(MP_TAC o
    check (can (term_match [] `(MAYCHANGE a ,, b) s s'` o concl))) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN MP_TAC th) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bignum_quadruple_from_memory] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_SIMP_TAC[] THEN
  DISCARD_STATE_TAC "s664" THEN
  X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_forall o concl))) THEN
  REWRITE_TAC[REWRITE_RULE[GSYM edwards25519]
   (GSYM(CONJUNCT2 EDWARDS25519_GROUP))] THEN
  SIMP_TAC[GSYM GROUP_POW_2] THEN
  DISCH_THEN(MP_TAC o SPEC `P:int#int`) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `Q = group_mul edwards25519_group
          (group_zpow edwards25519_group P
            (&(n DIV 2 EXP (4 * (i + 1))) -
             &(recoder DIV 2 EXP (4 * (i + 1)))))
          (group_zpow edwards25519_group E_25519
             (&(m DIV 2 EXP (4 * (i + 1))) -
              &(recoder DIV 2 EXP (4 * (i + 1)))))` THEN
  SUBGOAL_THEN `Q IN group_carrier edwards25519_group` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC GROUP_MUL THEN
    ASM_SIMP_TAC[GROUP_ZPOW; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519];
    DISCH_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Q:int#int`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 THEN
    EXISTS_TAC `Wa:num` THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `P:int#int`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `group_pow edwards25519_group (Q:int#int) 2`) THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_POW_POW] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPECL
   [`group_zpow edwards25519_group P (&cf - &8)`;
    `group_zpow edwards25519_group E_25519 (&bf - &8)`]) THEN
  ASM_SIMP_TAC[GROUP_ZPOW; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519] THEN
  DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `group_pow edwards25519_group (Q:int#int) 4`) THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_POW_POW] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `group_pow edwards25519_group (Q:int#int) 8`) THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_POW_POW] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPECL
   [`group_pow edwards25519_group Q 16`;
    `group_mul edwards25519_group
       (group_zpow edwards25519_group P (&cf - &8))
       (group_zpow edwards25519_group E_25519 (&bf - &8))`]) THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_ZPOW; GROUP_MUL;
               GENERATOR_IN_GROUP_CARRIER_EDWARDS25519] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!n. n DIV 2 EXP (4 * i) =
        16 * (n DIV 2 EXP (4 * (i + 1))) + (n DIV 2 EXP (4 * i)) MOD 16`
  MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`; EXP_ADD] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN ARITH_TAC;
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(recoder DIV 2 EXP (4 * i)) MOD 16 = 8` SUBST1_TAC THENL
   [UNDISCH_TAC `i < 63` THEN SPEC_TAC(`i:num`,`i:num`) THEN
    EXPAND_TAC "recoder" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_ARITH
   `(&16 * x + y) - (&16 * z + &8):int =
    (x - z) * &16 + (y - &8)`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM GROUP_NPOW] THEN
  ASM_SIMP_TAC[ABELIAN_GROUP_MUL_ZPOW; ABELIAN_EDWARDS25519_GROUP;
               GENERATOR_IN_GROUP_CARRIER_EDWARDS25519; GROUP_ZPOW;
               GSYM GROUP_ZPOW_MUL; GROUP_ZPOW_ADD] THEN
  ASM_SIMP_TAC[GEN_REWRITE_RULE I [ABELIAN_GROUP_MUL_AC]
        ABELIAN_EDWARDS25519_GROUP; GROUP_MUL; GROUP_ZPOW;
        GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]);;

let EDWARDS25519_SCALARMULDOUBLE_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!res scalar point bscalar n xy m pc stackpointer returnaddress.
    ALL (nonoverlapping (word_sub stackpointer (word 1720),1720))
        [(word pc,0x72c9); (scalar,32); (point,64); (bscalar,32)] /\
    nonoverlapping (res,64) (word pc,0x72c9) /\
    nonoverlapping (res,64) (word_sub stackpointer (word 1720),1728)
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
               (APPEND edwards25519_scalarmuldouble_alt_tmc
                       edwards25519_scalarmuldouble_alt_data) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [res; scalar; point; bscalar] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_pair_from_memory (point,4) s = xy /\
              bignum_from_memory (bscalar,4) s = m)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              !P. P IN group_carrier edwards25519_group /\
                  paired (modular_decode (256,p_25519)) xy = P
                  ==> bignum_pair_from_memory(res,4) s =
                      paired (modular_encode (256,p_25519))
                             (group_mul edwards25519_group
                                 (group_pow edwards25519_group P n)
                                 (group_pow edwards25519_group E_25519 m)))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(res,64);
                     memory :> bytes(word_sub stackpointer (word 1720),1720)])`,
  REWRITE_TAC[BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
                 fst EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC] THEN
  X86_ADD_RETURN_STACK_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
   (REWRITE_RULE[BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
                 fst EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC]
    EDWARDS25519_SCALARMULDOUBLE_ALT_CORRECT)
    `[RBX; RBP; R12; R13; R14; R15]` 1720);;

let EDWARDS25519_SCALARMULDOUBLE_ALT_SUBROUTINE_CORRECT = time prove
 (`!res scalar point bscalar n xy m pc stackpointer returnaddress.
    ALL (nonoverlapping (word_sub stackpointer (word 1720),1720))
        [(word pc,0x72cd); (scalar,32); (point,64); (bscalar,32)] /\
    nonoverlapping (res,64) (word pc,0x72cd) /\
    nonoverlapping (res,64) (word_sub stackpointer (word 1720),1728)
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
               (APPEND edwards25519_scalarmuldouble_alt_mc
                       edwards25519_scalarmuldouble_alt_data) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [res; scalar; point; bscalar] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_pair_from_memory (point,4) s = xy /\
              bignum_from_memory (bscalar,4) s = m)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              !P. P IN group_carrier edwards25519_group /\
                  paired (modular_decode (256,p_25519)) xy = P
                  ==> bignum_pair_from_memory(res,4) s =
                      paired (modular_encode (256,p_25519))
                             (group_mul edwards25519_group
                                 (group_pow edwards25519_group P n)
                                 (group_pow edwards25519_group E_25519 m)))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(res,64);
                     memory :> bytes(word_sub stackpointer (word 1720),1720)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE EDWARDS25519_SCALARMULDOUBLE_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let edwards25519_scalarmuldouble_alt_windows_mc,
    edwards25519_scalarmuldouble_alt_windows_data =
  define_coda_from_elf 0x6fe3
  "edwards25519_scalarmuldouble_alt_windows_mc"
  "edwards25519_scalarmuldouble_alt_windows_data"
  "x86/curve25519/edwards25519_scalarmuldouble_alt.obj";;

let edwards25519_scalarmuldouble_alt_windows_tmc = define_trimmed "edwards25519_scalarmuldouble_alt_windows_tmc" edwards25519_scalarmuldouble_alt_windows_mc;;

let EDWARDS25519_SCALARMULDOUBLE_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!res scalar point bscalar n xy m pc stackpointer returnaddress.
    ALL (nonoverlapping (word_sub stackpointer (word 1744),1744))
        [(word pc,0x72df); (scalar,32); (point,64); (bscalar,32)] /\
    nonoverlapping (res,64) (word pc,0x72df) /\
    nonoverlapping (res,64) (word_sub stackpointer (word 1744),1752)
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
               (APPEND edwards25519_scalarmuldouble_alt_windows_tmc
                       edwards25519_scalarmuldouble_alt_windows_data) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [res; scalar; point; bscalar] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_pair_from_memory (point,4) s = xy /\
              bignum_from_memory (bscalar,4) s = m)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              !P. P IN group_carrier edwards25519_group /\
                  paired (modular_decode (256,p_25519)) xy = P
                  ==> bignum_pair_from_memory(res,4) s =
                      paired (modular_encode (256,p_25519))
                             (group_mul edwards25519_group
                                 (group_pow edwards25519_group P n)
                                 (group_pow edwards25519_group E_25519 m)))
       (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(res,64);
                   memory :> bytes(word_sub stackpointer (word 1744),1744)])`,
  let WINDOWS_EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC =
    X86_MK_EXEC_RULE edwards25519_scalarmuldouble_alt_windows_tmc
  and baseth =
    X86_SIMD_SHARPEN_RULE EDWARDS25519_SCALARMULDOUBLE_ALT_NOIBT_SUBROUTINE_CORRECT
    (REWRITE_TAC[BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
                 fst EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC] THEN
     X86_ADD_RETURN_STACK_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
      (REWRITE_RULE[BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
                    fst EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC]
       EDWARDS25519_SCALARMULDOUBLE_ALT_CORRECT)
       `[RBX; RBP; R12; R13; R14; R15]` 1720) in
  let subth =
   REWRITE_RULE[BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
                fst EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC] baseth in
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPLICATE_TAC 8 GEN_TAC THEN WORD_FORALL_OFFSET_TAC 1744 THEN
  REWRITE_TAC[ALL; WINDOWS_C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[BYTES_LOADED_APPEND_CLAUSE] THEN
  REWRITE_TAC[fst WINDOWS_EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC] THEN
  GEN_REWRITE_TAC
   (RATOR_CONV o LAND_CONV o ABS_CONV o RAND_CONV o ONCE_DEPTH_CONV)
   [bytes_loaded] THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES; CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num`
      edwards25519_scalarmuldouble_alt_windows_data)] THEN
  REWRITE_TAC[edwards25519_scalarmuldouble_alt_windows_data] THEN
  REWRITE_TAC[GSYM edwards25519_scalarmuldouble_alt_data] THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC WINDOWS_EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ARITH_RULE `pc + 0x6fdf = (pc + 0x16) + 0x6fc9`]) THEN
  X86_SUBROUTINE_SIM_TAC
    (edwards25519_scalarmuldouble_alt_windows_tmc,
     WINDOWS_EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC,
     0x16,edwards25519_scalarmuldouble_alt_tmc,subth)
        [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
         `read (memory :> bytes (read RSI s,8 * 4)) s`;
         `read (memory :> bytes (read RDX s,8 * 4)) s,
          read (memory :> bytes (word_add (read RDX s) (word(8 * 4)),8 * 4)) s`;
         `read (memory :> bytes (read RCX s,8 * 4)) s`;
         `pc + 0x16`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
        8 THEN
  X86_STEPS_TAC WINDOWS_EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (9--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let EDWARDS25519_SCALARMULDOUBLE_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!res scalar point bscalar n xy m pc stackpointer returnaddress.
    ALL (nonoverlapping (word_sub stackpointer (word 1744),1744))
        [(word pc,0x72e3); (scalar,32); (point,64); (bscalar,32)] /\
    nonoverlapping (res,64) (word pc,0x72e3) /\
    nonoverlapping (res,64) (word_sub stackpointer (word 1744),1752)
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
               (APPEND edwards25519_scalarmuldouble_alt_windows_mc
                       edwards25519_scalarmuldouble_alt_windows_data) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [res; scalar; point; bscalar] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_pair_from_memory (point,4) s = xy /\
              bignum_from_memory (bscalar,4) s = m)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              !P. P IN group_carrier edwards25519_group /\
                  paired (modular_decode (256,p_25519)) xy = P
                  ==> bignum_pair_from_memory(res,4) s =
                      paired (modular_encode (256,p_25519))
                             (group_mul edwards25519_group
                                 (group_pow edwards25519_group P n)
                                 (group_pow edwards25519_group E_25519 m)))
       (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(res,64);
                   memory :> bytes(word_sub stackpointer (word 1744),1744)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE EDWARDS25519_SCALARMULDOUBLE_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

