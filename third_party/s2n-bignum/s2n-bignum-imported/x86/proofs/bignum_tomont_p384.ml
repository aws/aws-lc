(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 6-word (384-bit) bignum to Montgomery form modulo p_384.  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p384/bignum_tomont_p384.o";;
 ****)

let bignum_tomont_p384_mc =
  define_assert_from_elf "bignum_tomont_p384_mc" "x86/p384/bignum_tomont_p384.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744065119617025)) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0e;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xf3; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% rcx) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x49; 0x01; 0xc9;        (* ADD (% r9) (% rcx) *)
  0xc4; 0x62; 0xf3; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% r11,% rcx) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0xc4; 0x62; 0xf3; 0xf6; 0x66; 0x18;
                           (* MULX4 (% r12,% rcx) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0xc4; 0x62; 0xf3; 0xf6; 0x6e; 0x20;
                           (* MULX4 (% r13,% rcx) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0xc4; 0x62; 0xf3; 0xf6; 0x76; 0x28;
                           (* MULX4 (% r14,% rcx) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x49; 0x11; 0xcd;        (* ADC (% r13) (% rcx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x4c; 0x89; 0xc2;        (* MOV (% rdx) (% r8) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc2;        (* ADD (% rdx) (% r8) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0xbb; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r8) (% rdx,% rcx) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xeb;        (* SBB (% r11) (% rbp) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd6;        (* ADD (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 8589934592)) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x0e;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x08;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x10;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x18;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x28;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADCX (% r15) (% rbp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADOX (% r8) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADCX (% r8) (% rbp) *)
  0x4c; 0x89; 0xca;        (* MOV (% rdx) (% r9) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xca;        (* ADD (% rdx) (% r9) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0xb3; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r9) (% rdx,% rcx) *)
  0x4c; 0x11; 0xc8;        (* ADC (% rax) (% r9) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xec;        (* SBB (% r12) (% rbp) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd7;        (* ADD (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744065119617024)) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x0e;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x08;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x10;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x18;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x28;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADCX (% r8) (% rbp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADOX (% r9) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADCX (% r9) (% rbp) *)
  0x4c; 0x89; 0xd2;        (* MOV (% rdx) (% r10) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd2;        (* ADD (% rdx) (% r10) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0xab; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r10) (% rdx,% rcx) *)
  0x4c; 0x11; 0xd0;        (* ADC (% rax) (% r10) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xcc;        (* SBB (% r12) (% rcx) *)
  0x49; 0x19; 0xed;        (* SBB (% r13) (% rbp) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 8589934592)) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x0e;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x08;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x10;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x18;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x28;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADCX (% r9) (% rbp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADOX (% r10) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADCX (% r10) (% rbp) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xda;        (* ADD (% rdx) (% r11) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0xa3; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r11) (% rdx,% rcx) *)
  0x4c; 0x11; 0xd8;        (* ADC (% rax) (% r11) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc4;        (* SUB (% r12) (% rax) *)
  0x49; 0x19; 0xcd;        (* SBB (% r13) (% rcx) *)
  0x49; 0x19; 0xee;        (* SBB (% r14) (% rbp) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd1;        (* ADD (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4c; 0x03; 0x26;        (* ADD (% r12) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x13; 0x6e; 0x08;  (* ADC (% r13) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x13; 0x76; 0x10;  (* ADC (% r14) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x13; 0x7e; 0x18;  (* ADC (% r15) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x13; 0x46; 0x20;  (* ADC (% r8) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x13; 0x4e; 0x28;  (* ADC (% r9) (Memop Quadword (%% (rsi,40))) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xe2;        (* MOV (% rdx) (% r12) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe2;        (* ADD (% rdx) (% r12) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0x9b; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r12) (% rdx,% rcx) *)
  0x4c; 0x11; 0xe0;        (* ADC (% rax) (% r12) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc5;        (* SUB (% r13) (% rax) *)
  0x49; 0x19; 0xce;        (* SBB (% r14) (% rcx) *)
  0x49; 0x19; 0xef;        (* SBB (% r15) (% rbp) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd2;        (* ADD (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xea;        (* ADD (% rdx) (% r13) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xf3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rcx) (% rdx,% rax) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0xc4; 0xe2; 0x93; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% r13) (% rdx,% rcx) *)
  0x4c; 0x11; 0xe8;        (* ADC (% rax) (% r13) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x11; 0xed;              (* ADC (% ebp) (% ebp) *)
  0x49; 0x29; 0xc6;        (* SUB (% r14) (% rax) *)
  0x49; 0x19; 0xcf;        (* SBB (% r15) (% rcx) *)
  0x49; 0x19; 0xe8;        (* SBB (% r8) (% rbp) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xd3;        (* ADD (% r11) (% rdx) *)
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
  0x5d;                    (* POP (% rbp) *)
  0xc3                     (* RET *)
];;

let bignum_tomont_p384_tmc = define_trimmed "bignum_tomont_p384_tmc" bignum_tomont_p384_mc;;

let BIGNUM_TOMONT_P384_EXEC = X86_MK_CORE_EXEC_RULE bignum_tomont_p384_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let swlemma = WORD_RULE
  `word_add (word_shl x 32) x:int64 = word(4294967297 * val x)`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &(val(word(4294967297 * val x):int64)) * &18446744069414584321
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(4294967297 * val x):int64)) * &18446744069414584321`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_TOMONT_P384_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x44f) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_tomont_p384_tmc) /\
                  read RIP s = word(pc + 0x09) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = word (pc + 0x445) /\
                  bignum_from_memory (z,6) s = (2 EXP 384 * a) MOD p_384)
             (MAYCHANGE [RIP; RSI; RAX; RBP; RCX; RDX;
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
    X86_SINGLE_STEP_TAC BIGNUM_TOMONT_P384_EXEC s THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
    TRY(ACCUMULATE_ARITH_TAC s) THEN CLARIFY_TAC)
   (statenames "s" (1--210)) THEN

  (*** Do the congruential reasoning on the chosen multipliers ***)

  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Derive the main property of the pre-reduced form, which we call t ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
      [sum_s203; sum_s204; sum_s205; sum_s206;
       sum_s207; sum_s209; word (bitval carry_s209)]` THEN

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

  X86_ACCSTEPS_TAC BIGNUM_TOMONT_P384_EXEC (211--227) (211--227) THEN
  SUBGOAL_THEN
   `sum_s226:int64 = word(bitval(p_384 <= t))`
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

  X86_ACCSTEPS_TAC BIGNUM_TOMONT_P384_EXEC (228--242) (228--242) THEN
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

let BIGNUM_TOMONT_P384_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_tomont_p384_tmc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p384_tmc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p384_tmc /\
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
   bignum_tomont_p384_tmc BIGNUM_TOMONT_P384_CORRECT
   `[RBP; R12; R13; R14; R15]` 40);;

let BIGNUM_TOMONT_P384_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_tomont_p384_mc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p384_mc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p384_mc /\
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
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOMONT_P384_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_tomont_p384_windows_mc = define_from_elf
   "bignum_tomont_p384_windows_mc" "x86/p384/bignum_tomont_p384.obj";;

let bignum_tomont_p384_windows_tmc = define_trimmed "bignum_tomont_p384_windows_tmc" bignum_tomont_p384_windows_mc;;

let BIGNUM_TOMONT_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_tomont_p384_windows_tmc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p384_windows_tmc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p384_windows_tmc /\
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
   bignum_tomont_p384_windows_tmc bignum_tomont_p384_tmc
   BIGNUM_TOMONT_P384_CORRECT `[RBP; R12; R13; R14; R15]` 40);;

let BIGNUM_TOMONT_P384_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_tomont_p384_windows_mc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p384_windows_mc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p384_windows_mc /\
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
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOMONT_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

