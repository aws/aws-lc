(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* MULX-based multiplication modulo p_521.                                   *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_mul_p521.o";;
 ****)

let bignum_mul_p521_mc =
  define_assert_from_elf "bignum_mul_p521_mc" "x86/p521/bignum_mul_p521.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x83; 0xec; 0x40;  (* SUB (% rsp) (Imm8 (word 64)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x11;        (* MOV (% rdx) (Memop Quadword (%% (rcx,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0e;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x66; 0x18;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x6e; 0x20;
                           (* MULX4 (% r13,% rbx) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x49; 0x11; 0xdc;        (* ADC (% r12) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x76; 0x28;
                           (* MULX4 (% r14,% rbx) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x49; 0x11; 0xdd;        (* ADC (% r13) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x7e; 0x30;
                           (* MULX4 (% r15,% rbx) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x46; 0x38;
                           (* MULX4 (% r8,% rbx) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x49; 0x11; 0xe8;        (* ADC (% r8) (% rbp) *)
  0x48; 0x8b; 0x51; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rcx,8))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x4e; 0x38;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADOX (% r9) (% rbp) *)
  0x49; 0x11; 0xe9;        (* ADC (% r9) (% rbp) *)
  0x48; 0x8b; 0x51; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rcx,16))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x38;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADOX (% r10) (% rbp) *)
  0x49; 0x11; 0xea;        (* ADC (% r10) (% rbp) *)
  0x48; 0x8b; 0x51; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rcx,24))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADOX (% r11) (% rbp) *)
  0x49; 0x11; 0xeb;        (* ADC (% r11) (% rbp) *)
  0x48; 0x8b; 0x51; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rcx,32))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x66; 0x38;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe5;
                           (* ADOX (% r12) (% rbp) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x48; 0x8b; 0x51; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rcx,40))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6e; 0x38;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADOX (% r13) (% rbp) *)
  0x49; 0x11; 0xed;        (* ADC (% r13) (% rbp) *)
  0x48; 0x8b; 0x51; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rcx,48))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x76; 0x38;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADOX (% r14) (% rbp) *)
  0x49; 0x11; 0xee;        (* ADC (% r14) (% rbp) *)
  0x48; 0x8b; 0x51; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rcx,56))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7e; 0x38;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADOX (% r15) (% rbp) *)
  0x49; 0x11; 0xef;        (* ADC (% r15) (% rbp) *)
  0x48; 0x8b; 0x56; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rsi,64))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x19;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rcx,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x59; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rcx,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x59; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rcx,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x59; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rcx,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x59; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rcx,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x59; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rcx,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x59; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rcx,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x59; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rcx,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADOX (% rbx) (% rbp) *)
  0x48; 0x11; 0xdd;        (* ADC (% rbp) (% rbx) *)
  0x48; 0x8b; 0x51; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rcx,64))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% rbp) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0x48; 0x11; 0xc5;        (* ADC (% rbp) (% rax) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x25; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rax) (Imm32 (word 511)) *)
  0x4d; 0x0f; 0xac; 0xc8; 0x09;
                           (* SHRD (% r8) (% r9) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xd1; 0x09;
                           (* SHRD (% r9) (% r10) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xda; 0x09;
                           (* SHRD (% r10) (% r11) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xe3; 0x09;
                           (* SHRD (% r11) (% r12) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xec; 0x09;
                           (* SHRD (% r12) (% r13) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xf5; 0x09;
                           (* SHRD (% r13) (% r14) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xfe; 0x09;
                           (* SHRD (% r14) (% r15) (Imm8 (word 9)) *)
  0x49; 0x0f; 0xac; 0xef; 0x09;
                           (* SHRD (% r15) (% rbp) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xed; 0x09;  (* SHR (% rbp) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0xf9;                    (* STCF *)
  0x4c; 0x13; 0x04; 0x24;  (* ADC (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x08;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x13; 0x54; 0x24; 0x10;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x18;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x13; 0x64; 0x24; 0x20;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x13; 0x6c; 0x24; 0x28;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x13; 0x74; 0x24; 0x30;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x13; 0x7c; 0x24; 0x38;
                           (* ADC (% r15) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x81; 0xd5; 0x00; 0xfe; 0xff; 0xff;
                           (* ADC (% rbp) (Imm32 (word 4294966784)) *)
  0xf5;                    (* CMC *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x77; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r14) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x7f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r15) *)
  0x48; 0x83; 0xdd; 0x00;  (* SBB (% rbp) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe5; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rbp) (Imm32 (word 511)) *)
  0x48; 0x89; 0x6f; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rbp) *)
  0x48; 0x83; 0xc4; 0x40;  (* ADD (% rsp) (Imm8 (word 64)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0xc3                     (* RET *)
];;

let bignum_mul_p521_tmc = define_trimmed "bignum_mul_p521_tmc" bignum_mul_p521_mc;;

let BIGNUM_MUL_P521_EXEC = X86_MK_CORE_EXEC_RULE bignum_mul_p521_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_MUL_P521_CORRECT = prove
 (`!z x y a b pc stackpointer.
        ALL (nonoverlapping (stackpointer,64))
            [(word pc,0x6a7); (z,8 * 9); (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,0x6a7)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_mul_p521_tmc) /\
                  read RIP s = word(pc + 0x0e) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read RIP s = word (pc + 0x698) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [RIP; RAX; RBP; RBX; RCX; RDX;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                         memory :> bytes(stackpointer,64)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`;
     `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALL; C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 /\ b < p_521 assumption for simplicity ***)

  ASM_CASES_TAC `a < p_521 /\ b < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    X86_SIM_TAC BIGNUM_MUL_P521_EXEC (1--313)] THEN

  (*** Digitize, deduce the bound on the top words ***)

  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,9) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y_" `bignum_from_memory (y,9) s0` THEN
  SUBGOAL_THEN
   `a DIV 2 EXP 512 < 2 EXP 9 /\ b DIV 2 EXP 512 < 2 EXP 9`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN

  (*** Simulate the initial multiplication ***)

  X86_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC (1--271) (1--271) THEN

  (*** Introduce more systematic names for the high part digits ***)

  REABBREV_TAC `h0 = read R8 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h1 = read R9 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h2 = read R10 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h3 = read R11 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h4 = read R12 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h5 = read R13 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h6 = read R14 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h7 = read R15 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h8 = read RBP s271` THEN POP_ASSUM SUBST_ALL_TAC THEN

  (*** Show that the core multiplication operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_from_memory(stackpointer,8) s271 =
    a * b`
  ASSUME_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`1088`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[EXP_2; ARITH_RULE `2 EXP 1088 = 2 EXP 544 EXP 2`] THEN
      MATCH_MP_TAC LT_MULT2 THEN
      MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the rotation part ***)

  X86_STEPS_TAC BIGNUM_MUL_P521_EXEC (272--283) THEN

  (*** Break up into high and low parts ***)

  ABBREV_TAC `h = (a * b) DIV 2 EXP 521` THEN
  ABBREV_TAC `l = (a * b) MOD 2 EXP 521` THEN
  SUBGOAL_THEN `h < p_521 /\ l <= p_521` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_521] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LET_TRANS `(p_521 - 1) EXP 2` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < n ==> x <= n - 1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a * b) MOD p_521 = (h + l) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`a * b:num`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[CONG; p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(a * b) DIV 2 EXP 521 =
    bignum_of_wordlist
     [word_subword (word_join (h1:int64) h0:int128) (9,64);
      word_subword (word_join (h2:int64) h1:int128) (9,64);
      word_subword (word_join (h3:int64) h2:int128) (9,64);
      word_subword (word_join (h4:int64) h3:int128) (9,64);
      word_subword (word_join (h5:int64) h4:int128) (9,64);
      word_subword (word_join (h6:int64) h5:int128) (9,64);
      word_subword (word_join (h7:int64) h6:int128) (9,64);
      word_subword (word_join (h8:int64) h7:int128) (9,64);
      word_ushr h8 9] /\
    (a * b) MOD 2 EXP 521 =
    2 EXP 512 * val(word_and h0 (word 511):int64) +
    bignum_of_wordlist
     [mullo_s4; sum_s24; sum_s52; sum_s80; sum_s108; sum_s136; sum_s164;
      sum_s192]`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC DIVMOD_UNIQ THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD_USHR] THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
      ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE
       `x < 2 EXP (64 * 8) ==> 2 EXP 512 * h MOD 2 EXP 9 + x < 2 EXP 521`) THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN REWRITE_TAC[LENGTH; ARITH]];
    ALL_TAC] THEN

  (*** The net comparison h + l >= p_521 ***)

  X86_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC (284--293) (284--293) THEN
  SUBGOAL_THEN
   `&(val(word_add (word_ushr h8 9) (word_and h0 (word 511):int64))):real =
    &(val(word_ushr h8 9:int64)) + &(val(word_and h0 (word 511):int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN
    MP_TAC(SPEC `h8:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `carry_s293 <=> p_521 <= h + l` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final correction ***)

  X86_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC (294--313) (294--313) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if h + l < p_521 then &h + &l:real else (&h + &l) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[GSYM NOT_LT] THEN ABBREV_TAC `bb <=> h + l < p_521` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[REAL_OF_NUM_MOD] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ASM_SIMP_TAC[MOD_CASES; ARITH_RULE
     `h < p /\ l <= p ==> h + l < 2 * p`] THEN
    SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; COND_SWAP; GSYM NOT_LE] THEN
    MESON_TAC[]]);;

let BIGNUM_MUL_P521_NOIBT_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 9))
            [(word pc,LENGTH bignum_mul_p521_tmc); (word_sub stackpointer (word 112),120)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 112),112))
            [(word pc,LENGTH bignum_mul_p521_tmc); (x,8 * 9); (y,8 * 9)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_mul_p521_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 112),112)])`,
  X86_PROMOTE_RETURN_STACK_TAC
   bignum_mul_p521_tmc BIGNUM_MUL_P521_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 112);;

let BIGNUM_MUL_P521_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 9))
            [(word pc,LENGTH bignum_mul_p521_mc); (word_sub stackpointer (word 112),120)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 112),112))
            [(word pc,LENGTH bignum_mul_p521_mc); (x,8 * 9); (y,8 * 9)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_mul_p521_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 112),112)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUL_P521_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mul_p521_windows_mc = define_from_elf
   "bignum_mul_p521_windows_mc" "x86/p521/bignum_mul_p521.obj";;

let bignum_mul_p521_windows_tmc = define_trimmed "bignum_mul_p521_windows_tmc" bignum_mul_p521_windows_mc;;

let BIGNUM_MUL_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 9))
            [(word pc,LENGTH bignum_mul_p521_windows_tmc); (word_sub stackpointer (word 128),136)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 128),128))
            [(word pc,LENGTH bignum_mul_p521_windows_tmc); (x,8 * 9); (y,8 * 9)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_mul_p521_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 128),128)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   bignum_mul_p521_windows_tmc bignum_mul_p521_tmc BIGNUM_MUL_P521_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 112);;

let BIGNUM_MUL_P521_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 9))
            [(word pc,LENGTH bignum_mul_p521_windows_mc); (word_sub stackpointer (word 128),136)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 128),128))
            [(word pc,LENGTH bignum_mul_p521_windows_mc); (x,8 * 9); (y,8 * 9)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_mul_p521_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 128),128)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUL_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

