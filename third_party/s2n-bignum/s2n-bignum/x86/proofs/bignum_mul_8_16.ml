(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* MULX-based 8x8->16 multiplication.                                        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/fastmul/bignum_mul_8_16.o";;
 ****)

let bignum_mul_8_16_mc =
  define_assert_from_elf "bignum_mul_8_16_mc" "x86/fastmul/bignum_mul_8_16.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x11;        (* MOV (% rdx) (Memop Quadword (%% (rcx,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0e;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
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
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
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
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
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
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
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
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
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
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
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
  0x4c; 0x89; 0x77; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r14) *)
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
  0x4c; 0x89; 0x7f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r15) *)
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
  0x4c; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% r9) *)
  0x4c; 0x89; 0x57; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r11) *)
  0x4c; 0x89; 0x67; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% r13) *)
  0x4c; 0x89; 0x77; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% r15) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0xc3                     (* RET *)
];;

let bignum_mul_8_16_tmc = define_trimmed "bignum_mul_8_16_tmc" bignum_mul_8_16_mc;;

let BIGNUM_MUL_8_16_EXEC = X86_MK_CORE_EXEC_RULE bignum_mul_8_16_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUL_8_16_CORRECT = time prove
 (`!z x y a b pc.
     nonoverlapping (word pc,0x4cb) (z,8 * 16) /\
     nonoverlapping (x,8 * 8) (z,8 * 16) /\
     (y = z \/ nonoverlapping (y,8 * 8) (z,8 * 16))
     ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST bignum_mul_8_16_tmc) /\
               read RIP s = word(pc + 0x0a) /\
               C_ARGUMENTS [z; x; y] s /\
               bignum_from_memory (x,8) s = a /\
               bignum_from_memory (y,8) s = b)
          (\s. read RIP s = word (pc + 0x4c0) /\
               bignum_from_memory (z,16) s = a * b)
          (MAYCHANGE [RIP; RAX; RBP; RBX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,8) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,8) s0` THEN
  X86_ACCSTEPS_TAC BIGNUM_MUL_8_16_EXEC (1--224) (1--224) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let BIGNUM_MUL_8_16_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 48),56) (z,8 * 16) /\
     ALL (nonoverlapping (word_sub stackpointer (word 48),48))
         [(word pc,LENGTH bignum_mul_8_16_tmc); (x,8 * 8); (y,8 * 8)] /\
     nonoverlapping (word pc,LENGTH bignum_mul_8_16_tmc) (z,8 * 16) /\
     nonoverlapping (x,8 * 8) (z,8 * 16) /\
     (y = z \/ nonoverlapping (y,8 * 8) (z,8 * 16))
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_mul_8_16_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [z; x; y] s /\
               bignum_from_memory (x,8) s = a /\
               bignum_from_memory (y,8) s = b)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,16) s = a * b)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 16);
                memory :> bytes(word_sub stackpointer (word 48),48)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_mul_8_16_tmc BIGNUM_MUL_8_16_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_MUL_8_16_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 48),56) (z,8 * 16) /\
     ALL (nonoverlapping (word_sub stackpointer (word 48),48))
         [(word pc,LENGTH bignum_mul_8_16_mc); (x,8 * 8); (y,8 * 8)] /\
     nonoverlapping (word pc,LENGTH bignum_mul_8_16_mc) (z,8 * 16) /\
     nonoverlapping (x,8 * 8) (z,8 * 16) /\
     (y = z \/ nonoverlapping (y,8 * 8) (z,8 * 16))
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_mul_8_16_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [z; x; y] s /\
               bignum_from_memory (x,8) s = a /\
               bignum_from_memory (y,8) s = b)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,16) s = a * b)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 16);
                memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUL_8_16_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mul_8_16_windows_mc = define_from_elf
   "bignum_mul_8_16_windows_mc" "x86/fastmul/bignum_mul_8_16.obj";;

let bignum_mul_8_16_windows_tmc = define_trimmed "bignum_mul_8_16_windows_tmc" bignum_mul_8_16_windows_mc;;

let BIGNUM_MUL_8_16_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 64),72) (z,8 * 16) /\
     ALL (nonoverlapping (word_sub stackpointer (word 64),64))
         [(word pc,LENGTH bignum_mul_8_16_windows_tmc); (x,8 * 8); (y,8 * 8)] /\
     nonoverlapping (word pc,LENGTH bignum_mul_8_16_windows_tmc) (z,8 * 16) /\
     nonoverlapping (x,8 * 8) (z,8 * 16) /\
     (y = z \/ nonoverlapping (y,8 * 8) (z,8 * 16))
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_mul_8_16_windows_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [z; x; y] s /\
               bignum_from_memory (x,8) s = a /\
               bignum_from_memory (y,8) s = b)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,16) s = a * b)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 16);
                      memory :> bytes(word_sub stackpointer (word 64),64)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_mul_8_16_windows_tmc bignum_mul_8_16_tmc
    BIGNUM_MUL_8_16_CORRECT `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_MUL_8_16_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
     nonoverlapping (word_sub stackpointer (word 64),72) (z,8 * 16) /\
     ALL (nonoverlapping (word_sub stackpointer (word 64),64))
         [(word pc,LENGTH bignum_mul_8_16_windows_mc); (x,8 * 8); (y,8 * 8)] /\
     nonoverlapping (word pc,LENGTH bignum_mul_8_16_windows_mc) (z,8 * 16) /\
     nonoverlapping (x,8 * 8) (z,8 * 16) /\
     (y = z \/ nonoverlapping (y,8 * 8) (z,8 * 16))
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_mul_8_16_windows_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [z; x; y] s /\
               bignum_from_memory (x,8) s = a /\
               bignum_from_memory (y,8) s = b)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,16) s = a * b)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 16);
                      memory :> bytes(word_sub stackpointer (word 64),64)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUL_8_16_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

