(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extended Montgomery reduction of arbitrary bignum.                        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/fastmul/bignum_emontredc_8n.o";;
 ****)

let bignum_emontredc_8n_mc =
  define_assert_from_elf "bignum_emontredc_8n_mc" "x86/fastmul/bignum_emontredc_8n.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0xc1; 0xef; 0x03;  (* SHR (% rdi) (Imm8 (word 3)) *)
  0x0f; 0x84; 0x11; 0x0b; 0x00; 0x00;
                           (* JE (Imm32 (word 2833)) *)
  0x48; 0x8d; 0x5f; 0xff;  (* LEA (% rbx) (%% (rdi,18446744073709551615)) *)
  0x48; 0xc1; 0xe3; 0x06;  (* SHL (% rbx) (Imm8 (word 6)) *)
  0x53;                    (* PUSH (% rbx) *)
  0x57;                    (* PUSH (% rdi) *)
  0x48; 0x83; 0xec; 0x10;  (* SUB (% rsp) (Imm8 (word 16)) *)
  0x48; 0xc7; 0x04; 0x24; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,0))) (Imm32 (word 0)) *)
  0x48; 0x89; 0xd7;        (* MOV (% rdi) (% rdx) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0xc2; 0xeb; 0xf6; 0xc0;
                           (* MULX4 (% rax,% rdx) (% rdx,% r8) *)
  0x48; 0x89; 0x16;        (* MOV (Memop Quadword (%% (rsi,0))) (% rdx) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1f;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x8b; 0x66; 0x20;  (* MOV (% r12) (Memop Quadword (%% (rsi,32))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x8b; 0x6e; 0x28;  (* MOV (% r13) (Memop Quadword (%% (rsi,40))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x8b; 0x76; 0x30;  (* MOV (% r14) (Memop Quadword (%% (rsi,48))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x8b; 0x7e; 0x38;  (* MOV (% r15) (Memop Quadword (%% (rsi,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xc2; 0xeb; 0xf6; 0xc1;
                           (* MULX4 (% rax,% rdx) (% rdx,% r9) *)
  0x48; 0x89; 0x56; 0x08;  (* MOV (Memop Quadword (%% (rsi,8))) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1f;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xc2; 0xeb; 0xf6; 0xc2;
                           (* MULX4 (% rax,% rdx) (% rdx,% r10) *)
  0x48; 0x89; 0x56; 0x10;  (* MOV (Memop Quadword (%% (rsi,16))) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1f;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xc2; 0xeb; 0xf6; 0xc3;
                           (* MULX4 (% rax,% rdx) (% rdx,% r11) *)
  0x48; 0x89; 0x56; 0x18;  (* MOV (Memop Quadword (%% (rsi,24))) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1f;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xc2; 0xeb; 0xf6; 0xc4;
                           (* MULX4 (% rax,% rdx) (% rdx,% r12) *)
  0x48; 0x89; 0x56; 0x20;  (* MOV (Memop Quadword (%% (rsi,32))) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1f;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xc2; 0xeb; 0xf6; 0xc5;
                           (* MULX4 (% rax,% rdx) (% rdx,% r13) *)
  0x48; 0x89; 0x56; 0x28;  (* MOV (Memop Quadword (%% (rsi,40))) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1f;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xc2; 0xeb; 0xf6; 0xc6;
                           (* MULX4 (% rax,% rdx) (% rdx,% r14) *)
  0x48; 0x89; 0x56; 0x30;  (* MOV (Memop Quadword (%% (rsi,48))) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1f;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xc2; 0xeb; 0xf6; 0xc7;
                           (* MULX4 (% rax,% rdx) (% rdx,% r15) *)
  0x48; 0x89; 0x56; 0x38;  (* MOV (Memop Quadword (%% (rsi,56))) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1f;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5f; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rdi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x89; 0xf5;        (* MOV (% rbp) (% rsi) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x85; 0xc0;        (* TEST (% rax) (% rax) *)
  0x0f; 0x84; 0x6d; 0x05; 0x00; 0x00;
                           (* JE (Imm32 (word 1389)) *)
  0x48; 0x89; 0x44; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rax) *)
  0x48; 0x83; 0xc5; 0x40;  (* ADD (% rbp) (Imm8 (word 64)) *)
  0x48; 0x83; 0xc7; 0x40;  (* ADD (% rdi) (Imm8 (word 64)) *)
  0x48; 0x8b; 0x17;        (* MOV (% rdx) (Memop Quadword (%% (rdi,0))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x45; 0x00;
                           (* ADOX (% r8) (Memop Quadword (%% (rbp,0))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x4c; 0x89; 0x45; 0x00;  (* MOV (Memop Quadword (%% (rbp,0))) (% r8) *)
  0x41; 0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 0)) *)
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
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x57; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rdi,8))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x4d; 0x08;
                           (* ADOX (% r9) (Memop Quadword (%% (rbp,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x89; 0x4d; 0x08;  (* MOV (Memop Quadword (%% (rbp,8))) (% r9) *)
  0x41; 0xb9; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r9d) (Imm32 (word 0)) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x57; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x55; 0x10;
                           (* ADOX (% r10) (Memop Quadword (%% (rbp,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x89; 0x55; 0x10;  (* MOV (Memop Quadword (%% (rbp,16))) (% r10) *)
  0x41; 0xba; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 0)) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x57; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rdi,24))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x5d; 0x18;
                           (* ADOX (% r11) (Memop Quadword (%% (rbp,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x5d; 0x18;  (* MOV (Memop Quadword (%% (rbp,24))) (% r11) *)
  0x41; 0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r11d) (Imm32 (word 0)) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x57; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rdi,32))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x65; 0x20;
                           (* ADOX (% r12) (Memop Quadword (%% (rbp,32))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0x65; 0x20;  (* MOV (Memop Quadword (%% (rbp,32))) (% r12) *)
  0x41; 0xbc; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r12d) (Imm32 (word 0)) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x57; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rdi,40))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x6d; 0x28;
                           (* ADOX (% r13) (Memop Quadword (%% (rbp,40))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0x6d; 0x28;  (* MOV (Memop Quadword (%% (rbp,40))) (% r13) *)
  0x41; 0xbd; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r13d) (Imm32 (word 0)) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x57; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rdi,48))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x75; 0x30;
                           (* ADOX (% r14) (Memop Quadword (%% (rbp,48))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0x75; 0x30;  (* MOV (Memop Quadword (%% (rbp,48))) (% r14) *)
  0x41; 0xbe; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r14d) (Imm32 (word 0)) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x57; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rdi,56))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x7d; 0x38;
                           (* ADOX (% r15) (Memop Quadword (%% (rbp,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0x7d; 0x38;  (* MOV (Memop Quadword (%% (rbp,56))) (% r15) *)
  0x41; 0xbf; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r15d) (Imm32 (word 0)) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x83; 0x6c; 0x24; 0x08; 0x40;
                           (* SUB (Memop Quadword (%% (rsp,8))) (Imm8 (word 64)) *)
  0x0f; 0x85; 0x9d; 0xfa; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294965917)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x29; 0xc7;        (* SUB (% rdi) (% rax) *)
  0x48; 0x8b; 0x1c; 0x24;  (* MOV (% rbx) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xf7; 0xdb;        (* NEG (% rbx) *)
  0x4c; 0x11; 0x44; 0x06; 0x40;
                           (* ADC (Memop Quadword (%%%% (rsi,0,rax,&64))) (% r8) *)
  0x4c; 0x11; 0x4c; 0x06; 0x48;
                           (* ADC (Memop Quadword (%%%% (rsi,0,rax,&72))) (% r9) *)
  0x4c; 0x11; 0x54; 0x06; 0x50;
                           (* ADC (Memop Quadword (%%%% (rsi,0,rax,&80))) (% r10) *)
  0x4c; 0x11; 0x5c; 0x06; 0x58;
                           (* ADC (Memop Quadword (%%%% (rsi,0,rax,&88))) (% r11) *)
  0x4c; 0x11; 0x64; 0x06; 0x60;
                           (* ADC (Memop Quadword (%%%% (rsi,0,rax,&96))) (% r12) *)
  0x4c; 0x11; 0x6c; 0x06; 0x68;
                           (* ADC (Memop Quadword (%%%% (rsi,0,rax,&104))) (% r13) *)
  0x4c; 0x11; 0x74; 0x06; 0x70;
                           (* ADC (Memop Quadword (%%%% (rsi,0,rax,&112))) (% r14) *)
  0x4c; 0x11; 0x7c; 0x06; 0x78;
                           (* ADC (Memop Quadword (%%%% (rsi,0,rax,&120))) (% r15) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x48; 0x83; 0xc6; 0x40;  (* ADD (% rsi) (Imm8 (word 64)) *)
  0x48; 0x83; 0x6c; 0x24; 0x10; 0x01;
                           (* SUB (Memop Quadword (%% (rsp,16))) (Imm8 (word 1)) *)
  0x0f; 0x85; 0x0d; 0xf5; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294964493)) *)
  0x58;                    (* POP (% rax) *)
  0x48; 0x83; 0xc4; 0x18;  (* ADD (% rsp) (Imm8 (word 24)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0xc3                     (* RET *)
];;

let bignum_emontredc_8n_tmc = define_trimmed "bignum_emontredc_8n_tmc" bignum_emontredc_8n_mc;;

let BIGNUM_EMONTREDC_8N_EXEC = X86_MK_CORE_EXEC_RULE bignum_emontredc_8n_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** Lemma to justify zeros in the Montgomery steps ***)

let montgomery_lemma = prove
 (`!w n.
    (n * w + 1 == 0) (mod (2 EXP 64))
    ==> !h l x.
            &2 pow 64 * &h + &l:real =
            &(val(word_zx(word (w * x):int128):int64)) *
            &(val(word(bigdigit n 0):int64))
            ==> !h' l'. &2 pow 64 * &h' + &(val l'):real = &x + &l
                        ==> val(l':int64) = 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; GSYM LOWDIGITS_1; lowdigits] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_MOD_REFL] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`)) THEN
  REWRITE_TAC[MOD_MULT_ADD; DIMINDEX_128; DIMINDEX_64; MULT_CLAUSES] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `MIN 64 64 = 64 /\ MIN 128 64 = 64`] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG; GSYM DIVIDES_MOD] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`2 EXP 64`,`p:num`) THEN
  CONV_TAC NUMBER_RULE);;

let BIGNUM_EMONTREDC_8N_CORRECT = time prove
 (`!k z m w a n pc stackpointer.
      nonoverlapping (z,8 * 2 * val k) (word_sub stackpointer (word 32),32) /\
      ALLPAIRS nonoverlapping
         [(z,8 * 2 * val k); (word_sub stackpointer (word 32),32)]
         [(word pc,0xb32); (m,8 * val k)] /\
      8 divides val k
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_emontredc_8n_tmc) /\
                read RIP s = word(pc + 0xa) /\
                read RSP s = stackpointer /\
                C_ARGUMENTS [k; z; m; w] s /\
                bignum_from_memory (z,2 * val k) s = a /\
                bignum_from_memory (m,val k) s = n)
           (\s. read RIP s = word(pc + 0xb27) /\
                ((n * val w + 1 == 0) (mod (2 EXP 64))
                 ==> n * bignum_from_memory (z,val k) s + a =
                     2 EXP (64 * val k) *
                     (2 EXP (64 * val k) * val(C_RETURN s) +
                      bignum_from_memory
                        (word_add z (word(8 * val k)),val k) s)))
           (MAYCHANGE [RIP; RDI; RSI; RAX; RBX; RBP; RDX; R8; R9;
                       R10; R11; R12; R13; R14; R15] ,,
            MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                       memory :> bytes(word_sub stackpointer (word 32),32)] ,,
            MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`] THEN
  W64_GEN_TAC `w:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN X_GEN_TAC `stackpointer:int64` THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  ABBREV_TAC `k8 = k DIV 8` THEN

  (*** Degenerate k/8 = 0 case ***)

  ASM_CASES_TAC `k8 = 0` THENL
   [UNDISCH_THEN `k8 = 0` SUBST_ALL_TAC THEN
    SUBGOAL_THEN `val(word_ushr(word k:int64) 3) = 0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 3`];
      ALL_TAC] THEN
    X86_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--3) THEN
    UNDISCH_TAC `8 divides k` THEN
    ASM_REWRITE_TAC[DIVIDES_DIV_MULT; MULT_CLAUSES] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC] THEN

  (*** Restate things in terms of k' = k * k DIV 8 for naturalness ***)

  ABBREV_TAC `k' = 8 * k8` THEN
  ABBREV_TAC `a' = lowdigits a (2 * k')` THEN
  ABBREV_TAC `n' = lowdigits n k'` THEN

  ENSURES_SEQUENCE_TAC `pc + 0x16`
   `\s. read RSP s = word_add stackpointer (word 32) /\
        read RDI s = word k8 /\
        read RSI s = z /\
        read RDX s = m /\
        read RCX s = word w /\
        bignum_from_memory (z,2 * k') s = a' /\
        bignum_from_memory (m,k') s = n'` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--3) THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN
    ASM_REWRITE_TAC[word_ushr; NUM_REDUCE_CONV `2 EXP 3`] THEN
    MAP_EVERY EXPAND_TAC ["a'"; "n'"; "a"; "n"] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    MAP_EVERY EXPAND_TAC ["k'"; "k8"] THEN
    CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xb27`
   `\s. read RSP s = word_add stackpointer (word 32) /\
        ((n' * w + 1 == 0) (mod (2 EXP 64))
         ==> n' * bignum_from_memory (z,k') s + a' =
           2 EXP (64 * k') *
           (2 EXP (64 * k') * val (read RAX s) +
            bignum_from_memory (word_add z (word (8 * k')),k') s))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X86_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [] THEN
    UNDISCH_TAC `8 divides k` THEN
    ASM_REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIVIDES_DIV_MULT] THEN
    ASM_CASES_TAC `k':num = k` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `k':num = k` SUBST_ALL_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`lowdigits a (2 * k) = a'`; `lowdigits n k = n'`] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  SUBGOAL_THEN
   `nonoverlapping (z,8 * 2 * k') (stackpointer,32) /\
    nonoverlapping (z,8 * 2 * k') (word pc,0xb32) /\
    nonoverlapping (z,8 * 2 * k') (m:int64,8 * k') /\
    nonoverlapping (stackpointer,32) (m,8 * k')`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [MAP_EVERY EXPAND_TAC ["k'"; "k8"] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE
     [RIP; RDI; RSI; RAX; RBX; RBP; RDX;
      R8; R9; R10; R11; R12; R13; R14; R15] ,,
    MAYCHANGE [memory :> bytes (z,8 * 2 * k');
               memory :> bytes (stackpointer,32)] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF]` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    MAP_EVERY EXPAND_TAC ["k'"; "k8"] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `k:num`) o concl)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  MAP_EVERY SPEC_TAC
    [(`a':num`,`a:num`); (`n':num`,`n:num`); (`k':num`,`k:num`)] THEN
  REPEAT STRIP_TAC THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Get a basic bound on k and k8 from the nonoverlapping assumptions ***)

  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  MP_TAC(ASSUME
   `nonoverlapping_modulo (2 EXP 64)
     (val(z:int64),8 * 2 * k) (val(m:int64),8 * k)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `k8 < 2 EXP 58` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Lets us adjust stack provided we restore it to its initial value ***)

  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN

  (*** Main loop invariant for "outerloop" ***)

  ENSURES_WHILE_PUP_TAC `k8:num` `pc + 0x2f` `pc + 0xb1c`
   `\i s. (read RSP s = stackpointer /\
           read RDI s = m /\
           read RCX s = word w /\
           bignum_from_memory (m,k) s = n /\
           read (memory :> bytes64(word_add stackpointer (word 24))) s =
           word(64 * (k8 - 1)) /\
           read (memory :> bytes64(word_add stackpointer (word 16))) s =
           word(k8 - i) /\
           read RSI s = word_add z (word(8 * 8 * i)) /\
           bignum_from_memory(word_add z (word(8 * (k + 8 * i))),
                              2 * k - (k + 8 * i)) s =
           highdigits a (k + 8 * i) /\
           ((n * w + 1 == 0) (mod (2 EXP 64))
            ==> 2 EXP (64 * 8 * i) *
                (2 EXP (64 * k) * val(read(memory :> bytes64 stackpointer) s) +
                 bignum_from_memory(word_add z (word(8 * 8 * i)),k) s) =
               bignum_from_memory(z,8 * i) s * n + lowdigits a (k + 8 * i))) /\
          (read ZF s <=> i = k8)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:x86state`]
        HIGHDIGITS_BIGNUM_FROM_MEMORY) THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:x86state`]
        LOWDIGITS_BIGNUM_FROM_MEMORY) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `MIN (2 * k) k = k /\ 2 * k - k = k`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(ASSUME_TAC o SYM)) THEN
    X86_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; VAL_WORD_0; ADD_CLAUSES; EXP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; ARITH_RULE `2 * k - k = k`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    MATCH_MP_TAC(WORD_RULE
     `word_add x (word 64) = word_add y (word 64) ==> x = y`) THEN
    ASM_SIMP_TAC[GSYM WORD_ADD; ARITH_RULE
     `~(k = 0) ==> 64 * (k - 1) + 64 = 64 * k`] THEN
    REWRITE_TAC[WORD_ADD; WORD_RULE
     `word_add x y = word_sub x (word_neg y)`] THEN
    CONV_TAC(LAND_CONV(LAND_CONV WORD_REDUCE_CONV)) THEN CONV_TAC WORD_RULE;
    ALL_TAC; (*** This is the main loop invariant: save for later ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1];
    GHOST_INTRO_TAC `cout:int64`
     `read (memory :> bytes64 stackpointer)` THEN
    X86_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--3) THEN DISCH_TAC THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; GSYM MULT_2] THEN REWRITE_TAC[MULT_SYM]] THEN

  (*** Start on the main outer loop invariant, rebase at z + 64 * i = rsi ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * (k + 8 * i))) =
    word_add (word_add z (word(8 * 8 * i))) (word(8 * k))`] THEN
  REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * 8 * (i + 1))) =
    word_add (word_add z (word(8 * 8 * i))) (word(8 * 8))`] THEN
  ABBREV_TAC `z':int64 = word_add z (word (8 * 8 * i))` THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add z (word (8 * 8))) (word (8 * k)) =
    word_add z (word (8 * (k + 8)))`] THEN
  REWRITE_TAC[ARITH_RULE `2 * k - (k  + i) = k - i`] THEN

  GHOST_INTRO_TAC `cout:num`
   `\s. val(read (memory :> bytes64 stackpointer) s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory(z',k) s =
        lowdigits (bignum_from_memory(z',k+8) s) k`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    REWRITE_TAC[ARITH_RULE `MIN (k + 8) k = k`];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory (z,8 * (i + 1)) s =
        2 EXP (64 * 8 * i) * bignum_from_memory(z',8) s +
        bignum_from_memory(z,8 * i) s`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory (word_add z' (word (8 * k)),k - 8 * i) s =
        highdigits a (k + 8 * i) <=>
        highdigits (bignum_from_memory(z',k+8) s) k =
        lowdigits (highdigits a (k + 8 * i)) 8 /\
        bignum_from_memory
         (word_add z' (word (8 * (k + 8))),k - 8 * (i + 1)) s =
        highdigits a (k + 8 * (i + 1))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN
    REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; ADD_SUB2] THEN
    SUBGOAL_THEN
     `k - 8 * i = 8 + (k - 8 * (i + 1))`
    SUBST1_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
    MP_TAC(SPECL [`highdigits a (k + 8 * i)`; `8`]
     (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM th]) THEN
    SIMP_TAC[LEXICOGRAPHIC_EQ; BIGNUM_FROM_MEMORY_BOUND; LOWDIGITS_BOUND] THEN
    REWRITE_TAC[HIGHDIGITS_HIGHDIGITS] THEN
    REWRITE_TAC[ARITH_RULE `(k + 8 * i) + 8 = k + 8 * (i + 1)`] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_add z (word (8 * k))) (word (8 * 8)) =
      word_add z (word (8 * (k + 8)))`] THEN
    MATCH_ACCEPT_TAC CONJ_SYM;
    ALL_TAC] THEN

  GHOST_INTRO_TAC `z1:num` `bignum_from_memory(z',k+8)` THEN
  BIGNUM_TERMRANGE_TAC `k + 8` `z1:num` THEN
  GHOST_INTRO_TAC `q1:num` `bignum_from_memory(z,8 * i)` THEN
  BIGNUM_TERMRANGE_TAC `8 * i` `q1:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  ENSURES_SEQUENCE_TAC `pc + 0xb1c`
   `\s. read RSP s = stackpointer /\
        read RDI s = m /\
        read RCX s = word w /\
        bignum_from_memory (m,k) s = n /\
        read (memory :> bytes64 (word_add stackpointer (word 24))) s =
        word (64 * (k8 - 1)) /\
        read (memory :> bytes64 (word_add stackpointer (word 16))) s =
        word (k8 - (i + 1)) /\
        (read ZF s <=> i + 1 = k8) /\
        read RSI s = word_add z' (word (8 * 8)) /\
        bignum_from_memory (word_add z' (word (8 * (k + 8))),k - 8 * (i + 1))
        s =
        highdigits a (k + 8 * (i + 1)) /\
        bignum_from_memory (z,8 * i) s = q1 /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 8) *
             (2 EXP (64 * k) *
              val(read (memory :> bytes64 stackpointer) s) +
              bignum_from_memory(word_add z' (word(8 * 8)),k) s) =
             bignum_from_memory(z',8) s * n + 2 EXP (64 * k) * cout + z1)` THEN
  CONJ_TAC THENL
   [ALL_TAC;

    X86_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [] THEN
    DISCH_THEN(fun th ->
     REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th))) THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE
     `64 * 8 * (i + 1) = 64 * 8 * i + 64 * 8`] THEN
    ASM_REWRITE_TAC[GSYM MULT_ASSOC] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; EQ_ADD_LCANCEL] THEN
    MP_TAC(SPECL [`z1:num`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[ARITH_RULE
     `ee * e * c + ee * (e * h + l):num =
      (ee * (e * c + l)) + (ee * e) * h`] THEN
    REWRITE_TAC[GSYM EXP_ADD; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[lowdigits; highdigits; LEFT_ADD_DISTRIB; ADD_ASSOC] THEN
    REWRITE_TAC[ARITH_RULE `64 * 8 * i + 64 * k = 64 * k + 64 * 8 * i`] THEN
    SPEC_TAC(`64 * k + 64 * 8 * i`,`j:num`) THEN
    REWRITE_TAC[EXP_ADD; MOD_MULT_MOD] THEN ARITH_TAC] THEN

  (*** Now discard no-longer-relevant things outside the window ***)

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE
     [RIP; RSP; RDI; RSI; RAX; RBX; RBP; RDX;
      R8; R9; R10; R11; R12; R13; R14; R15] ,,
    MAYCHANGE [memory :> bytes(z',8 * (k + 8));
               memory :> bytes (stackpointer,32)] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF]` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `nonoverlapping (stackpointer,32) (z,8 * 8 * i) /\
    nonoverlapping (stackpointer,32) (word pc,0xb32) /\
    nonoverlapping (stackpointer,32) (m,8 * k) /\
    nonoverlapping (stackpointer,32)
     (word_add z' (word (8 * (k + 8))),8 * (k - 8 * (i + 1))) /\
    nonoverlapping (z':int64,8 * (k + 8)) (z,8 * 8 * i) /\
    nonoverlapping (z':int64,8 * (k + 8)) (word pc,0xb32) /\
    nonoverlapping (z':int64,8 * (k + 8)) (m,8 * k) /\
    nonoverlapping (z':int64,8 * (k + 8))
     (word_add z' (word (8 * (k + 8))),8 * (k - 8 * (i + 1)))`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "z'" THEN REPEAT CONJ_TAC THEN TRY NONOVERLAPPING_TAC THEN
    UNDISCH_TAC
     `nonoverlapping_modulo (2 EXP 64) (val(z:int64),8 * 2 * k)
                  (val(stackpointer:int64),32)` THEN
    GEN_REWRITE_TAC LAND_CONV [NONOVERLAPPING_MODULO_SYM] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
      NONOVERLAPPING_MODULO_SUBREGIONS) THEN
    REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL] THEN CONTAINED_TAC;
    STRIP_TAC] THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_FORGET_COMPONENTS_TAC
   [`memory :> bytes (z,8 * 8 * i)`;
    `memory :>
     bytes (word_add z' (word (8 * (k + 8))),8 * (k - 8 * (i + 1)))`] THEN

  SUBGOAL_THEN `nonoverlapping (stackpointer,32) (z':int64,8 * (k + 8))`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "z'" THEN
    UNDISCH_TAC
     `nonoverlapping_modulo (2 EXP 64) (val(z:int64),8 * 2 * k)
                  (val(stackpointer:int64),32)` THEN
    GEN_REWRITE_TAC LAND_CONV [NONOVERLAPPING_MODULO_SYM] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
      NONOVERLAPPING_MODULO_SUBREGIONS) THEN
    REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL] THEN CONTAINED_TAC;
    STRIP_TAC] THEN

  (*** Get the cout < 2 before we forget too much context ***)

  SUBGOAL_THEN `(n * w + 1 == 0) (mod (2 EXP 64)) ==> cout < 2`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `2 EXP (64 * 8 * i) * (2 EXP (64 * k) * cout + lowdigits z1 k) <
      2 EXP (64 * 8 * i) * 2 EXP (64 * k) * 2`
    MP_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC (ARITH_RULE
       `x < d * e /\ y < e * d ==> x + y < d * e * 2`) THEN
      ASM_SIMP_TAC[LT_MULT2] THEN REWRITE_TAC[GSYM EXP_ADD] THEN
      REWRITE_TAC[LOWDIGITS_BOUND; GSYM LEFT_ADD_DISTRIB];
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `d * (e * c + l):num < x ==> d * e * c < x`)) THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN

  (*** Now forget more things; back up a few steps and forget i as well ***)

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `z:int64`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `q1:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `r1:num`) o concl)) THEN

  ENSURES_SEQUENCE_TAC `pc + 0xb0e`
   `\s. read RSP s = stackpointer /\
        read RDI s = m /\
        read RCX s = word w /\
        bignum_from_memory (m,k) s = n /\
        read (memory :> bytes64 (word_add stackpointer (word 24))) s =
        word (64 * (k8 - 1)) /\
        read (memory :> bytes64 (word_add stackpointer (word 16))) s =
        word (k8 - i) /\
        read RSI s = z' /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 8) *
             (2 EXP (64 * k) * val(read RAX s) +
              bignum_from_memory(word_add z' (word(8 * 8)),k) s) =
              bignum_from_memory(z',8) s * n +
              2 EXP (64 * k) * cout + z1)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `caro:int64` `read RAX` THEN
    X86_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--3) THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k - (j + 1) = k - j - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= k - j <=> j < k`];
      VAL_INT64_TAC `k8 - i:num` THEN ASM_REWRITE_TAC[VAL_WORD_1] THEN
      UNDISCH_TAC `i:num < k8` THEN ARITH_TAC;
      CONV_TAC WORD_RULE]] THEN

  ABBREV_TAC `wouter:int64 = word (k8 - i)` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `i:num`) o concl)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  MAP_EVERY SPEC_TAC
    [(`z1:num`,`a:num`); (`z':int64`,`z:int64`)] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `8 <= k` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `8 * k8 = k`)) THEN UNDISCH_TAC `~(k8 = 0)` THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The initial Montgomery 8-block ***)

  ENSURES_SEQUENCE_TAC `pc + 0x555`
   `\s. read RSP s = stackpointer /\
        read RDI s = m /\
        read RCX s = word w /\
        bignum_from_memory(m,k) s = n /\
        read (memory :> bytes64(word_add stackpointer (word 24))) s =
        word (64 * (k8 - 1)) /\
        read (memory :> bytes64(word_add stackpointer (word 16))) s = wouter /\
        read RSI s = z /\
        read (memory :> bytes64 stackpointer) s = word cout /\
        bignum_from_memory(word_add z (word (8 * 8)),k) s =
        highdigits a 8 /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 8) *
             bignum_of_wordlist [read R8 s; read R9 s; read R10 s; read R11 s;
                            read R12 s; read R13 s; read R14 s; read R15 s] =
             bignum_from_memory(z,8) s * lowdigits n 8 + lowdigits a 8)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `highdigits (bignum_from_memory(z,k+8) s0) 8 = highdigits a 8`
    MP_TAC THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]; ALL_TAC] THEN
    REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; ADD_SUB] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[NUM_REDUCE_CONV `8 * 8`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(!i. i < 8
           ==> bigdigit (bignum_from_memory(z,k+8) s0) i = bigdigit a i) /\
      (!i. i < 8
           ==> bigdigit (bignum_from_memory(m,k) s0) i = bigdigit n i)`
    MP_TAC THENL [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    SUBGOAL_THEN `!i. i < 8 ==> i < k /\ i < k + 8` MP_TAC THENL
     [UNDISCH_TAC `8 <= k` THEN ARITH_TAC; SIMP_TAC[]] THEN
    DISCH_THEN(K ALL_TAC) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV(BINOP_CONV EXPAND_CASES_CONV)) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] THEN
    STRIP_TAC THEN
    X86_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--240) (1--240) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[RAND_CONV(TOP_DEPTH_CONV num_CONV) `lowdigits x 8`] THEN
    REWRITE_TAC[ADD1; LOWDIGITS_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP montgomery_lemma) THEN
    DISCH_THEN(fun ith ->
      EVERY_ASSUM(fun th ->
        try let th' = MATCH_MP ith th in
            FIRST_ASSUM(MP_TAC o MATCH_MP th')
        with Failure _ -> ALL_TAC)) THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
     (MP_TAC o MATCH_MP (MESON[REAL_ADD_LID]
        `n = 0 ==> !x:real. &n + x = x`))) THEN
    REPEAT(DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Shared tail to handle the final carry chaining in k8 = 1 too ***)

  GHOST_INTRO_TAC `q:num` `bignum_from_memory(z,8)` THEN
  BIGNUM_TERMRANGE_TAC `8` `q:num` THEN

  (*** Set up a version with the whole z buffer ***)

  ENSURES_SEQUENCE_TAC `pc + 0xad6`
   `\s. read RSP s = stackpointer /\
        read RSI s = z /\
        read RDI s = m /\
        read RCX s = word w /\
        bignum_from_memory(m,k) s = n /\
        read (memory :> bytes64 (word_add stackpointer (word 24))) s =
        word (64 * (k8 - 1)) /\
        read RAX s = word (64 * (k8 - 1)) /\
        read (memory :> bytes64 (word_add stackpointer (word 16))) s =
        wouter /\
        read (memory :> bytes64 stackpointer) s = word cout /\
        bignum_from_memory (word_add z (word (8 * k)),8) s =
        highdigits a k /\
        bignum_from_memory (z,8) s = q /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * k) *
             bignum_of_wordlist
             [read R8 s; read R9 s; read R10 s; read R11 s; read R12 s;
              read R13 s; read R14 s; read R15 s] +
             bignum_from_memory(z,k) s =
             q * n + lowdigits a k + q)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `g8:int64` `read R8` THEN
    GHOST_INTRO_TAC `g9:int64` `read R9` THEN
    GHOST_INTRO_TAC `g10:int64` `read R10` THEN
    GHOST_INTRO_TAC `g11:int64` `read R11` THEN
    GHOST_INTRO_TAC `g12:int64` `read R12` THEN
    GHOST_INTRO_TAC `g13:int64` `read R13` THEN
    GHOST_INTRO_TAC `g14:int64` `read R14` THEN
    GHOST_INTRO_TAC `g15:int64` `read R15` THEN
    SUBGOAL_THEN
     `word_add z (word(1 * val(word(64 * (k8 - 1)):int64) + 64)):int64 =
      word_add z (word(8 * k)) /\
      word_add z (word(1 * val(word(64 * (k8 - 1)):int64) + 72)):int64 =
      word_add z (word(8 * k + 8)) /\
      word_add z (word(1 * val(word(64 * (k8 - 1)):int64) + 80)):int64 =
      word_add z (word(8 * k + 16)) /\
      word_add z (word(1 * val(word(64 * (k8 - 1)):int64) + 88)):int64 =
      word_add z (word(8 * k + 24)) /\
      word_add z (word(1 * val(word(64 * (k8 - 1)):int64) + 96)):int64 =
      word_add z (word(8 * k + 32)) /\
      word_add z (word(1 * val(word(64 * (k8 - 1)):int64) + 104)):int64 =
      word_add z (word(8 * k + 40)) /\
      word_add z (word(1 * val(word(64 * (k8 - 1)):int64) + 112)):int64 =
      word_add z (word(8 * k + 48)) /\
      word_add z (word(1 * val(word(64 * (k8 - 1)):int64) + 120)):int64 =
      word_add z (word(8 * k + 56))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LEFT_SUB_DISTRIB; WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `64 * 1 <= 64 * k8 <=> ~(k8 = 0)`] THEN
      SUBST1_TAC(SYM(ASSUME `8 * k8 = k`)) THEN CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `!j. j < 8
          ==> bigdigit (bignum_from_memory(word_add z (word (8 * k)),8) s0) j =
              bigdigit a (k + j)`
    MP_TAC THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BIGDIGIT_HIGHDIGITS];
      SIMP_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY]] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND; GSYM WORD_ADD_ASSOC;
      GSYM WORD_ADD] THEN
    REWRITE_TAC[] THEN CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES]) THEN

    X86_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (3--10) (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
      ASSUME_TAC th) THEN

    ABBREV_TAC `bout <=> ~(word cout:int64 = word 0)` THEN
    SUBGOAL_THEN `cout = bitval bout` SUBST_ALL_TAC THENL
     [EXPAND_TAC "bout" THEN UNDISCH_TAC `cout < 2` THEN
      SPEC_TAC(`cout:num`,`c:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES];
      ALL_TAC] THEN

    MP_TAC(SPECL [`a:num`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (ARITH_RULE
       `z = q * n + a + q
        ==> x + q = z + b + h
            ==> x = q * n + b + h + a`)) THEN

    SUBST1_TAC(SYM(ASSUME `read (memory :> bytes (z,8 * 8)) s12 = q`)) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_SPLIT] THEN
    ONCE_REWRITE_TAC[MESON[ADD_SYM]
     `bignum_from_memory (z,8 + k) = bignum_from_memory (z,k + 8)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
    GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `a + b + c:num = (a + c) + b`] THEN
    REWRITE_TAC[EQ_ADD_RCANCEL; ADD_ASSOC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a * b * c:num = b * a * c`] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; VAL_WORD_BITVAL] THEN
    AP_TERM_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN

    REPLICATE_TAC 8
     (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP]) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[HIGHDIGITS_ZERO] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN

    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC] THEN

  (*** The semi-degenerate case where we skip the inner loop ***)

  ASM_CASES_TAC `k8 = 1` THENL
   [UNDISCH_THEN `k8 = 1` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `8 * 1 = k ==> k = 8`)) THEN
    X86_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--5) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN

  (*** Setup of the inner loop "innerloop" ***)

  ENSURES_WHILE_PAUP_TAC `1` `k8:num` `pc + 0x56b` `pc + 0xac8`
   `\i s. (read RSP s = stackpointer /\
           read RSI s = z /\
           read RBP s = word_sub (word_add z (word(64 * i))) (word 64) /\
           read RDI s = word_sub (word_add m (word(64 * i))) (word 64) /\
           read RCX s = word w /\
           bignum_from_memory(m,k) s = n /\
           read (memory :> bytes64 (word_add stackpointer (word 24))) s =
           word (64 * (k8 - 1)) /\
           read (memory :> bytes64 (word_add stackpointer (word 16))) s =
           wouter /\
           read (memory :> bytes64 stackpointer) s = word cout /\
           bignum_from_memory (z,8) s = q /\
           read (memory :> bytes64 (word_add stackpointer (word 8))) s =
           word (64 * (k8 - i)) /\
           bignum_from_memory (word_add z (word (8 * 8 * i)),
                               (k + 8) - 8 * i) s =
           highdigits a (8 * i) /\
           ((n * w + 1 == 0) (mod (2 EXP 64))
            ==> 2 EXP (64 * 8 * i) *
                bignum_of_wordlist
                [read R8 s; read R9 s; read R10 s; read R11 s; read R12 s;
                 read R13 s; read R14 s; read R15 s] +
                bignum_from_memory(z,8 * i) s =
                q * lowdigits n (8 * i) + lowdigits a (8 * i) + q)) /\
          (read ZF s <=> i = k8)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0) /\ ~(k = 1)`];

    SUBGOAL_THEN `~(val(word (64 * (k8 - 1)):int64) = 0)` ASSUME_TAC THENL
     [VAL_INT64_TAC `64 * (k8 - 1)` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`~(k8 = 0)`; `~(k8 = 1)`] THEN ARITH_TAC;
      ALL_TAC] THEN
    X86_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--5) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_SUB] THEN
    ASM_REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    CONV_TAC WORD_RULE;

    ALL_TAC; (*** The main loop invariant preservation ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1];

    X86_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--3) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB; WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `64 * 1 <= 64 * k8 <=> ~(k8 = 0)`] THEN
    SUBST1_TAC(SYM(ASSUME `8 * k8 = k`)) THEN CONV_TAC WORD_RULE] THEN

  (*** launch into the inner loop, but for simplicity localize our window ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * i < k` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i:num < k8`; `8 * k8 = k`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(k + 8) - 8 * (i + 1) = k - 8 * i`] THEN

  ABBREV_TAC `z':int64 = word_add z (word (64 * i))` THEN
  ABBREV_TAC `m':int64 = word_add m (word (64 * i))` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `8 * i + 8 = 8 * (i + 1)`] THEN
  ASM_REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * 8 * i)) = word_add z (word(64 * i))`] THEN

  SUBGOAL_THEN
   `ALL (nonoverlapping (stackpointer:int64,32))
        [(z,64); (z,8 * 8 * i); (m',64);
         (word_add z (word (64 * (i + 1))),8 * (k - 8 * i))] /\
    ALL (nonoverlapping (z':int64,64))
        [(z,64); (z,8 * 8 * i); (m,8 * k); (stackpointer,32); (word pc,0xb32);
         (m',64); (word_add z (word (64 * (i + 1))),8 * (k - 8 * i))]`
  MP_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THENL
   [MAP_EVERY EXPAND_TAC ["z'"; "m'"] THEN
    REPEAT CONJ_TAC THEN TRY NONOVERLAPPING_TAC THEN
    ONCE_REWRITE_TAC[WORD_RULE
     `word_add z (word (8 * 8 * (i + 1))) =
      word_add (word_add z (word(64 * i))) (word 64)`] THEN
    NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE
     [RIP; RDI; RSI; RAX; RBX; RBP; RDX;
      R8; R9; R10; R11; R12; R13; R14; R15] ,,
    MAYCHANGE [memory :> bytes (z',8 * 8);
               memory :> bytes (stackpointer,32)] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF]` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  GHOST_INTRO_TAC `g8:int64` `read R8` THEN
  GHOST_INTRO_TAC `g9:int64` `read R9` THEN
  GHOST_INTRO_TAC `g10:int64` `read R10` THEN
  GHOST_INTRO_TAC `g11:int64` `read R11` THEN
  GHOST_INTRO_TAC `g12:int64` `read R12` THEN
  GHOST_INTRO_TAC `g13:int64` `read R13` THEN
  GHOST_INTRO_TAC `g14:int64` `read R14` THEN
  GHOST_INTRO_TAC `g15:int64` `read R15` THEN
  GHOST_INTRO_TAC `zlo:num` `bignum_from_memory (z,8 * i)` THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  ABBREV_TAC `z'':int64 = word_add z (word (64 * (i + 1)))` THEN

  SUBGOAL_THEN
   `bignum_from_memory(z'',k - 8 * i) s0 = highdigits a (8 * (i + 1))`
  MP_TAC THENL
   [EXPAND_TAC "z''" THEN REWRITE_TAC[WORD_RULE
     `word_add z (word (64 * (i + 1))) =
      word_add (word_add z (word(8 * 8 * i))) (word(8 * 8))`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 8 * i = 64 * i`] THEN
    SUBGOAL_THEN `k - 8 * i = ((k + 8) - 8 * i) - 8` SUBST1_TAC THENL
     [UNDISCH_TAC `8 * i < k` THEN ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV]] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_TAC] THEN

  SUBGOAL_THEN
   `(!j. j < 8
         ==> bigdigit (bignum_from_memory(z,8) s0) j = bigdigit q j) /\
    (!j. j < 8
         ==> bigdigit
              (bignum_from_memory(z',((k + 8) - 8 * i)) s0) j =
             bigdigit a (8 * i + j)) /\
    (!j. j < 8
         ==> bigdigit (highdigits (bignum_from_memory(m,k) s0) (8 * i)) j =
             bigdigit n (8 * i + j))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGDIGIT_HIGHDIGITS];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [HIGHDIGITS_BIGNUM_FROM_MEMORY; BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
  SUBGOAL_THEN `!j. j < 8 ==> j < (k + 8) - 8 * i /\ j < k - 8 * i`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i:num < k8`; `8 * k8 = k`] THEN ARITH_TAC;
    SIMP_TAC[]] THEN
  DISCH_THEN(K ALL_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [BIGDIGIT_HIGHDIGITS; VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 8 * i = 64 * i`] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ADD_CLAUSES; WORD_ADD_0] THEN
  STRIP_TAC THEN

  X86_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 64)) (word 64) = x`]) THEN

  X86_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (3--242) (3--243) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word_add z (word (64 * (i + 1))):int64 = z''`)) THEN
    SUBST1_TAC(SYM(ASSUME `word_add z (word (64 * i)):int64 = z'`)) THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word_add m (word (64 * i)):int64 = m'`)) THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word(64 * x)) (word 64) =
      word_mul (word 64) (word_sub (word x) (word 1))`] THEN
    REWRITE_TAC[WORD_MUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `k - (j + 1) = k - j - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k - j <=> j < k`];
    DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    VAL_INT64_TAC `64 * (k8 - (i + 1))` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`i:num < k8`; `8 * k8 = k`] THEN ARITH_TAC] THEN

  DISCH_THEN(fun th ->
   REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
   ASSUME_TAC th) THEN
  SUBST1_TAC(ARITH_RULE `64 * i = 8 * 8 * i`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_RULE `8 * (i + 1) = 8 * i + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [ADD_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o TOP_DEPTH_CONV)
   [ADD_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV
   [ARITH_RULE `(q * (x1 + l1) + (x2 + l2)) + q =
                (x1 * q + x2) + (q * l1 + l2 + q)`] THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB;
              EXP_ADD; GSYM MULT_ASSOC] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN AP_TERM_TAC THEN
  UNDISCH_TAC `read (memory :> bytes (z,8 * 8)) s243 = q` THEN
  CONV_TAC(LAND_CONV(LAND_CONV BIGNUM_EXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[bignum_of_wordlist] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN

  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REAL_ARITH_TAC);;

(*** The above doesn't quite match what the heuristics in the automated
 *** X86_PROMOTE_RETURN_STACK_TAC expects, partly because the core statement
 *** has a negative stack offset and partly because the subsequent stack
 *** adjustment isn't just a single subtract after the initial pushes. So
 *** for now we just duplicate the basic argument in X86_ADD_RETURN_STACK_TAC
 *** with manual tweaks.
 ***)

let BIGNUM_EMONTREDC_8N_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc stackpointer returnaddress.
      nonoverlapping (z,8 * 2 * val k) (word_sub stackpointer (word 80),88) /\
      ALLPAIRS nonoverlapping
         [(z,8 * 2 * val k); (word_sub stackpointer (word 80),80)]
         [(word pc,LENGTH bignum_emontredc_8n_tmc); (m,8 * val k)] /\
      8 divides val k
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_emontredc_8n_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [k; z; m; w] s /\
                bignum_from_memory (z,2 * val k) s = a /\
                bignum_from_memory (m,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                ((n * val w + 1 == 0) (mod (2 EXP 64))
                 ==> n * bignum_from_memory (z,val k) s + a =
                     2 EXP (64 * val k) *
                     (2 EXP (64 * val k) * val(C_RETURN s) +
                      bignum_from_memory
                        (word_add z (word(8 * val k)),val k) s)))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                       memory :> bytes(word_sub stackpointer (word 80),80)])`,
  let BIGNUM_EMONTREDC_8N_EXEC = X86_MK_EXEC_RULE bignum_emontredc_8n_tmc in
  REWRITE_TAC[fst BIGNUM_EMONTREDC_8N_EXEC] THEN
  REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MP_TAC (X86_CORE_PROMOTE BIGNUM_EMONTREDC_8N_CORRECT) THEN
  REPLICATE_TAC 7 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC 48 THEN MP_TAC th) THEN
  MATCH_MP_TAC MONO_FORALL THEN WORD_FORALL_OFFSET_TAC 32 THEN
  GEN_TAC THEN DISCH_THEN(fun th -> GEN_TAC THEN MP_TAC th) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(fun th ->
    REPEAT GEN_TAC THEN
    TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MAP_EVERY (fun c -> ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c)
              (dest_list `[RBX; RBP; R12; R13; R14; R15]`) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--6) THEN
    MP_TAC th) THEN
  X86_BIGSTEP_TAC BIGNUM_EMONTREDC_8N_EXEC "s7" THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  X86_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (8--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let BIGNUM_EMONTREDC_8N_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc stackpointer returnaddress.
      nonoverlapping (z,8 * 2 * val k) (word_sub stackpointer (word 80),88) /\
      ALLPAIRS nonoverlapping
         [(z,8 * 2 * val k); (word_sub stackpointer (word 80),80)]
         [(word pc,LENGTH bignum_emontredc_8n_mc); (m,8 * val k)] /\
      8 divides val k
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_emontredc_8n_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [k; z; m; w] s /\
                bignum_from_memory (z,2 * val k) s = a /\
                bignum_from_memory (m,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                ((n * val w + 1 == 0) (mod (2 EXP 64))
                 ==> n * bignum_from_memory (z,val k) s + a =
                     2 EXP (64 * val k) *
                     (2 EXP (64 * val k) * val(C_RETURN s) +
                      bignum_from_memory
                        (word_add z (word(8 * val k)),val k) s)))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                       memory :> bytes(word_sub stackpointer (word 80),80)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_EMONTREDC_8N_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_emontredc_8n_windows_mc = define_from_elf
   "bignum_emontredc_8n_windows_mc" "x86/fastmul/bignum_emontredc_8n.obj";;

let bignum_emontredc_8n_windows_tmc = define_trimmed "bignum_emontredc_8n_windows_tmc" bignum_emontredc_8n_windows_mc;;

(*** Likewise, a manual tweak of WINDOWS_X86_WRAP_STACK_TAC
 *** to get the Windows ABI version
 ***)

let BIGNUM_EMONTREDC_8N_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc stackpointer returnaddress.
      nonoverlapping (z,8 * 2 * val k) (word_sub stackpointer (word 96),104) /\
      ALLPAIRS nonoverlapping
         [(z,8 * 2 * val k); (word_sub stackpointer (word 96),96)]
         [(word pc,LENGTH bignum_emontredc_8n_windows_tmc); (m,8 * val k)] /\
      8 divides val k
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_emontredc_8n_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [k; z; m; w] s /\
                bignum_from_memory (z,2 * val k) s = a /\
                bignum_from_memory (m,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                ((n * val w + 1 == 0) (mod (2 EXP 64))
                 ==> n * bignum_from_memory (z,val k) s + a =
                     2 EXP (64 * val k) *
                     (2 EXP (64 * val k) * val(WINDOWS_C_RETURN s) +
                      bignum_from_memory
                        (word_add z (word(8 * val k)),val k) s)))
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                       memory :> bytes(word_sub stackpointer (word 96),96)])`,
  let BIGNUM_EMONTREDC_8N_EXEC =
    X86_MK_EXEC_RULE bignum_emontredc_8n_windows_tmc
  and pcofflemma = MESON[]
    `!n:num. (!x. P(x + n) ==> Q x) ==> (!x. P x) ==> (!x. Q x)`
  and subimpth =
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE [LENGTH]
        (MATCH_MP bytes_loaded_of_append3
          (TRANS bignum_emontredc_8n_windows_tmc (N_SUBLIST_CONV
             (SPEC_ALL (X86_TRIM_EXEC_RULE bignum_emontredc_8n_tmc)) 14
             (rhs(concl bignum_emontredc_8n_windows_tmc)))))) in
  REWRITE_TAC[fst BIGNUM_EMONTREDC_8N_EXEC] THEN
  REWRITE_TAC [WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MP_TAC BIGNUM_EMONTREDC_8N_CORRECT THEN
  REPLICATE_TAC 6 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC pcofflemma THEN EXISTS_TAC `0xe` THEN
  X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[ARITH_RULE `(pc + 14) + n = pc + n + 14`] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC 64 THEN MP_TAC th) THEN
  MATCH_MP_TAC MONO_FORALL THEN WORD_FORALL_OFFSET_TAC 32 THEN
  GEN_TAC THEN DISCH_THEN(fun th -> GEN_TAC THEN MP_TAC th) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN] THEN
  DISCH_THEN(fun th ->
    REPEAT GEN_TAC THEN
    TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MAP_EVERY (fun c -> ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c)
              (dest_list `[RDI; RSI; RBX; RBP; R12; R13; R14; R15]`) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--12) THEN
    MP_TAC th) THEN
  X86_BIGSTEP_TAC BIGNUM_EMONTREDC_8N_EXEC "s13" THENL
   [MATCH_MP_TAC subimpth THEN FIRST_X_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  X86_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (14--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let BIGNUM_EMONTREDC_8N_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc stackpointer returnaddress.
      nonoverlapping (z,8 * 2 * val k) (word_sub stackpointer (word 96),104) /\
      ALLPAIRS nonoverlapping
         [(z,8 * 2 * val k); (word_sub stackpointer (word 96),96)]
         [(word pc,LENGTH bignum_emontredc_8n_windows_mc); (m,8 * val k)] /\
      8 divides val k
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_emontredc_8n_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [k; z; m; w] s /\
                bignum_from_memory (z,2 * val k) s = a /\
                bignum_from_memory (m,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                ((n * val w + 1 == 0) (mod (2 EXP 64))
                 ==> n * bignum_from_memory (z,val k) s + a =
                     2 EXP (64 * val k) *
                     (2 EXP (64 * val k) * val(WINDOWS_C_RETURN s) +
                      bignum_from_memory
                        (word_add z (word(8 * val k)),val k) s)))
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                       memory :> bytes(word_sub stackpointer (word 96),96)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_EMONTREDC_8N_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

