  .intel_syntax noprefix
  .text

  mov rcx, [rax]
  mov rdx, [rax+8]
  mov rsi, [rbx]
  mov rdi, [rbx+8]
  cmp rcx, rsi
  jne bb_false
  cmp rdx, rdi
  jne bb_false
  mov rax, 1
  ret
bb_false:
  mov rax, 0
  ret
