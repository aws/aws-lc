  .intel_syntax noprefix
  .text

  cmp rbx, rcx
  ja BB2
  mov rax, rcx
  ret
BB2:
  mov rax, rbx
  ret
