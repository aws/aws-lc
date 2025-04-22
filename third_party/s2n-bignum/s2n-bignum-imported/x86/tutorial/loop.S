  .intel_syntax noprefix
  .text

  mov rbx, 0
  mov rax, 0

loop:
  add rbx, 1
  add rax, 2
  cmp rbx, 10
  jne loop

  ret
