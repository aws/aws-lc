  .intel_syntax noprefix
  .text

  mov rcx, [rax]
  mov rdx, [rbx]
  mov [rbx], rcx
  mov [rax], rdx
