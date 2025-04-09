  .intel_syntax noprefix
  .text

mov r8, [rax]
mov r9, [rax + 8]
imul r8, r9
add r8, r9
mov [rbx], r8
