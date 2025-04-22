  .intel_syntax noprefix
  .text

mov rdi, [rax]
mov rsi, [rax + 8]
add rdi, 1
imul rsi, rdi
mov [rbx], rsi
