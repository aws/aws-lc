  .intel_syntax noprefix
  .text

mov R8, [RAX]
mov R9, [RAX + 8]
add R8, 1
add R9, 2
mov [RBX], R8
mov [RBX + 8], R9
