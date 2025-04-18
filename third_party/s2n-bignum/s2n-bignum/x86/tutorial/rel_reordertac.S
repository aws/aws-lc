  .intel_syntax noprefix
  .text

mov RDI, [RAX]
add RDI, 1
mov [RBX], RDI
mov RDI, [RAX + 8]
add RDI, 2
mov [RBX + 8], RDI
