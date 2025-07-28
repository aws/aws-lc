	.type foo, @function
	.globl foo
foo:
	movq $0, %rax
	ret

	.type x25519_foo, @function
	.globl x25519_foo
x25519_foo:
	movq $0, %rax
	ret

	.type ROL64, @function
	.globl ROL64
ROL64:
	movq $0, %rax
	ret

bar:
	# References to globals must be rewritten to their local targets.
	call foo
	jmp foo
	jbe foo
	jne foo

	# References potentially matching arm registers e.g. 'x[0-9][0-9]' should be
	# matched as global symbols and rewritten to the corresponding local target.
	call x25519_foo

	# Refernces potentially matching arm instructions e.g. arm rol, and label ROL64
	callq ROL64

	# Jumps to PLT symbols are rewritten through redirectors.
	call memcpy@PLT
	jmp memcpy@PLT
	jbe memcpy@PLT

	# Jumps to local PLT symbols use their local targets.
	call foo@PLT
	jmp foo@PLT
	jbe foo@PLT

	# Synthesized symbols are treated as local ones.
	call OPENSSL_ia32cap_get@PLT

	# References to local labels are left as-is in the first file.
.Llocal_label:
	jbe .Llocal_label
	leaq .Llocal_label+2048(%rip), %r14
	leaq .Llocal_label+2048+1024(%rip), %r14

	.section .rodata
.L1:
	.quad 42
.L2:
	.quad .L2-.L1
	.uleb128 .L2-.L1
	.sleb128 .L2-.L1

	# Local labels and their jumps are left alone.
	.text
	jmp 1f
1:
	jmp 1b
