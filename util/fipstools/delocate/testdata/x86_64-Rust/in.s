	.text
	.file 1 "bcm.c"
	.globl c_func
	.type c_func, @function
c_func:
	.loc 1 2 0
	call bcm_rust_func@PLT
	ret
