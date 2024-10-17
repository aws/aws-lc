.text
.file 1 "inserted_by_delocate.c"
.loc 1 1 0
BORINGSSL_bcm_text_start:
	.text

        # PIC function call
.L0:

        leaq    .L0(%rip), %rax
# WAS movabsq $_GLOBAL_OFFSET_TABLE_-.L0, %rcx
	movq	.Lboringssl_got_delta(%rip), %rcx
	addq $.Lboringssl_got_delta-.L0, %rcx
        addq    %rax, %rcx
# WAS movabsq $_Z1gv@GOTOFF, %rax
	movq .Lboringssl_gotoff__Z1gv(%rip), %rax
        addq    %rcx, %rax
        jmpq    *%rax


        # PIC global variable load.
.L0$pb:

        leaq    .L0$pb(%rip), %rax
# WAS movabsq $_GLOBAL_OFFSET_TABLE_-.L0$pb, %rcx
	movq	.Lboringssl_got_delta(%rip), %rcx
	addq $.Lboringssl_got_delta-.L0$pb, %rcx
        addq    %rax, %rcx
# WAS movabsq $h@GOT, %rax
	movq .Lboringssl_got_h(%rip), %rax
        movq    (%rcx,%rax), %rax
        movl    (%rax), %eax
        retq

        # Non-PIC function call. Not yet handled. Doesn't appear to be used in
        # configurations that we care about.
        #
        # movabsq $_Z1gv, %rax
        # jmpq    *%rax

.text
.loc 1 2 0
BORINGSSL_bcm_text_end:
.type OPENSSL_ia32cap_get, @function
.globl OPENSSL_ia32cap_get
.LOPENSSL_ia32cap_get_local_target:
OPENSSL_ia32cap_get:
	leaq OPENSSL_ia32cap_P(%rip), %rax
	ret
.Lboringssl_got_delta:
	.quad _GLOBAL_OFFSET_TABLE_-.Lboringssl_got_delta
.Lboringssl_got_h:
	.quad h@GOT
.Lboringssl_gotoff__Z1gv:
	.quad _Z1gv@GOTOFF
