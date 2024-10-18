.text
.file 1 "inserted_by_delocate.c"
.loc 1 1 0
BORINGSSL_bcm_text_start:
	.text
.Lfoo_local_target:
foo:
# WAS addis 22,2,bar@toc@ha
# WAS ld 0,bar@toc@l(22)
	addi 1, 1, -288
	mflr 0
	std 0, -8(1)
	std 3, -16(1)
	bl .Lbcm_loadtoc_bar
	std 3, -24(1)
	ld 3, -8(1)
	mtlr 3
	ld 0, -24(1)
	ld 3, -16(1)
	addi 1, 1, 288
	addi 1, 1, -288
	std 3, -8(1)
	mr 3, 0
	ld 0, 0(3)
	ld 3, -8(1)
	addi 1, 1, 288
.text
.loc 1 2 0
BORINGSSL_bcm_text_end:
.type bcm_loadtoc_bar, @function
bcm_loadtoc_bar:
.Lbcm_loadtoc_bar:
	addis 3, 2, bar@toc@ha
	addi 3, 3, bar@toc@l
	blr
.LBORINGSSL_external_toc:
.quad .TOC.-.LBORINGSSL_external_toc
