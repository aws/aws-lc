.text
.file 1 "inserted_by_delocate.c"
.loc 1 1 0
BORINGSSL_bcm_text_start:
	.text
.Lfoo_local_target:
foo:
.LCF0:

0:

999:
	addis 2, 12, .LBORINGSSL_external_toc-999b@ha
	addi 2, 2, .LBORINGSSL_external_toc-999b@l
	ld 12, 0(2)
	add 2, 2, 12
# WAS addi 2,2,.TOC.-.LCF0@l
	.localentry foo,.-foo
.Lfoo_local_entry:
.LVL0:

	bl
.text
.loc 1 2 0
BORINGSSL_bcm_text_end:
.LBORINGSSL_external_toc:
.quad .TOC.-.LBORINGSSL_external_toc
