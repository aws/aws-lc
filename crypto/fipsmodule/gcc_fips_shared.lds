SECTIONS
{
  .text : {
    BORINGSSL_bcm_text_start = .;
    *(.text)
    /* gcc puts some code in sections named ".text.unlikely", ".text.exit" and ".text.startup". */
    *(.text.unlikely)
    *(.text.exit)
    *(.text.startup)
    *(.text.exit.*)
    *(.text.startup.*)
    *(.text.unlikely.*)
    BORINGSSL_bcm_text_end = .;
  }
  .rodata : {
    BORINGSSL_bcm_rodata_start = .;
    *(.rodata)
    *(.rodata.*)
    BORINGSSL_bcm_rodata_end = .;
  }

  .init_array : {
    *(.init_array)
    *(.init_array.*)
  }
  .fini_array : {
    *(.fini_array)
    *(.fini_array.*)
  }

  /DISCARD/ : {
    /* These sections shouldn't exist. In order to catch any slip-ups, direct
     * the linker to discard them. */
    *(.rela.dyn)
    *(.data)
    *(.rel.ro)
    /* Don't discard text.* here since we explicitly include what we want above */
    *(.data.*)
  }
}
