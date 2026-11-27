/* Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC */

/* Partial-link script for bcm-rust.o where it is a FIPS module, in ELF FIPS
 * builds (cmake/cargo.cmake). rustc gives every function and constant a
 * section of its own, and the consumer's linker could separate or reorder
 * those. This puts all of them in one .text section, with the module region
 * from TEXT_START to TEXT_END and the expected hash after it (src/fips.rs).
 * inject_hash -rust reads the two symbols. Sections not named here, such as
 * .data, .init_array and .eh_frame, stay outside the region (src/fips.rs).
 * Static FIPS builds don't use it: delocate writes the module there. */
SECTIONS
{
  .text : {
    BORINGSSL_bcm_rust_text_start = .;
    *(.bcm_rust_text_start)
    *(.text .text.* .rodata .rodata.*)
    BORINGSSL_bcm_rust_text_end = .;
    *(.bcm_rust_text_end)
    *(.bcm_rust_text_hash)
  }
}
