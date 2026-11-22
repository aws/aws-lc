/* Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC */

/* Partial-link script for the crate's ELF fold (cmake/cargo.cmake). rustc
 * gives every function and constant a section of its own. This merges them
 * into .text and .rodata, as bcm.c's object has them, so that shared FIPS
 * builds' module script (crypto/fipsmodule/fips_shared.lds), which discards
 * .text.*, takes them into the module. Other sections keep their names. */
SECTIONS
{
  .text : { *(.text .text.*) }
  .rodata : { *(.rodata .rodata.*) }
}
