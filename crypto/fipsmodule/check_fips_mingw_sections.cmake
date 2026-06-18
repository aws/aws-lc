# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Verifies that the partial-linked FIPS module object (bcm.o) does not contain
# any code or read-only data in sections that would fall outside the
# [BORINGSSL_bcm_text_start, BORINGSSL_bcm_text_end] (and rodata) integrity
# markers in the final DLL.
#
# Background: at -O2+ GCC partitions functions into hot/cold paths and moves
# cold code into .text.unlikely (and constructors/destructors into
# .text.startup/.text.exit). On ELF the FIPS linker script (gcc_fips_shared.lds)
# gathers these back between the markers and /DISCARD/s stray sections. The
# PE/COFF MinGW path has no such net: it partial-links with a plain `ld -r` and
# relies on GCC not emitting split sections (see -fno-reorder-functions /
# -fno-reorder-blocks-and-partition in the top-level CMakeLists.txt). If a split
# section ever reappears, the module would still pass its self-test (injection
# and the runtime check measure the same window) but would silently leave that
# code/data outside the integrity check. This guard turns that silent gap into a
# hard build failure.
#
# Required arguments (passed via -D):
#   OBJDUMP     - path to a binutils/llvm objdump for the target
#   BCM_OBJECT  - path to the partial-linked module object to inspect

if(NOT OBJDUMP)
  message(FATAL_ERROR "FIPS MinGW section check: OBJDUMP not provided")
endif()
if(NOT BCM_OBJECT)
  message(FATAL_ERROR "FIPS MinGW section check: BCM_OBJECT not provided")
endif()

execute_process(
  COMMAND "${OBJDUMP}" -h "${BCM_OBJECT}"
  OUTPUT_VARIABLE objdump_output
  ERROR_VARIABLE objdump_error
  RESULT_VARIABLE objdump_result
)
if(NOT objdump_result EQUAL 0)
  message(FATAL_ERROR
    "FIPS MinGW section check: failed to run '${OBJDUMP} -h ${BCM_OBJECT}'\n${objdump_error}")
endif()

# Extract section names (the second whitespace-delimited column of `objdump -h`)
# and flag any that indicate split-out module code or data. Dollar-suffixed
# grouped sections such as .rdata$zzz are benign compiler metadata that the
# linker collates into .rdata, so only the dot-form splits are forbidden.
string(REPLACE "\n" ";" objdump_lines "${objdump_output}")
set(forbidden_sections "")
foreach(line IN LISTS objdump_lines)
  string(REGEX REPLACE "^[ \t]+" "" line "${line}")
  string(REGEX REPLACE "[ \t]+" ";" fields "${line}")
  list(LENGTH fields field_count)
  if(field_count GREATER 1)
    list(GET fields 1 section_name)
    if(section_name MATCHES "^\\.text\\." OR section_name MATCHES "^\\.rdata\\.")
      list(APPEND forbidden_sections "${section_name}")
    endif()
  endif()
endforeach()

if(forbidden_sections)
  list(REMOVE_DUPLICATES forbidden_sections)
  string(REPLACE ";" ", " forbidden_pretty "${forbidden_sections}")
  message(FATAL_ERROR
    "FIPS integrity check would be incomplete: '${BCM_OBJECT}' contains "
    "split-out section(s) outside the integrity markers: ${forbidden_pretty}.\n"
    "All module code must live in a single contiguous .text (and rodata in "
    ".rdata) bracketed by BORINGSSL_bcm_text_start/end. Ensure the module is "
    "built with -fno-reorder-functions -fno-reorder-blocks-and-partition "
    "(and -fno-function-sections -fno-data-sections); see the FIPS_SHARED "
    "MinGW blocks in the top-level CMakeLists.txt.")
endif()

message(STATUS "FIPS MinGW section check passed for ${BCM_OBJECT}")
