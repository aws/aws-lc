# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# MinGW emits external address cells in grouped .rdata$* sections. They are part
# of the FIPS module's read-only data, so merge them into .rdata before the final
# DLL link. The end marker is compiled into .rdata$zzzz, so it remains after the
# merged grouped sections.

foreach(required_var OBJDUMP OBJCOPY LINKER INPUT_OBJECT OUTPUT_OBJECT)
  if(NOT DEFINED ${required_var} OR "${${required_var}}" STREQUAL "")
    message(FATAL_ERROR
      "FIPS MinGW rodata merge: ${required_var} not provided")
  endif()
endforeach()

execute_process(
  COMMAND "${OBJDUMP}" -h "${INPUT_OBJECT}"
  OUTPUT_VARIABLE objdump_output
  ERROR_VARIABLE objdump_error
  RESULT_VARIABLE objdump_result
)
if(NOT objdump_result EQUAL 0)
  message(FATAL_ERROR
    "FIPS MinGW rodata merge: failed to run '${OBJDUMP} -h ${INPUT_OBJECT}'\n${objdump_error}")
endif()

string(REPLACE "\n" ";" objdump_lines "${objdump_output}")
set(objcopy_args "")
foreach(line IN LISTS objdump_lines)
  string(REGEX REPLACE "^[ \t]+" "" line "${line}")
  string(REGEX REPLACE "[ \t]+" ";" fields "${line}")
  list(LENGTH fields field_count)
  if(field_count GREATER 1)
    list(GET fields 1 section_name)
    if(section_name MATCHES "^\\.rdata\\$")
      list(APPEND objcopy_args "--rename-section" "${section_name}=.rdata")
    endif()
  endif()
endforeach()

if(NOT objcopy_args)
  execute_process(
    COMMAND "${CMAKE_COMMAND}" -E copy "${INPUT_OBJECT}" "${OUTPUT_OBJECT}"
    ERROR_VARIABLE copy_error
    RESULT_VARIABLE copy_result
  )
  if(NOT copy_result EQUAL 0)
    message(FATAL_ERROR
      "FIPS MinGW rodata merge: failed to copy '${INPUT_OBJECT}' to '${OUTPUT_OBJECT}'\n${copy_error}")
  endif()
  return()
endif()

set(renamed_object "${OUTPUT_OBJECT}.rdata_renamed.tmp")
set(cleaned_object "${OUTPUT_OBJECT}.rdata_cleaned.tmp")
file(REMOVE "${renamed_object}" "${cleaned_object}" "${OUTPUT_OBJECT}")

execute_process(
  COMMAND "${OBJCOPY}" ${objcopy_args} --wildcard --localize-symbol=.refptr.* "${INPUT_OBJECT}" "${renamed_object}"
  ERROR_VARIABLE objcopy_error
  RESULT_VARIABLE objcopy_result
)
if(NOT objcopy_result EQUAL 0)
  message(FATAL_ERROR
    "FIPS MinGW rodata merge: failed to rename grouped .rdata sections\n${objcopy_error}")
endif()

# Re-link the renamed object to coalesce the duplicate .rdata sections into one
# contiguous section. Warnings from intermediate COMDAT section names are
# expected after the rename and are intentionally not surfaced on success.
execute_process(
  COMMAND "${LINKER}" -r "${renamed_object}" -o "${OUTPUT_OBJECT}"
  ERROR_VARIABLE linker_error
  RESULT_VARIABLE linker_result
)
file(REMOVE "${renamed_object}")
if(NOT linker_result EQUAL 0)
  message(FATAL_ERROR
    "FIPS MinGW rodata merge: failed to merge grouped .rdata sections\n${linker_error}")
endif()

# The rename can leave the merged .rdata section marked LINK_ONCE/COMDAT. Clear
# that metadata so the final DLL link emits base-relocation entries for absolute
# refptr cells inside the FIPS rodata window.
execute_process(
  COMMAND "${OBJCOPY}"
          --set-section-flags ".rdata=alloc,load,readonly,data,contents"
          "${OUTPUT_OBJECT}" "${cleaned_object}"
  ERROR_VARIABLE objcopy_flags_error
  RESULT_VARIABLE objcopy_flags_result
)
if(NOT objcopy_flags_result EQUAL 0)
  message(FATAL_ERROR
    "FIPS MinGW rodata merge: failed to clear merged .rdata flags\n${objcopy_flags_error}")
endif()
file(REMOVE "${OUTPUT_OBJECT}")
file(RENAME "${cleaned_object}" "${OUTPUT_OBJECT}")
