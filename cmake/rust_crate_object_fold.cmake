# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# rust-phase0: the crate object fold for windows-msvc, windows-gnullvm and
# wasm, run by cargo.cmake with `cmake -P`. llvm-objcopy can't make COFF or
# wasm symbols local, but fat LTO already makes `core` internal to the crate
# object, so OUTPUT is that object, taken out of the staticlib. The build fails
# if it defines an external symbol other than the exports, needs a symbol from
# another member (compiler_builtins), or carries linker directives (.drectve).
# With LLVM_OBJCOPY (windows-gnullvm), the fold renames caracal's
# rust_eh_personality to PERSONALITY, which no consumer's Rust defines.
#
# Inputs (-D): LLVM_AR LLVM_NM LLVM_OBJDUMP STATICLIB EXPORTS_FILE OUTPUT,
# and optionally LLVM_OBJCOPY PERSONALITY

# MSVC names float and vector constants __real@<hex>, __xmm@<hex> and so on,
# in COMDAT sections, exactly as MSVC's C compiler does. Duplicates fold.
set(comdat_constant "^__(real|xmm|ymm|zmm)@[0-9a-f]+$")

function(run)
  execute_process(COMMAND ${ARGN} RESULT_VARIABLE rc OUTPUT_VARIABLE out ERROR_VARIABLE err)
  if(NOT rc EQUAL 0)
    string(REPLACE ";" " " cmd "${ARGN}")
    message(FATAL_ERROR "rust crate object fold: '${cmd}' failed:\n${out}${err}")
  endif()
  set(run_out "${out}" PARENT_SCOPE)
endfunction()

# Every external symbol in the staticlib, one per line of llvm-nm's POSIX
# output: "<lib>[<member>]: <symbol> <type> ...". The crate object is the
# member that defines the first export.
file(STRINGS "${EXPORTS_FILE}" exports)
list(GET exports 0 first_export)
run(${LLVM_NM} -A --format=posix --extern-only "${STATICLIB}")
if(NOT run_out MATCHES "\\[([^][]+)\\]: ${first_export} [^U]")
  message(FATAL_ERROR "rust crate object fold: no member of ${STATICLIB} defines ${first_export}")
endif()
set(crate "${CMAKE_MATCH_1}")
string(REPLACE "\n" ";" nm_lines "${run_out}")

set(crate_defined "")
set(crate_undefined "")
set(others_defined "")
foreach(line IN LISTS nm_lines)
  if(line MATCHES "\\[([^][]+)\\]: ([^ ]+) ([A-Za-z])")
    set(member "${CMAKE_MATCH_1}")
    set(sym "${CMAKE_MATCH_2}")
    set(type "${CMAKE_MATCH_3}")
    if(NOT member STREQUAL crate)
      if(NOT type STREQUAL "U")
        list(APPEND others_defined "${sym}")
      endif()
    elseif(type STREQUAL "U")
      list(APPEND crate_undefined "${sym}")
    elseif(NOT sym MATCHES "${comdat_constant}")
      list(APPEND crate_defined "${sym}")
    endif()
  endif()
endforeach()
if(LLVM_OBJCOPY)
  list(REMOVE_ITEM crate_defined rust_eh_personality)
endif()
list(SORT crate_defined)
list(SORT exports)
if(NOT crate_defined STREQUAL exports)
  message(FATAL_ERROR "rust crate object fold: the crate object defines external symbols "
                      "'${crate_defined}', expected only '${exports}'")
endif()
# Anything no member defines comes from the C runtime (abort, memcpy).
foreach(sym IN LISTS crate_undefined)
  list(FIND others_defined "${sym}" i)
  if(NOT i EQUAL -1)
    message(FATAL_ERROR "rust crate object fold: the crate object needs ${sym} from another "
                        "member of ${STATICLIB}, which the fold doesn't take")
  endif()
endforeach()

# Extract to a temporary file and rename it only after the checks pass, so a
# failed check leaves no OUTPUT that a later build would treat as up to date.
set(tmp "${OUTPUT}.tmp")
execute_process(COMMAND ${LLVM_AR} p "${STATICLIB}" "${crate}" OUTPUT_FILE "${tmp}" RESULT_VARIABLE rc)
if(NOT rc EQUAL 0)
  message(FATAL_ERROR "rust crate object fold: can't extract ${crate} from ${STATICLIB}")
endif()
run(${LLVM_OBJDUMP} -h "${tmp}")
if(run_out MATCHES "\\.drectve")
  message(FATAL_ERROR "rust crate object fold: the crate object has linker directives (.drectve)")
endif()
if(LLVM_OBJCOPY)
  run(${LLVM_OBJCOPY} "--redefine-sym=rust_eh_personality=${PERSONALITY}" "${tmp}")
endif()
file(RENAME "${tmp}" "${OUTPUT}")
