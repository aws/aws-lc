# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# The crate object fold for windows-msvc, windows-gnullvm and wasm, run by
# cargo.cmake with `cmake -P`. llvm-objcopy can't make COFF or wasm symbols
# local, but fat LTO already makes `core` internal to the crate object, so
# OUTPUT is that object, taken out of the staticlib. The build fails
# if it defines an external symbol other than the exports, needs a symbol from
# another member (compiler_builtins), or carries linker directives (.drectve).
# With PERSONALITY (windows-gnullvm), the fold renames the crate's
# rust_eh_personality to PERSONALITY, which no consumer's Rust defines.
#
# With ASM_LIB, a static library holding one object, the crate's own copy of
# its assembly, the fold writes that object to ASM_OUTPUT. COFF symbols can't
# be made local, so it renames the copy's symbols, and the crate object's
# references to them, by adding _bcm_rust: libcrypto has its own copy.
#
# With COFF_SECTIONS, OUTPUT is a FIPS module (crypto/rust/fipsmodule/src/
# fips.rs). Where ELF has bcm-rust.lds, COFF_SECTIONS renames both objects'
# code and constants into one group of sections, which the linker sorts by
# their $ suffix and merges into one section, .bcmrs: the start marker in
# $a, the module in $m and the end marker in $z. The hash goes to .rdata,
# outside the region. Sections not named here, such as .data, .pdata and
# .xdata, stay outside the region. The crate's COMDAT constants get names of
# their own, so that none folds with an identical constant outside the module.
#
# Inputs (-D): LLVM_AR LLVM_NM LLVM_OBJDUMP STATICLIB EXPORTS_FILE OUTPUT, and
# optionally LLVM_OBJCOPY PERSONALITY ASM_LIB ASM_OUTPUT COFF_SECTIONS

# MSVC names float and vector constants __real@<hex>, __xmm@<hex> and so on,
# in COMDAT sections, exactly as MSVC's C compiler does. MinGW reaches C data,
# such as OPENSSL_ia32cap_P, through a pointer named .refptr.<symbol>, in a
# COMDAT section, as MinGW's C compiler does. Duplicates fold.
set(comdat_constant "^(__(real|xmm|ymm|zmm)@[0-9a-f]+|\\.refptr\\..+)$")

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
set(crate_constants "")
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
    else()
      list(APPEND crate_constants "${sym}")
    endif()
  endif()
endforeach()
if(PERSONALITY)
  list(REMOVE_ITEM crate_defined rust_eh_personality)
endif()
if(COFF_SECTIONS)
  # The module region's markers, which inject_hash finds in the linker's map.
  list(REMOVE_ITEM crate_defined BORINGSSL_bcm_rust_text_start BORINGSSL_bcm_rust_text_end)
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

# Extract to temporary files and rename them only after the checks pass, so a
# failed check leaves no OUTPUT that a later build would treat as up to date.
function(extract lib member out)
  execute_process(COMMAND ${LLVM_AR} p "${lib}" "${member}" OUTPUT_FILE "${out}" RESULT_VARIABLE rc)
  if(NOT rc EQUAL 0)
    message(FATAL_ERROR "rust crate object fold: can't extract ${member} from ${lib}")
  endif()
endfunction()
set(tmp "${OUTPUT}.tmp")
extract("${STATICLIB}" "${crate}" "${tmp}")
run(${LLVM_OBJDUMP} -h "${tmp}")
if(run_out MATCHES "\\.drectve")
  message(FATAL_ERROR "rust crate object fold: the crate object has linker directives (.drectve)")
endif()
set(renames "")
if(PERSONALITY)
  list(APPEND renames "--redefine-sym=rust_eh_personality=${PERSONALITY}")
endif()
set(objects "${tmp}")
if(ASM_LIB)
  run(${LLVM_AR} t "${ASM_LIB}")
  string(STRIP "${run_out}" asm_members)
  string(REPLACE "\n" ";" asm_members "${asm_members}")
  list(LENGTH asm_members n)
  if(NOT n EQUAL 1)
    message(FATAL_ERROR "rust crate object fold: ${ASM_LIB} holds ${n} objects, expected one")
  endif()
  set(asm_tmp "${ASM_OUTPUT}.tmp")
  extract("${ASM_LIB}" "${asm_members}" "${asm_tmp}")
  run(${LLVM_NM} --extern-only --defined-only --format=just-symbols "${asm_tmp}")
  string(REPLACE "\n" ";" asm_symbols "${run_out}")
  foreach(sym IN LISTS asm_symbols)
    if(sym)
      list(APPEND renames "--redefine-sym=${sym}=${sym}_bcm_rust")
    endif()
  endforeach()
  run(${LLVM_OBJCOPY} ${renames} "${asm_tmp}")
  list(APPEND objects "${asm_tmp}")
endif()
if(COFF_SECTIONS)
  foreach(sym IN LISTS crate_constants)
    list(APPEND renames "--redefine-sym=${sym}=${sym}_bcm_rust")
  endforeach()
endif()
if(renames)
  run(${LLVM_OBJCOPY} ${renames} "${tmp}")
endif()
if(COFF_SECTIONS)
  foreach(obj IN LISTS objects)
    run("${COFF_SECTIONS}" -o "${obj}" "${obj}"
      ".bcm_rust_text_start=.bcmrs$a,code" ".bcm_rust_text_end=.bcmrs$z,code"
      ".bcm_rust_text_hash=.rdata" ".text*=.bcmrs$m" ".rdata*=.bcmrs$m,code"
      ".rodata*=.bcmrs$m,code")
  endforeach()
endif()
if(ASM_LIB)
  file(RENAME "${asm_tmp}" "${ASM_OUTPUT}")
endif()
file(RENAME "${tmp}" "${OUTPUT}")
