# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Builds the Rust crate as a staticlib with CMake-forced Cargo settings and
# folds it into one object, bcm-rust.o, that build_libcrypto() adds the way the
# FIPS build adds bcm.o. Consumers still link only libcrypto.
# Cargo discovery comes from the caracal PoC's cmake/cargo.cmake.

# With ENABLE_RUST=AUTO, the default, a failed check below logs why and builds
# without Rust, where ENABLE_RUST=ON fails configure. message() with no mode
# prints the GitHub Actions annotation without "-- ", so it shows on the job's
# summary page. return() leaves this included file, not the caller.
macro(rust_unsupported)
  if(ENABLE_RUST STREQUAL "AUTO")
    string(CONCAT rust_reason ${ARGN})
    message(STATUS "ENABLE_RUST=AUTO: building without Rust: ${rust_reason}")
    message("::warning title=ENABLE_RUST::building without Rust: ${rust_reason}")
    set(ENABLE_RUST OFF)
    return()
  endif()
  message(FATAL_ERROR ${ARGN})
endmacro()

# Multi-config generators build one bcm-rust.o per configuration. The build tool
# expands ${CMAKE_CFG_INTDIR} in custom command outputs on every CMake
# version; $<CONFIG> there needs CMake 3.20.
if(CMAKE_CONFIGURATION_TYPES)
  set(RUST_CONFIG_DIR "/${CMAKE_CFG_INTDIR}")
else()
  set(RUST_CONFIG_DIR "")
endif()
# Cargo builds one target per run, so bcm-rust.o holds one architecture.
if(APPLE AND CMAKE_OSX_ARCHITECTURES MATCHES ";")
  rust_unsupported("ENABLE_RUST does not support universal binaries")
endif()

find_program(CARGO_EXECUTABLE NAMES cargo
             HINTS "$ENV{CARGO_HOME}/bin" "$ENV{HOME}/.cargo/bin")
find_program(RUSTC_EXECUTABLE NAMES rustc
             HINTS "$ENV{CARGO_HOME}/bin" "$ENV{HOME}/.cargo/bin")
if(NOT CARGO_EXECUTABLE OR NOT RUSTC_EXECUTABLE)
  rust_unsupported("ENABLE_RUST is set but cargo/rustc was not found. Install a "
                      "Rust toolchain or set CARGO_EXECUTABLE and RUSTC_EXECUTABLE.")
endif()
execute_process(COMMAND ${RUSTC_EXECUTABLE} -vV
  RESULT_VARIABLE rustc_result OUTPUT_VARIABLE rustc_vv ERROR_VARIABLE rustc_err
  OUTPUT_STRIP_TRAILING_WHITESPACE ERROR_STRIP_TRAILING_WHITESPACE)
if(NOT rustc_result EQUAL 0 OR NOT rustc_vv)
  rust_unsupported("ENABLE_RUST: '${RUSTC_EXECUTABLE} -vV' failed: ${rustc_err}")
endif()
string(REGEX MATCH "^[^\n]*" RUSTC_VERSION_OUTPUT "${rustc_vv}")
string(REGEX MATCH "\nhost: ([^\r\n]+)" rust_host "${rustc_vv}")
set(rust_host "${CMAKE_MATCH_1}")
message(STATUS "Found cargo: ${CARGO_EXECUTABLE}; rustc: ${RUSTC_EXECUTABLE} (${RUSTC_VERSION_OUTPUT})")
# The crate uses the 2024 edition, which needs rustc 1.85.
string(REGEX MATCH "[0-9]+\\.[0-9]+\\.[0-9]+" RUSTC_VERSION "${RUSTC_VERSION_OUTPUT}")
if(RUSTC_VERSION VERSION_LESS 1.85)
  rust_unsupported("ENABLE_RUST needs rustc 1.85 or newer, for the 2024 edition; "
                      "found '${RUSTC_VERSION_OUTPUT}'")
endif()

# The C library check and the partial link get the C flags from the toolchain
# file or the user, such as -m32, and the compiler target. AWS-LC adds its own
# flags after this file runs: with -fsanitize, clang links a sanitizer runtime
# into bcm-rust.o even with -nostdlib. -fno-sanitize=all, which GCC 4.8 lacks,
# keeps out one passed in CFLAGS.
if(CMAKE_HOST_WIN32)
  separate_arguments(RUST_LINK_C_FLAGS WINDOWS_COMMAND "${CMAKE_C_FLAGS}")
else()
  separate_arguments(RUST_LINK_C_FLAGS UNIX_COMMAND "${CMAKE_C_FLAGS}")
endif()
if(CMAKE_C_FLAGS MATCHES "-fsanitize=")
  list(APPEND RUST_LINK_C_FLAGS -fno-sanitize=all)
endif()
if(CMAKE_C_COMPILER_TARGET AND CMAKE_C_COMPILE_OPTIONS_TARGET)
  list(APPEND RUST_LINK_C_FLAGS "${CMAKE_C_COMPILE_OPTIONS_TARGET}${CMAKE_C_COMPILER_TARGET}")
endif()

# rust_target_from_c(<var>) sets <var> to the Rust target triple of the C
# toolchain, or to "" for a system it doesn't know. The CPU comes from
# CMAKE_SYSTEM_PROCESSOR, because gcc -m32 still reports an x86_64 triple, or
# from the compiler's triple when a toolchain sets only CMAKE_SYSTEM_NAME. On
# Linux the C library and the ARM float ABI come from the C headers' macros
# (zig's -dumpmachine reports musl when zig builds against glibc), else from
# the triple.
function(rust_target_from_c var)
  set(c_triple "${CMAKE_C_COMPILER_TARGET}")
  if(NOT c_triple AND NOT MSVC)
    execute_process(COMMAND ${CMAKE_C_COMPILER} -dumpmachine
      OUTPUT_VARIABLE c_triple OUTPUT_STRIP_TRAILING_WHITESPACE ERROR_QUIET)
  endif()
  string(TOLOWER "${CMAKE_SYSTEM_PROCESSOR}" cpu)
  if(NOT cpu)
    string(REGEX MATCH "^[^-]+" cpu "${c_triple}")
  endif()
  string(REGEX REPLACE "^(amd64|x64)$" x86_64 cpu "${cpu}")
  string(REGEX REPLACE "^(x86|i[3-6]86)$" i686 cpu "${cpu}")
  string(REGEX REPLACE "^arm64$" aarch64 cpu "${cpu}")
  string(REGEX REPLACE "^arm.*" arm cpu "${cpu}")
  string(REGEX REPLACE "^ppc" powerpc cpu "${cpu}")
  string(REGEX REPLACE "^riscv(64)?$" riscv64gc cpu "${cpu}")
  set(libc gnu)
  if(c_triple MATCHES "musl|uclibc")
    set(libc "${CMAKE_MATCH_0}")
  endif()
  string(REGEX MATCH "hf$" hf "${c_triple}")
  if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
    # musl defines no macro of its own.
    set(probe "${CMAKE_CURRENT_BINARY_DIR}/rust_libc_probe.c")
    file(WRITE "${probe}" "#include <features.h>
#if defined(__UCLIBC__)
awslc_libc=uclibc
#elif defined(__GLIBC__)
awslc_libc=gnu
#else
awslc_libc=musl
#endif
#if defined(__ARM_PCS_VFP)
awslc_float=hf
#endif
")
    set(sysroot "")
    if(CMAKE_SYSROOT AND CMAKE_C_COMPILE_OPTIONS_SYSROOT)
      set(sysroot "${CMAKE_C_COMPILE_OPTIONS_SYSROOT}${CMAKE_SYSROOT}")
    endif()
    execute_process(COMMAND ${CMAKE_C_COMPILER} ${RUST_LINK_C_FLAGS} ${sysroot} -E "${probe}"
      RESULT_VARIABLE rc OUTPUT_VARIABLE macros ERROR_QUIET)
    if(rc EQUAL 0 AND macros MATCHES "awslc_libc=([a-z]+)")
      set(libc "${CMAKE_MATCH_1}")
      set(hf "")
      if(macros MATCHES "awslc_float=hf")
        set(hf hf)
      endif()
    endif()
  endif()

  set(target "")
  if(c_triple MATCHES "^wasm32-wasip2")
    set(target wasm32-wasip2)
  elseif(c_triple MATCHES "^wasm32-wasi")
    set(target wasm32-wasip1)
  elseif(CMAKE_SYSTEM_NAME STREQUAL "Linux")
    if(cpu STREQUAL "arm" AND libc STREQUAL "uclibc")
      # Rust has no generic arm uClibc target, only armv5te and armv7.
      set(target armv7-unknown-linux-uclibceabi${hf})
    elseif(cpu STREQUAL "arm" AND c_triple MATCHES "^armv7")
      set(target armv7-unknown-linux-${libc}eabi${hf})
    elseif(cpu STREQUAL "arm")
      set(target arm-unknown-linux-${libc}eabi${hf})
    else()
      set(target ${cpu}-unknown-linux-${libc})
    endif()
  elseif(CMAKE_SYSTEM_NAME STREQUAL "Android")
    if(cpu STREQUAL "arm")
      set(target armv7-linux-androideabi)
    else()
      set(target ${cpu}-linux-android)
    endif()
  elseif(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
    set(target ${cpu}-apple-darwin)
  elseif(CMAKE_SYSTEM_NAME STREQUAL "iOS")
    set(target ${cpu}-apple-ios)
    string(TOLOWER "${CMAKE_OSX_SYSROOT}" sysroot)
    if(cpu STREQUAL "aarch64" AND sysroot MATCHES "simulator")
      string(APPEND target -sim)
    endif()
  elseif(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    # clang.exe can target the MSVC ABI too. MinGW Clang (MSYS2 clang64, zig)
    # is Rust's gnullvm.
    if(MSVC OR c_triple MATCHES "msvc")
      set(target ${cpu}-pc-windows-msvc)
    elseif(CMAKE_C_COMPILER_ID STREQUAL "GNU")
      set(target ${cpu}-pc-windows-gnu)
    else()
      set(target ${cpu}-pc-windows-gnullvm)
    endif()
  endif()
  set(${var} "${target}" PARENT_SCOPE)
endfunction()

set(RUST_TARGET "" CACHE STRING "Rust target triple to build for when ENABLE_RUST is on \
(default: the host, or when cross-compiling, the target of the C toolchain)")
# RUST_CARGO_TARGET is Cargo's --target, empty to build for rustc's host.
set(RUST_CARGO_TARGET "${RUST_TARGET}")
if(CMAKE_CROSSCOMPILING AND NOT RUST_TARGET)
  if(DEFINED ENV{CARGO_MANIFEST_DIR} AND DEFINED ENV{TARGET})
    # A Cargo build script runs CMake (aws-lc-sys): build for Cargo's target.
    set(RUST_CARGO_TARGET "$ENV{TARGET}")
  elseif(CMAKE_SYSTEM_NAME STREQUAL "Emscripten")
    rust_unsupported("ENABLE_RUST does not support Emscripten: its -pthread build "
                        "needs Rust's std rebuilt with -Zbuild-std")
  else()
    rust_target_from_c(RUST_CARGO_TARGET)
    if(NOT RUST_CARGO_TARGET)
      rust_unsupported("ENABLE_RUST can't derive a Rust target for ${CMAKE_SYSTEM_NAME} "
                          "${CMAKE_SYSTEM_PROCESSOR}; set RUST_TARGET")
    endif()
  endif()
  # CMake counts every build with a preset CMAKE_SYSTEM_NAME as cross, native
  # ones too (zig, MSYS2, the cmake crate on Apple). Those need no --target.
  if(RUST_CARGO_TARGET STREQUAL rust_host)
    set(RUST_CARGO_TARGET "")
  endif()
endif()
if(RUST_CARGO_TARGET)
  # rustc prints no target-libdir for a target it doesn't know.
  execute_process(COMMAND ${RUSTC_EXECUTABLE} --print target-libdir --target ${RUST_CARGO_TARGET}
    OUTPUT_VARIABLE target_libdir OUTPUT_STRIP_TRAILING_WHITESPACE ERROR_QUIET)
  if(target_libdir)
    file(GLOB libcore "${target_libdir}/libcore-*.rlib")
  endif()
  if(NOT libcore)
    rust_unsupported("ENABLE_RUST: no Rust standard library for ${RUST_CARGO_TARGET}: "
                        "rustup target add ${RUST_CARGO_TARGET}")
  endif()
  message(STATUS "Rust target: ${RUST_CARGO_TARGET}")
  set(rust_triple "${RUST_CARGO_TARGET}")
else()
  set(rust_triple "${rust_host}")
endif()

# Consumer-supplied rustc flags, the Rust analogue of CMAKE_C_FLAGS. They reach
# rustc with ours, as `cargo rustc` arguments (cargo_add_rust_object).
set(RUST_FLAGS "" CACHE STRING "Extra rustc flags (semicolon-separated list)")
# Cargo passes RUST_FLAGS after the profile settings forced below, and rustc
# keeps the last of a repeated -C option: -Copt-level=0 brought panic data back.
set(forced_codegen "opt-level|lto|codegen-units|panic|debuginfo|debug-assertions|overflow-checks|incremental")
foreach(flag IN LISTS RUST_FLAGS)
  if(flag MATCHES "^(-C *|--codegen[= ]*)?(${forced_codegen})(=|$)" OR flag MATCHES "^-[Og]$")
    message(FATAL_ERROR "RUST_FLAGS must not contain '${flag}': CMake forces "
                        "opt-level, lto, codegen-units, panic, debug info and checks")
  endif()
endforeach()

# The C toolchain's objcopy makes Rust symbols local, on ELF and MinGW GCC, and
# Apple's linker does it itself. windows-msvc and windows-gnullvm have no
# partial link, and wasm-ld's can't take -u, so those targets take the crate
# object fold. It needs LLVM tools from rustup's llvm-tools or an LLVM C
# toolchain.
set(RUST_CRATE_OBJECT_FOLD OFF)
if(rust_triple MATCHES "-windows-(msvc|gnullvm)$|^wasm")
  set(RUST_CRATE_OBJECT_FOLD ON)
  # The host's target-libdir is <sysroot>/lib/rustlib/<host>/lib.
  execute_process(COMMAND ${RUSTC_EXECUTABLE} --print target-libdir
    OUTPUT_VARIABLE rust_libdir OUTPUT_STRIP_TRAILING_WHITESPACE)
  # Linux packages often install clang as a symlink into the LLVM bin directory.
  get_filename_component(c_compiler_dir "${CMAKE_C_COMPILER}" DIRECTORY)
  get_filename_component(c_compiler_real "${CMAKE_C_COMPILER}" REALPATH)
  get_filename_component(c_compiler_real_dir "${c_compiler_real}" DIRECTORY)
  set(llvm_tools ar nm objdump)
  if(rust_triple MATCHES "-windows-gnullvm$")
    list(APPEND llvm_tools objcopy)
  endif()
  foreach(tool IN LISTS llvm_tools)
    string(TOUPPER "${tool}" TOOL)
    find_program(RUST_LLVM_${TOOL} NAMES llvm-${tool} NO_DEFAULT_PATH
                 HINTS "${rust_libdir}/../bin" "${c_compiler_dir}" "${c_compiler_real_dir}")
    if(NOT RUST_LLVM_${TOOL})
      rust_unsupported("ENABLE_RUST for ${rust_triple} needs llvm-${tool}: "
                          "rustup component add llvm-tools")
    endif()
  endforeach()
elseif(NOT APPLE AND NOT CMAKE_OBJCOPY)
  rust_unsupported("ENABLE_RUST needs objcopy")
endif()
if(ENABLE_RUST STREQUAL "AUTO")
  message(STATUS "ENABLE_RUST=AUTO: building with Rust")
  message("::notice title=ENABLE_RUST::building with Rust")
endif()

# Rust code in a FIPS build has to be FIPS module code, or it would break the
# build's validation. No FIPS module holds Rust yet, so a FIPS build that finds
# Rust fails, even with AUTO. -DENABLE_RUST=OFF builds C only.
if(FIPS)
  message(FATAL_ERROR "ENABLE_RUST: FIPS builds can't use Rust yet: no FIPS "
                      "module holds Rust code. Configure with -DENABLE_RUST=OFF "
                      "to build C only.")
endif()

# cargo_add_rust_object(OUTPUT <object> MANIFEST_PATH <Cargo.toml>
#                       LIB_NAME <name> [CFGS <cfg>...] EXPORTS <sym>...)
#
# Adds a custom command producing OUTPUT, built with each of CFGS set as a
# Rust cfg, in which only EXPORTS stay global, and hidden where the object
# format has visibility, so libcrypto doesn't export them. With
# BORINGSSL_PREFIX, EXPORTS carry the prefix in both the Rust and the C code.
# Use OUTPUT as a source file of a target in the same directory.
function(cargo_add_rust_object)
  cmake_parse_arguments(arg "" "OUTPUT;MANIFEST_PATH;LIB_NAME" "CFGS;EXPORTS" ${ARGN})
  get_filename_component(crate_dir "${arg_MANIFEST_PATH}" DIRECTORY)
  file(GLOB_RECURSE rust_sources "${crate_dir}/*.rs" "${crate_dir}/Cargo.toml" "${crate_dir}/Cargo.lock")

  set(target_dir "${AWSLC_BINARY_DIR}/cargo${RUST_CONFIG_DIR}")
  set(out_dir "${target_dir}")
  set(cargo_target_args "")
  if(RUST_CARGO_TARGET)
    set(cargo_target_args --target "${RUST_CARGO_TARGET}")
    set(out_dir "${out_dir}/${RUST_CARGO_TARGET}")
  endif()
  # Always Cargo's release profile; CMake pins every setting that matters.
  set(staticlib "${out_dir}/release/${CMAKE_STATIC_LIBRARY_PREFIX}${arg_LIB_NAME}${CMAKE_STATIC_LIBRARY_SUFFIX}")

  # Debug (or no build type) gets Rust's debug settings, anything else Release's.
  string(TOLOWER "${CMAKE_BUILD_TYPE}" build_type_lower)
  if(CMAKE_CONFIGURATION_TYPES)
    set(is_debug "$<CONFIG:Debug>")
  elseif(build_type_lower MATCHES "^(debug)?$")
    set(is_debug 1)
  else()
    set(is_debug 0)
  endif()
  # Debug uses opt-level 2. Below it, core's unwinding code keeps references
  # to rust_eh_personality: pass 2 of the Xcode 16 and 26 linkers turns the
  # Apple fold's local copy into an undefined symbol, and ELF objects get a
  # COMDAT group (see the ELF fold).
  set(rust_opt "$<${is_debug}:2>$<$<NOT:${is_debug}>:3>")
  set(rust_debug "$<${is_debug}:true>$<$<NOT:${is_debug}>:false>")

  # Forced settings. --config outranks Cargo.toml and config files.
  set(P "profile.release")
  set(forced_config
    --config "${P}.opt-level=${rust_opt}"
    --config "${P}.lto=\"fat\""
    --config "${P}.codegen-units=1"
    --config "${P}.panic=\"abort\""
    --config "${P}.debug=${rust_debug}"
    --config "${P}.debug-assertions=${rust_debug}"
    --config "${P}.overflow-checks=${rust_debug}"
    --config "${P}.incremental=false"
    --config "build.rustc-wrapper=\"\""
    --config "build.rustc-workspace-wrapper=\"\"")
  set(rustflags ${RUST_FLAGS})
  foreach(cfg IN LISTS arg_CFGS)
    list(APPEND rustflags "--cfg=${cfg}")
  endforeach()
  set(symbol_prefix "")
  set(export_prefix "")
  if(BORINGSSL_PREFIX)
    # src/lib.rs prefixes its exports with the prefix the C code gets from
    # boringssl_prefix_symbols.h. Supplied headers set their own, which can
    # differ: aws-lc-sys passes BORINGSSL_PREFIX=<prefix>_ with headers that
    # define <prefix>.
    set(symbol_prefix "${BORINGSSL_PREFIX}")
    if(BORINGSSL_PREFIX_HEADERS_PATH)
      file(STRINGS "${BORINGSSL_PREFIX_HEADERS_PATH}/openssl/boringssl_prefix_symbols.h"
           prefix_define REGEX "^#define BORINGSSL_PREFIX [A-Za-z0-9_]+" LIMIT_COUNT 1)
      if(prefix_define)
        string(REGEX REPLACE "^#define BORINGSSL_PREFIX ([A-Za-z0-9_]+).*" "\\1"
               symbol_prefix "${prefix_define}")
      endif()
    endif()
    list(APPEND rustflags --cfg=awslc_prefix)
    set(export_prefix "${symbol_prefix}_")
  endif()
  # The rustflags go to rustc as `cargo rustc` arguments, not in
  # CARGO_ENCODED_RUSTFLAGS: its 0x1f separator can't be written into a Visual
  # Studio project, which is XML. An empty CARGO_ENCODED_RUSTFLAGS still
  # outranks RUSTFLAGS and config-file rustflags, so none of those reach rustc.
  # RUSTC and RUSTC_WRAPPER env vars are read by Cargo directly, so pin them too.
  set(cargo_env ${CMAKE_COMMAND} -E env
    "RUSTC=${RUSTC_EXECUTABLE}"
    "RUSTC_WRAPPER="
    "RUSTC_WORKSPACE_WRAPPER="
    "CARGO_ENCODED_RUSTFLAGS="
    "BORINGSSL_PREFIX=${symbol_prefix}"
    --unset=RUSTFLAGS)
  if(APPLE)
    # rustc reads the deployment target from the environment. Match the C code.
    if(IOS)
      set(deployment_var IPHONEOS_DEPLOYMENT_TARGET)
    else()
      set(deployment_var MACOSX_DEPLOYMENT_TARGET)
    endif()
    if(CMAKE_OSX_DEPLOYMENT_TARGET)
      list(APPEND cargo_env "${deployment_var}=${CMAKE_OSX_DEPLOYMENT_TARGET}")
    else()
      list(APPEND cargo_env "--unset=${deployment_var}")
    endif()
  endif()

  # A partial link with `-u <export>` takes the crate object out of the
  # staticlib, plus only the members it needs (compiler_builtins helpers).
  # Every other symbol then becomes local.
  get_filename_component(output_dir "${arg_OUTPUT}" DIRECTORY)
  get_filename_component(output_name "${arg_OUTPUT}" NAME_WE)
  set(linked_obj "${output_dir}/${output_name}_full.o")
  set(exports_file "${CMAKE_CURRENT_BINARY_DIR}/rust_exports.txt")
  set(export_syms "")
  set(undefined_args "")
  foreach(sym ${arg_EXPORTS})
    set(sym "${export_prefix}${sym}")
    if(APPLE)
      # Mach-O prefixes C symbol names with an underscore.
      set(sym "_${sym}")
    endif()
    list(APPEND export_syms "${sym}")
    # -Wl,-u, because zig cc reads a bare -u argument as an input file.
    list(APPEND undefined_args "-Wl,-u,${sym}")
  endforeach()
  string(REPLACE ";" "\n" exports_text "${export_syms}")
  file(WRITE "${exports_file}" "${exports_text}\n")

  # The partial link runs through the driver CMake links C programs with,
  # which tells the linker the target: with only a library as input, lld 14
  # needs -m and Apple's ld -arch and -platform_version. zig's Apple toolchain
  # file sets /usr/bin/cc as that driver.
  string(REGEX MATCH "^[^ ]+" link_driver "${CMAKE_C_LINK_EXECUTABLE}")
  if(NOT link_driver OR link_driver MATCHES "^<")
    set(link_driver "${CMAKE_C_COMPILER}")
  endif()
  set(partial_link ${link_driver} -r -nostdlib ${RUST_LINK_C_FLAGS})
  if(APPLE)
    # Same -arch, -platform_version and SDK as the C code. Pass 1 makes every
    # symbol but the exports local: hidden but global would still clash with
    # a consumer's own Rust in a static link. Pass 2 hides the exports.
    # Apple's compilers call aarch64 arm64.
    string(REPLACE aarch64 arm64 osx_arch "${CMAKE_SYSTEM_PROCESSOR}")
    list(APPEND partial_link -arch ${osx_arch})
    if(CMAKE_OSX_SYSROOT)
      list(APPEND partial_link -isysroot "${CMAKE_OSX_SYSROOT}")
    endif()
    if(CMAKE_OSX_DEPLOYMENT_TARGET)
      list(APPEND partial_link "${CMAKE_C_OSX_DEPLOYMENT_TARGET_FLAG}${CMAKE_OSX_DEPLOYMENT_TARGET}")
    endif()
    set(fold_commands
      COMMAND ${partial_link} ${undefined_args}
        "-Wl,-exported_symbols_list,${exports_file}" -o "${linked_obj}" "${staticlib}"
      COMMAND ${partial_link} -Wl,-keep_private_externs
        "-Wl,-unexported_symbols_list,${exports_file}" -o "${arg_OUTPUT}" "${linked_obj}")
  elseif(RUST_CRATE_OBJECT_FOLD)
    set(fold_commands
      COMMAND ${CMAKE_COMMAND} "-DLLVM_AR=${RUST_LLVM_AR}" "-DLLVM_NM=${RUST_LLVM_NM}"
        "-DLLVM_OBJDUMP=${RUST_LLVM_OBJDUMP}" "-DLLVM_OBJCOPY=${RUST_LLVM_OBJCOPY}"
        "-DPERSONALITY=${export_prefix}awslc_rust_eh_personality" "-DSTATICLIB=${staticlib}"
        "-DEXPORTS_FILE=${exports_file}" "-DOUTPUT=${arg_OUTPUT}"
        -P "${AWSLC_SOURCE_DIR}/cmake/rust_crate_object_fold.cmake")
  else()
    # On ELF, a stub of .hidden directives makes the exports hidden in the
    # object itself, whether or not C calls them. COFF (MinGW) has no
    # visibility, and Windows exports only functions marked for export.
    set(hidden_stub "")
    if(NOT WIN32)
      set(hidden_stub "${CMAKE_CURRENT_BINARY_DIR}/rust_exports_hidden.s")
      string(REPLACE ";" "\n.hidden " hidden_text "${export_syms}")
      # Without the note, the linker would give the stub an executable stack.
      file(WRITE "${hidden_stub}" ".hidden ${hidden_text}\n.section .note.GNU-stack,\"\",%progbits\n")
    endif()
    # MinGW reaches C data through a pointer, .refptr.<symbol>, in a COMDAT
    # that C's objects define too. It stays global: the linker keeps one copy
    # and resolves every object's references to it.
    set(keep_refptr "")
    if(WIN32)
      set(keep_refptr --wildcard "--keep-global-symbol=.refptr.*")
    endif()
    # Code that keeps core's unwind paths (opt-level 1 does) puts
    # DW.ref.rust_eh_personality in a COMDAT group. A consumer's own Rust has a
    # group of the same name, so its linker would keep one and reject our
    # references into the dropped copy. The rename gives ours a name no
    # consumer's Rust uses.
    set(fold_commands
      COMMAND ${partial_link} ${undefined_args} -o "${linked_obj}" ${hidden_stub} "${staticlib}"
      COMMAND ${CMAKE_OBJCOPY} "--keep-global-symbols=${exports_file}" ${keep_refptr}
        "--redefine-sym=DW.ref.rust_eh_personality=${export_prefix}awslc_DW.ref.rust_eh_personality"
        "${linked_obj}" "${arg_OUTPUT}")
  endif()

  add_custom_command(
    OUTPUT "${arg_OUTPUT}"
    COMMAND ${CMAKE_COMMAND} -E make_directory "${output_dir}"
    COMMAND ${cargo_env} ${CARGO_EXECUTABLE} rustc --lib
      --locked --offline
      --manifest-path "${arg_MANIFEST_PATH}"
      --target-dir "${target_dir}"
      --release
      ${cargo_target_args}
      ${forced_config}
      -- ${rustflags}
    ${fold_commands}
    DEPENDS ${rust_sources} "${AWSLC_SOURCE_DIR}/cmake/rust_crate_object_fold.cmake"
    COMMENT "Building Rust staticlib ${arg_LIB_NAME} into ${output_name}"
    USES_TERMINAL
    VERBATIM)
endfunction()
