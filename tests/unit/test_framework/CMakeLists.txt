include(${CONFIG_DIR}/perlasm.cmake)

if(${ARCH} STREQUAL "arm")
  set(
    TRAMPOLINE_ARCH_SOURCES

    trampoline-armv4.${ASM_EXT}
  )
endif()


if(${ARCH} STREQUAL "aarch64")
  set(
    TRAMPOLINE_ARCH_SOURCES

    trampoline-armv8.${ASM_EXT}
  )
endif()

if(${ARCH} STREQUAL "x86_64")
  set(
    TRAMPOLINE_ARCH_SOURCES

    trampoline-x86_64.${ASM_EXT}
  )
endif()

perlasm(trampoline-armv4.${ASM_EXT}  asm/trampoline-armv4.pl)
perlasm(trampoline-armv8.${ASM_EXT}  asm/trampoline-armv8.pl)
perlasm(trampoline-x86_64.${ASM_EXT} asm/trampoline-x86_64.pl)

add_library(
  test_support_lib

  STATIC

  abi_test.cc
  file_test.cc
  malloc.cc
  test_util.cc
  wycheproof_util.cc
  
  ${TRAMPOLINE_ARCH_SOURCES}
)

if (LIBUNWIND_FOUND)
  target_compile_options(test_support_lib PRIVATE ${LIBUNWIND_CFLAGS_OTHER})
  target_include_directories(test_support_lib PRIVATE ${LIBUNWIND_INCLUDE_DIRS})
  target_link_libraries(test_support_lib ${LIBUNWIND_LDFLAGS})
endif()
if(WIN32)
  target_link_libraries(test_support_lib dbghelp)
endif()
add_dependencies(test_support_lib global_target)

add_library(
  awslc_gtest_main

  OBJECT

  gtest_main.cc
)

add_dependencies(awslc_gtest_main global_target)
