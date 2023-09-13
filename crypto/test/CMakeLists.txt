add_library(
  test_support_lib

  STATIC

  abi_test.cc
  file_test.cc
  malloc.cc
  test_util.cc
  wycheproof_util.cc
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
add_dependencies(test_support_lib boringssl_prefix_symbols)
target_include_directories(test_support_lib BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)

add_library(
  boringssl_gtest_main

  OBJECT

  gtest_main.cc
)

add_dependencies(boringssl_gtest_main global_target)
add_dependencies(boringssl_gtest_main boringssl_prefix_symbols)
target_include_directories(boringssl_gtest_main BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
