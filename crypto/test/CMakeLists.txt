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
target_link_libraries(test_support_lib boringssl_gtest crypto)

target_include_directories(test_support_lib BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)

add_library(boringssl_gtest_main STATIC gtest_main.cc)
target_link_libraries(boringssl_gtest_main boringssl_gtest crypto test_support_lib)
target_include_directories(boringssl_gtest_main BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
