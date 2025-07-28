if(FIPS AND BUILD_TESTING)
  add_executable(
    test_fips

    test_fips.c
  )
  target_link_libraries(test_fips crypto)
  target_include_directories(test_fips BEFORE PRIVATE ${AWSLC_BINARY_DIR}/symbol_prefix_include)

  add_subdirectory(inject_hash/macho_parser/tests)
endif()
