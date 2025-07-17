if(FIPS AND BUILD_TESTING)
  add_executable(
    test_fips

    test_fips.c
  )
  target_link_libraries(test_fips crypto)
  target_add_awslc_include_paths(test_fips PRIVATE)

  add_subdirectory(inject_hash/macho_parser/tests)
endif()
