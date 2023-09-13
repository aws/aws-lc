include_directories(../../include)

if(FIPS AND BUILD_TESTING)
  add_executable(
    test_fips

    test_fips.c
  )

  add_dependencies(test_fips global_target)
  target_link_libraries(test_fips crypto)
  target_include_directories(test_fips BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
endif()
