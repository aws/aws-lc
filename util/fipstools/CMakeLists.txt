if(FIPS AND BUILD_TESTING)
  add_executable(
    test_fips

    test_fips.c
  )
  target_link_libraries(test_fips crypto)
endif()
