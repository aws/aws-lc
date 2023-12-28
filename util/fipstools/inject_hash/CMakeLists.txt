if(FIPS AND APPLE)
  add_executable(
    inject_hash

    inject_hash.c
    macho_parser.c
  )
  target_link_libraries(inject_hash fips_hashing)
endif()
