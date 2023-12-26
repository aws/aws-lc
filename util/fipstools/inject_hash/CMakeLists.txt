if(FIPS)
  add_executable(
    inject_hash

    inject_hash.c
    macho_parser.c
  )
  # target_link_libraries(inject_hash crypto)
  target_include_directories(inject_hash BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
endif()
