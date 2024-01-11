if(FIPS AND APPLE)
  add_executable(
    test_macho_parser

    macho_tests.c
    ../macho_parser.c
  )
endif()
