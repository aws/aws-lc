if(FIPS AND APPLE)
    add_subdirectory(macho_parser/tests)

    add_executable(
        inject_hash

        inject_hash.c
        macho_parser/macho_parser.c
    )
endif()