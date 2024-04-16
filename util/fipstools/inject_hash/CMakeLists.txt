if(FIPS AND APPLE)
    add_executable(
        inject_hash

        inject_hash.c
        macho_parser/macho_parser.c
    )
endif()