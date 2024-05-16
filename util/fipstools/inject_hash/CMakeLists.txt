if(FIPS AND APPLE)
    add_executable(
        inject_hash

        inject_hash.c
        inject_hash_lib.c
        macho_parser/macho_parser.c
    )
    target_link_libraries(inject_hash PUBLIC fips_hashing)
    target_include_directories(inject_hash PRIVATE ${PROJECT_SOURCE_DIR}/include)
endif()
