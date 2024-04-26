if(FIPS AND APPLE)
    add_subdirectory(test_libs)

    add_executable(
        test_inject_hash

        inject_hash_tests.cc
        ../inject_hash_lib.c
        ../macho_parser/macho_parser.c
    )

    target_link_libraries(
        test_inject_hash

        test_support_lib
        boringssl_gtest_main
    )
endif()
