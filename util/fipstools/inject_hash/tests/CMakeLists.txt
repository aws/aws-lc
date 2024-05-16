if(FIPS AND APPLE)
    add_subdirectory(test_libs)

    add_executable(
        test_inject_hash

        inject_hash_tests.cc
        ../inject_hash_lib.c
        ../macho_parser/macho_parser.c
    )
    add_dependencies(
        test_inject_hash
        
        good_lib
        bad_hash_lib
        bad_marker_lib
    )

    target_link_libraries(
        test_inject_hash

        test_support_lib
        boringssl_gtest_main
    )
endif()
