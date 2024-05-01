if(FIPS AND APPLE)
    set(INJECT_HASH_TEST_LIB_COMPILE_OPTIONS
        "-Wno-unused-function"
        "-Wno-missing-prototypes"
        "-g0"
    )

    function(create_test_lib name)
        add_library(${name} testlib.c)
        target_compile_options(${name} PRIVATE ${INJECT_HASH_TEST_LIB_COMPILE_OPTIONS})

        if(NOT "${ARGN}" STREQUAL "")
            target_compile_definitions(${name} PRIVATE ${ARGN})
        endif()
    endfunction()

    create_test_lib(good_lib)
    create_test_lib(bad_hash_lib "-DBAD_HASH")
    create_test_lib(bad_marker_lib "-DBAD_MARKER")
endif()
