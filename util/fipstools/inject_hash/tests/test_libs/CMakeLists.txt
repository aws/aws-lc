if(FIPS AND APPLE)
    set(INJECT_HASH_TEST_LIB_COMPILE_OPTIONS
        "-Wno-unused-function"
        "-Wno-missing-prototypes"
        "-g0"
    )

    add_library(
        good_lib

        testlib.c
    )
    target_compile_options(good_lib PRIVATE ${INJECT_HASH_TEST_LIB_COMPILE_OPTIONS})

    add_library(
        bad_hash_lib

        testlib.c
    )
    target_compile_options(bad_hash_lib PRIVATE ${INJECT_HASH_TEST_LIB_COMPILE_OPTIONS})
    target_compile_definitions(bad_hash_lib PRIVATE "-DBAD_HASH")
endif()
