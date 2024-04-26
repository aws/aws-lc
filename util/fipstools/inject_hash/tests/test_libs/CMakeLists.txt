if(FIPS AND APPLE)
    add_library(
        good_lib

        good_lib.c
    )
    target_compile_options(good_lib PRIVATE "-Wno-unused-function" "-Wno-missing-prototypes" "-g0")
endif()