if(USE_CPP_INJECT_HASH)
    add_executable(inject_hash_cpp
        inject_hash.cpp
    )

    target_include_directories(inject_hash_cpp PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_CURRENT_BINARY_DIR}
        ${CMAKE_SOURCE_DIR}/include
    )
    
    # due to aws-lc's nature of converting every warning into an error,
    # we need to disable some warnings that are coming from the LIEF submodule
    if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
        target_compile_options(inject_hash_cpp PRIVATE
            -Wno-overloaded-virtual
            -Wno-unused-parameter
        )
    endif()

    target_link_libraries(inject_hash_cpp PRIVATE
        LIEF::LIEF
    )

    set_target_properties(inject_hash_cpp PROPERTIES
        CXX_STANDARD 17
        CXX_STANDARD_REQUIRED ON
    )
endif()