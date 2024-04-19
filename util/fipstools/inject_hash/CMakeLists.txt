if(FIPS AND APPLE)
    add_executable(
        inject_hash

        inject_hash.c
        macho_parser/macho_parser.c
    )
    target_link_libraries(
        inject_hash
        
        fips_hashing
    )
    target_include_directories(inject_hash PRIVATE ${PROJECT_SOURCE_DIR}/include)

    set(INJECT_HASH_APPLE_FLAG "-f")
    add_custom_command(
      OUTPUT crypto POST_BUILD
      COMMAND ${PROJECT_BINARY_DIR}/crypto/inject_hash/inject_hash
      -p $<TARGET_FILE:crypto> -o $<TARGET_FILE:crypto> ${INJECT_HASH_APPLE_FLAG}
      DEPENDS inject_hash
      WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
    )
endif()