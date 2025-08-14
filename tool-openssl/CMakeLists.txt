add_executable(
    openssl

    ../tool/args.cc
    ../tool/file.cc
    ../tool/fd.cc
    ../tool/client.cc
    ../tool/transport_common.cc

    crl.cc
    dgst.cc
    pkcs8.cc
    pkey.cc
    rehash.cc
    req.cc
    ordered_args.cc
    rsa.cc
    s_client.cc
    tool.cc
    verify.cc
    version.cc
    x509.cc
)

target_compile_options(openssl PUBLIC -DINTERNAL_TOOL)

if(WIN32)
    target_link_libraries(openssl ws2_32)
endif()

if(APPLE OR WIN32 OR ANDROID)
    target_link_libraries(openssl ssl crypto)
    set(LIBRT_FLAG "")
else()
    find_library(FOUND_LIBRT rt)
    if(FOUND_LIBRT)
        target_link_libraries(openssl ssl crypto -lrt)
        set(LIBRT_FLAG "-lrt")
    else()
        target_link_libraries(openssl ssl crypto)
        set(LIBRT_FLAG "")
    endif()
endif()

target_add_awslc_include_paths(TARGET openssl SCOPE PRIVATE)

install(TARGETS openssl
        RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
        BUNDLE DESTINATION ${CMAKE_INSTALL_BINDIR}
)

file(INSTALL
    ${CMAKE_CURRENT_SOURCE_DIR}/c_rehash.sh
    DESTINATION
    ${CMAKE_CURRENT_BINARY_DIR}
    NO_SOURCE_PERMISSIONS
    FILE_PERMISSIONS
    OWNER_READ OWNER_WRITE OWNER_EXECUTE
    GROUP_READ GROUP_EXECUTE
    WORLD_READ WORLD_EXECUTE
    RENAME
    c_rehash
)

install(
    PROGRAMS ${CMAKE_CURRENT_SOURCE_DIR}/c_rehash.sh
    RENAME c_rehash
    DESTINATION ${CMAKE_INSTALL_BINDIR}
)

if(MSVC AND CMAKE_BUILD_TYPE_LOWER MATCHES "relwithdebinfo" AND FIPS)
    install (FILES $<TARGET_FILE_DIR:openssl>/openssl.pdb DESTINATION ${CMAKE_INSTALL_LIBDIR})
endif()

if(BUILD_TESTING)
    add_executable(
        tool_openssl_test

        ../tool/args.cc
        ../tool/file.cc
        ../tool/fd.cc
        ../crypto/test/test_util.cc
        ../tool/client.cc
        ../tool/transport_common.cc

        crl.cc
        crl_test.cc
        dgst.cc
        dgst_test.cc
        pkcs8.cc
        pkcs8_test.cc
        pkey.cc
        pkey_test.cc
        rehash.cc
        rehash_test.cc
        req.cc
        req_test.cc
        rsa.cc
        rsa_test.cc
        s_client.cc
        ordered_args.cc
        verify.cc
        verify_test.cc
        x509.cc
        x509_test.cc
    )

    target_add_awslc_include_paths(TARGET tool_openssl_test SCOPE PRIVATE)

    file(INSTALL
            ${CMAKE_CURRENT_SOURCE_DIR}/c_rehash_test.sh
            DESTINATION
            ${CMAKE_CURRENT_BINARY_DIR}
            NO_SOURCE_PERMISSIONS
            FILE_PERMISSIONS
            OWNER_READ OWNER_WRITE OWNER_EXECUTE
            GROUP_READ GROUP_EXECUTE
            WORLD_READ WORLD_EXECUTE
            RENAME
            c_rehash_test
    )

    target_link_libraries(tool_openssl_test boringssl_gtest_main ssl crypto)
    add_dependencies(all_tests tool_openssl_test)
    add_dependencies(tool_openssl_test openssl)
    set_test_location(tool_openssl_test)
endif()
