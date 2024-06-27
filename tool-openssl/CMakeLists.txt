add_executable(
        openssl

        ../tool/args.cc
        ../tool/file.cc
        tool.cc
        x509.cc
)

target_include_directories(openssl PUBLIC ${PROJECT_SOURCE_DIR}/include)
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

target_include_directories(openssl BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)

install(TARGETS openssl
        RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
        BUNDLE DESTINATION ${CMAKE_INSTALL_BINDIR}
)

if(MSVC AND CMAKE_BUILD_TYPE_LOWER MATCHES "relwithdebinfo" AND FIPS)
    install (FILES $<TARGET_FILE_DIR:openssl>/openssl.pdb DESTINATION ${CMAKE_INSTALL_LIBDIR})
endif()

if(BUILD_TESTING)
    add_executable(
            x509_test

            x509_test.cc
            ../tool/args.cc
            ../tool/file.cc
            x509.cc
    )

    target_link_libraries(x509_test boringssl_gtest_main ssl crypto)
    add_dependencies(all_tests x509_test)
endif()
