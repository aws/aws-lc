include_directories(../include)

add_library(
  ssl

  bio_ssl.cc
  d1_both.cc
  d1_lib.cc
  d1_pkt.cc
  d1_srtp.cc
  dtls_method.cc
  dtls_record.cc
  encrypted_client_hello.cc
  handoff.cc
  handshake.cc
  handshake_client.cc
  handshake_server.cc
  s3_both.cc
  s3_lib.cc
  s3_pkt.cc
  ssl_aead_ctx.cc
  ssl_asn1.cc
  ssl_buffer.cc
  ssl_cert.cc
  ssl_cipher.cc
  ssl_file.cc
  ssl_key_share.cc
  ssl_lib.cc
  ssl_privkey.cc
  ssl_session.cc
  ssl_stat.cc
  ssl_transcript.cc
  ssl_versions.cc
  ssl_x509.cc
  t1_enc.cc
  t1_lib.cc
  tls_method.cc
  tls_record.cc
  tls13_both.cc
  tls13_client.cc
  tls13_enc.cc
  tls13_server.cc
)

add_dependencies(ssl global_target)

target_link_libraries(ssl crypto)

target_include_directories(ssl SYSTEM PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../include>
  $<INSTALL_INTERFACE:include>)

if(BUILD_TESTING)
  add_executable(
    ssl_test

    span_test.cc
    ssl_test.cc
    ssl_c_test.c

    $<TARGET_OBJECTS:boringssl_gtest_main>
  )

  add_dependencies(ssl_test global_target)

  target_link_libraries(ssl_test test_support_lib boringssl_gtest ssl crypto)
  if(WIN32)
    target_link_libraries(ssl_test ws2_32)
  endif()
  add_dependencies(all_tests ssl_test)
  add_subdirectory(test)
endif()

install(TARGETS ssl
        EXPORT ssl-targets
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
)

configure_file("cmake/ssl-config.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/ssl-config.cmake"
    @ONLY)

install(FILES "${CMAKE_CURRENT_BINARY_DIR}/ssl-config.cmake"
    DESTINATION "${CMAKE_INSTALL_LIBDIR}/ssl/cmake"
    COMPONENT Development)

if (BUILD_SHARED_LIBS)
   set (TARGET_DIR "shared")
else()
   set (TARGET_DIR "static")
endif()

install(EXPORT ssl-targets
    DESTINATION "${CMAKE_INSTALL_LIBDIR}/ssl/cmake/${TARGET_DIR}"
    COMPONENT Development)
