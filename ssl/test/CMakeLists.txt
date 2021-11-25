include_directories(../../include)

add_executable(
  bssl_shim

  async_bio.cc
  bssl_shim.cc
  handshake_util.cc
  mock_quic_transport.cc
  packeted_bio.cc
  settings_writer.cc
  test_config.cc
  test_state.cc
)

add_dependencies(bssl_shim global_target)

target_link_libraries(bssl_shim test_support_lib ssl crypto)
if(WIN32)
  target_link_libraries(bssl_shim ws2_32)
endif()

# TODO: reenable below test or delete after testing the decoded SSL in runner.
# add_executable(
#   ssl_conn_transfer

#   ssl_conn_transfer.c
# )

# add_dependencies(ssl_conn_transfer global_target)

# target_link_libraries(ssl_conn_transfer ssl crypto)

if(UNIX AND NOT APPLE AND NOT ANDROID)
  add_executable(
    handshaker

    async_bio.cc
    handshake_util.cc
    handshaker.cc
    mock_quic_transport.cc
    packeted_bio.cc
    settings_writer.cc
    test_config.cc
    test_state.cc
  )

  add_dependencies(handshaker global_target)

  target_link_libraries(handshaker test_support_lib ssl crypto)
else()
  # Declare a dummy target for run_tests to depend on.
  add_custom_target(handshaker)
endif()
