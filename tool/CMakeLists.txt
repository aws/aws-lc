
add_executable(
  bssl

  args.cc
  ciphers.cc
  client.cc
  const.cc
  digest.cc
  fd.cc
  file.cc
  generate_ed25519.cc
  genrsa.cc
  pkcs12.cc
  rand.cc
  server.cc
  sign.cc
  speed.cc
  tool.cc
  transport_common.cc
)

target_include_directories(bssl PUBLIC ${AWSLC_INSTALL_DIR}/include ${AWSLC_INSTALL_DIR}/include/internal/tool)

add_dependencies(bssl global_target)

if(WIN32)
  target_link_libraries(bssl ws2_32)
endif()

if(APPLE OR WIN32 OR ANDROID)
  target_link_libraries(bssl ssl crypto)
  set(LIBRT_FLAG "")
else()
  find_library(FOUND_LIBRT rt)
  if(FOUND_LIBRT)
    target_link_libraries(bssl ssl crypto -lrt)
    set(LIBRT_FLAG "-lrt")
  else()
    target_link_libraries(bssl ssl crypto)
    set(LIBRT_FLAG "")
  endif()
endif()

function(build_benchmark target_name additional_include_dir lib_crypto)
  message(${additional_include_dir})
  add_executable(
          ${target_name}
          speed.cc
          args.cc
          const.cc
          benchmark.cc
  )
  # Link with the internal tool directory for shared headers with the rest of the tool instead of the top level AWS-LC
  # include directory
  target_include_directories(${target_name} PUBLIC ${additional_include_dir} ${AWSLC_INSTALL_DIR}/include/internal/tool)
  target_link_libraries(${target_name} ${lib_crypto} ${LIBRT_FLAG})
endfunction()

if(AWSLC_INSTALL_DIR)
  build_benchmark(awslc_bm ${AWSLC_INSTALL_DIR}/include crypto)
endif()

# This expects a directory which contains the includes are in include/openssl/*.h and the OpenSSL artifacts in build/
if(OPENSSL_INSTALL_DIR)
  build_benchmark(ossl_bm ${OPENSSL_INSTALL_DIR}/include ${OPENSSL_INSTALL_DIR}/build/lib/libcrypto.a)

  if(NOT MSVC AND NOT ANDROID)
    # OpenSSL uses pthread_rwlock_unlock from pthread and  dlopen/close from dl
    target_link_libraries(ossl_bm -DOPENSSL_BENCHMARK pthread dl)

    target_compile_options(ossl_bm PUBLIC -DOPENSSL_BENCHMARK)
  endif()
endif()

# This expects a directory in which the includes are in include/ and the BoringSSL artifacts are in build/
if(BORINGSSL_INSTALL_DIR)
  build_benchmark(bssl_bm ${BORINGSSL_INSTALL_DIR}/include ${BORINGSSL_INSTALL_DIR}/build/crypto/libcrypto.a)

  if(NOT MSVC AND NOT ANDROID)
    # BoringSSL uses pthread_rwlock_unlock from pthread
    target_link_libraries(bssl_bm pthread)
  endif()
endif()

