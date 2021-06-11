include_directories(../include)

add_executable(
  awslc

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

target_include_directories(awslc PUBLIC ${INCLUDE_DIR} ${INCLUDE_DIR}/internal/tool)
target_compile_options(awslc PUBLIC -DAWSLC_BENCHMARK)

add_dependencies(awslc global_target)

if(WIN32)
  target_link_libraries(awslc ws2_32)
endif()

if(APPLE OR WIN32 OR ANDROID)
  target_link_libraries(awslc ssl crypto)
  set(LIBRT_FLAGS "")
else()
  find_library(FOUND_LIBRT rt)
  if(FOUND_LIBRT)
    target_link_libraries(awslc ssl crypto -lrt)
    set(LIBRT_FLAGS "-lrt")
  else()
    target_link_libraries(awslc ssl crypto)
    set(LIBRT_FLAGS "")
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
  target_include_directories(${target_name} PUBLIC ${additional_include_dir} ${INCLUDE_DIR}/internal/tool)
  target_link_libraries(${target_name} ${lib_crypto} ${LIBRT_FLAGS})

  string(TOUPPER ${target_name} upper_target_name)
  target_compile_options(${target_name} PUBLIC -D${upper_target_name})
  install(TARGETS ${target_name}
          EXPORT ${target_name}-targets
          RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
          )
endfunction()

if(INCLUDE_DIR)
  build_benchmark(awslc_benchmark ${INCLUDE_DIR} crypto)
endif()

# This expects a directory which contains lib/libcrypto.a and the includes in include/openssl/*.h
if(OPENSSL_INSTALL_DIR)
  build_benchmark(openssl_benchmark ${OPENSSL_INSTALL_DIR}/include ${OPENSSL_INSTALL_DIR}/libcrypto.a)

  # libpthread is a linux only library
  if(NOT MSVC AND NOT ANDROID)
    # OpenSSL uses pthread_rwlock_unlock from pthread and  dlopen/close from dl
    target_link_libraries(openssl_benchmark pthread dl)
    # OpenSSL uses both anonymous structs and unions
    target_compile_options(openssl_benchmark PUBLIC -Wno-gnu-anonymous-struct -Wno-nested-anon-types)
  endif()
endif()

if(BORINGSSL_INSTALL_DIR)
  build_benchmark(boringssl_benchmark ${BORINGSSL_INSTALL_DIR}/include ${BORINGSSL_INSTALL_DIR}/build/crypto/libcrypto.a)

  # libpthread is a linux only library
  if(NOT MSVC AND NOT ANDROID)
    # BoringSSL uses pthread_rwlock_unlock from pthread
    target_link_libraries(boringssl_benchmark pthread)
    # BoringSSL uses both anonymous structs and unions
    target_compile_options(boringssl_benchmark PUBLIC -Wno-gnu-anonymous-struct -Wno-nested-anon-types)
  endif()
endif()

install(TARGETS awslc
        EXPORT awslc-targets
        RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
        )