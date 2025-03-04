add_executable(
  bssl

  args.cc
  ciphers.cc
  client.cc
  const.cc
  digest.cc
  fd.cc
  file.cc
  generate_ech.cc
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

target_include_directories(bssl PUBLIC ${AWSLC_SOURCE_DIR}/include)
target_compile_options(bssl PUBLIC -DINTERNAL_TOOL)

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

target_include_directories(bssl BEFORE PRIVATE ${AWSLC_BINARY_DIR}/symbol_prefix_include)

install(TARGETS bssl
        RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
        BUNDLE DESTINATION ${CMAKE_INSTALL_BINDIR}
)

if(MSVC AND CMAKE_BUILD_TYPE_LOWER MATCHES "relwithdebinfo" AND FIPS)
  install (FILES $<TARGET_FILE_DIR:bssl>/bssl.pdb DESTINATION ${CMAKE_INSTALL_LIBDIR})
endif()

function(build_benchmark target_name install_path)
  find_library(libcrypto-${target_name} crypto PATHS ${install_path}/lib/ ${install_path}/lib64/ NO_DEFAULT_PATH)
  find_library(libdecrepit-${target_name} decrepit PATHS ${install_path}/lib/ ${install_path}/lib64/ NO_DEFAULT_PATH)
  message(STATUS "Building ${target_name} benchmark using header files from ${install_path}/include and libcrypto from ${libcrypto-${target_name}}.")
  add_executable(
          ${target_name}
          speed.cc
          args.cc
          const.cc
          benchmark.cc
  )
  # Link with the internal tool directory for shared headers with the rest of the tool instead of the top level AWS-LC
  # include directory
  target_include_directories(${target_name} PUBLIC ${install_path}/include ${AWSLC_INSTALL_DIR}/include/internal/tool)
  target_link_libraries(${target_name} ${libcrypto-${target_name}} ${LIBRT_FLAG})
  if (libdecrepit-${target_name})
    target_link_libraries(${target_name} ${libdecrepit-${target_name}})
  endif ()
  if(NOT MSVC AND NOT ANDROID)
    target_link_libraries(${target_name} pthread dl)
  endif()
  target_compile_options(${target_name} PUBLIC -Wno-deprecated-declarations)

endfunction()



if(BENCHMARK_LIBS)
  set(BENCHMARK_LIBS_STR ${BENCHMARK_LIBS} CACHE STRING "Libraries and paths")

  foreach(PAIR IN LISTS BENCHMARK_LIBS_STR)
    string(REPLACE ":" ";" PAIR_LIST ${PAIR})
    list(LENGTH PAIR_LIST PAIR_LENGTH)

    if(PAIR_LENGTH EQUAL 2)
      list(GET PAIR_LIST 0 NAME)
      list(GET PAIR_LIST 1 INSTALL_PATH)
      build_benchmark(${NAME} ${INSTALL_PATH})
    else()
      message(WARNING "Invalid benchmark pair: ${PAIR}, expected format: 'exectuable_name,/path/to/install/dir")
    endif()
  endforeach()
endif()

## Legacy options to build speed with a particular library. Use -DBENCHMARK_LIBS="name1,/path1;name2,/path2"
if(AWSLC_INSTALL_DIR)
  message(WARNING "Use of AWSLC_INSTALL_DIR is deprecated, the list option '-DBENCHMARK_LIBS=awslc_bm:/install/path' is recommended")
  build_benchmark(awslc_bm ${AWSLC_INSTALL_DIR})
endif()

# This expects a directory which contains the includes in include/openssl/ and the OpenSSL artifacts in lib/
# Currently this is the default OpenSSL build we target so the "OPENSSL_1_1_BENCHMARK" flag isn't used,
# but we include this to maintain uniformity across OpenSSL versions
if(OPENSSL_1_1_INSTALL_DIR)
  message(WARNING "Use of OPENSSL_1_1_INSTALL_DIR is deprecated, the list option '-DBENCHMARK_LIBS=awslc_bm:/install/path' is recommended")
  build_benchmark(ossl_1_1_bm ${OPENSSL_1_1_INSTALL_DIR})
endif()

# This expects a directory which contains the includes in include/openssl/ and the OpenSSL artifacts in lib/
if(OPENSSL_1_0_INSTALL_DIR)
  message(WARNING "Use of OPENSSL_1_0_INSTALL_DIR is deprecated, the list option '-DBENCHMARK_LIBS=awslc_bm:/install/path' is recommended")
  build_benchmark(ossl_1_0_bm ${OPENSSL_1_0_INSTALL_DIR})
endif()

# This expects a directory which contains the includes in include/openssl/ and the OpenSSL artifacts in lib/ or lib64/
if(OPENSSL_3_0_INSTALL_DIR)
  message(WARNING "Use of OPENSSL_3_0_INSTALL_DIR is deprecated, the list option '-DBENCHMARK_LIBS=awslc_bm:/install/path' is recommended")
  build_benchmark(ossl_3_0_bm ${OPENSSL_3_0_INSTALL_DIR})
  if(NOT MSVC)
    # The low-level function calls are deprecated for OpenSSL 3.0. We should revisit using these in the future,
    # but disabling the warnings works for now
    target_compile_options(ossl_3_0_bm PUBLIC -Wno-deprecated-declarations)

  endif ()
endif()

if(BORINGSSL_INSTALL_DIR)
  message(WARNING "Use of BORINGSSL_INSTALL_DIR is deprecated, the list option '-DBENCHMARK_LIBS=awslc_bm:/install/path' is recommended")
  build_benchmark(bssl_bm ${BORINGSSL_INSTALL_DIR})
endif()
