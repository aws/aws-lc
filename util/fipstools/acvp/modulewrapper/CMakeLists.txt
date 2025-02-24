if(FIPS)
  add_executable(
    modulewrapper

    main.cc
    modulewrapper.cc
  )
  target_link_libraries(modulewrapper crypto)
  target_include_directories(modulewrapper BEFORE PRIVATE ${AWSLC_BINARY_DIR}/symbol_prefix_include)
endif()
