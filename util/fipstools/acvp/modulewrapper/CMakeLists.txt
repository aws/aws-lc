include_directories(../../../../include)

if(FIPS)
  add_executable(
    modulewrapper

    main.cc
    modulewrapper.cc
  )

  add_dependencies(modulewrapper global_target)

  target_link_libraries(modulewrapper crypto)
  target_include_directories(modulewrapper BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
endif()
