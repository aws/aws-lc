include_directories(${INCLUDE_DIR})

if(FIPS)
  add_executable(
    modulewrapper

    modulewrapper.cc
  )

  add_dependencies(modulewrapper global_target)

  target_link_libraries(modulewrapper crypto)
endif()
