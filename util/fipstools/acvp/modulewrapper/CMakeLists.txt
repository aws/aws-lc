include_directories(../../../../include)

if(FIPS)
  add_executable(
    modulewrapper

    main.cc
    modulewrapper.cc
  )

  if(MSVC)
    # If we're building for MSVC then we want to enable the /DEBUG:FULL flag for the debug symbols
    set_property(TARGET modulewrapper APPEND PROPERTY LINK_FLAGS /DEBUG:FULL)
  endif()

  add_dependencies(modulewrapper global_target)

  target_link_libraries(modulewrapper crypto)
endif()
