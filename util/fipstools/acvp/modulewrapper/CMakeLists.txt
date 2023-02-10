include_directories(../../../../include)

if(FIPS)
  add_executable(
    modulewrapper

    main.cc
    modulewrapper.cc
  )

  if(MSVC)
    # If we're building for MSVC then we want to enable the /DEBUG:FULL flag for the debug symbols
    # This isn't the same as building in 'debug' mode, but instead generates .pdb files that allow debugging of release code.
    target_link_options(modulewrapper PUBLIC /DEBUG:FULL)
  endif()

  add_dependencies(modulewrapper global_target)

  target_link_libraries(modulewrapper crypto)
endif()
