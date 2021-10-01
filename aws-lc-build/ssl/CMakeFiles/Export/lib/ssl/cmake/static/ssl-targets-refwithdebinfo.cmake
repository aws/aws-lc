#----------------------------------------------------------------
# Generated CMake target import file for configuration "RefWithDebInfo".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "ssl" for configuration "RefWithDebInfo"
set_property(TARGET ssl APPEND PROPERTY IMPORTED_CONFIGURATIONS REFWITHDEBINFO)
set_target_properties(ssl PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_REFWITHDEBINFO "CXX"
  IMPORTED_LOCATION_REFWITHDEBINFO "${_IMPORT_PREFIX}/lib/libssl.a"
  )

list(APPEND _IMPORT_CHECK_TARGETS ssl )
list(APPEND _IMPORT_CHECK_FILES_FOR_ssl "${_IMPORT_PREFIX}/lib/libssl.a" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
