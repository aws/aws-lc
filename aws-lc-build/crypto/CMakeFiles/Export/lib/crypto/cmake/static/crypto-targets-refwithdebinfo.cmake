#----------------------------------------------------------------
# Generated CMake target import file for configuration "RefWithDebInfo".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "pq_crypto" for configuration "RefWithDebInfo"
set_property(TARGET pq_crypto APPEND PROPERTY IMPORTED_CONFIGURATIONS REFWITHDEBINFO)
set_target_properties(pq_crypto PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_REFWITHDEBINFO "C"
  IMPORTED_LOCATION_REFWITHDEBINFO "${_IMPORT_PREFIX}/lib/libpq_crypto.a"
  )

list(APPEND _IMPORT_CHECK_TARGETS pq_crypto )
list(APPEND _IMPORT_CHECK_FILES_FOR_pq_crypto "${_IMPORT_PREFIX}/lib/libpq_crypto.a" )

# Import target "crypto" for configuration "RefWithDebInfo"
set_property(TARGET crypto APPEND PROPERTY IMPORTED_CONFIGURATIONS REFWITHDEBINFO)
set_target_properties(crypto PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_REFWITHDEBINFO "ASM;C"
  IMPORTED_LOCATION_REFWITHDEBINFO "${_IMPORT_PREFIX}/lib/libcrypto.a"
  )

list(APPEND _IMPORT_CHECK_TARGETS crypto )
list(APPEND _IMPORT_CHECK_FILES_FOR_crypto "${_IMPORT_PREFIX}/lib/libcrypto.a" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
