# The AWS-LC OpenSSL provider. Off by default: it needs OpenSSL's provider
# headers, which AWS-LC's own tree does not carry.

if(NOT AWSLC_PROVIDER_OPENSSL_ROOT)
  message(FATAL_ERROR
    "BUILD_AWSLC_PROVIDER requires AWSLC_PROVIDER_OPENSSL_ROOT, the install "
    "prefix of an OpenSSL 3.5 or later build supplying the provider headers.")
endif()

find_path(AWSLC_PROVIDER_OPENSSL_INCLUDE_DIR
  NAMES openssl/core_dispatch.h
  PATHS "${AWSLC_PROVIDER_OPENSSL_ROOT}/include"
  NO_DEFAULT_PATH)

if(NOT AWSLC_PROVIDER_OPENSSL_INCLUDE_DIR)
  message(FATAL_ERROR
    "openssl/core_dispatch.h not found under "
    "${AWSLC_PROVIDER_OPENSSL_ROOT}/include. AWSLC_PROVIDER_OPENSSL_ROOT must "
    "point at the install prefix of an OpenSSL 3.5 or later build.")
endif()

# Check the version for a 3.5 minimum, not just that the header exists.
file(STRINGS "${AWSLC_PROVIDER_OPENSSL_INCLUDE_DIR}/openssl/opensslv.h"
  AWSLC_PROVIDER_OPENSSL_VERSION_LINE
  REGEX "^# *define +OPENSSL_VERSION_STR +\"[0-9.]+\"")
string(REGEX MATCH "[0-9]+\\.[0-9]+\\.[0-9]+"
  AWSLC_PROVIDER_OPENSSL_VERSION "${AWSLC_PROVIDER_OPENSSL_VERSION_LINE}")

if(NOT AWSLC_PROVIDER_OPENSSL_VERSION)
  message(WARNING
    "Could not determine the OpenSSL version at "
    "${AWSLC_PROVIDER_OPENSSL_ROOT}; the provider needs 3.5 or later.")
elseif(AWSLC_PROVIDER_OPENSSL_VERSION VERSION_LESS "3.5")
  message(FATAL_ERROR
    "The provider requires OpenSSL 3.5 or later; found "
    "${AWSLC_PROVIDER_OPENSSL_VERSION} at ${AWSLC_PROVIDER_OPENSSL_ROOT}.")
else()
  message(STATUS "aws-lc-provider: building against OpenSSL "
    "${AWSLC_PROVIDER_OPENSSL_VERSION}")
endif()

# This target exposes only a deliberately unimplemented entry point.
add_library(awslc_provider MODULE frontend/provider.c)
# Replace the directory-level AWS-LC include paths inherited from the parent.
# OpenSSL and AWS-LC both provide openssl/* headers, and the frontend must see
# only OpenSSL's definitions.
set_property(TARGET awslc_provider PROPERTY INCLUDE_DIRECTORIES
  "${AWSLC_PROVIDER_OPENSSL_INCLUDE_DIR}")
set_target_properties(awslc_provider PROPERTIES
  C_VISIBILITY_PRESET hidden
  OUTPUT_NAME "awslc"
  PREFIX "")

if(APPLE)
  # OpenSSL's module loader appends .dylib on macOS, while CMake normally gives
  # a MODULE library the .so suffix.
  set_target_properties(awslc_provider PROPERTIES SUFFIX ".dylib")
endif()

if(APPLE)
  target_link_options(awslc_provider PRIVATE "-Wl,-undefined,dynamic_lookup")
endif()
