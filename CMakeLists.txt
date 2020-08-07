cmake_minimum_required(VERSION 2.8.12)

project(AWSLC NONE)

include(cmake/apply-quilt-patches.cmake)
add_subdirectory(third_party/boringssl)

# Copy awslc-config.cmake to build artifacts. 
configure_file("cmake/awslc-config.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/awslc-config.cmake"
    @ONLY)

install(FILES "${CMAKE_CURRENT_BINARY_DIR}/awslc-config.cmake"
    DESTINATION "${CMAKE_INSTALL_LIBDIR}/${PROJECT_NAME}/cmake/"
    COMPONENT Development)
