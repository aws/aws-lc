include(CMakeFindDependencyMacro)

find_dependency(crypto)

if (BUILD_SHARED_LIBS)
    include(${CMAKE_CURRENT_LIST_DIR}/shared/ssl-targets.cmake)
else()
    include(${CMAKE_CURRENT_LIST_DIR}/static/ssl-targets.cmake)
endif()
