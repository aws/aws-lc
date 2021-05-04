if(WIN32 OR UNIX OR APPLE)
    find_package(Threads REQUIRED)
endif()

if (BUILD_SHARED_LIBS)
    include(${CMAKE_CURRENT_LIST_DIR}/shared/crypto-targets.cmake)
else()
    include(${CMAKE_CURRENT_LIST_DIR}/static/crypto-targets.cmake)
endif()

