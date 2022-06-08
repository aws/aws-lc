if(WIN32 OR UNIX OR APPLE)
    find_package(Threads REQUIRED)
endif()

if (BUILD_SHARED_LIBS)
    message(STATUS "FOUND AWS-LC CRYPTO cmake config - shared")
    include(${CMAKE_CURRENT_LIST_DIR}/shared/crypto-targets.cmake)
else()
    message(STATUS "FOUND AWS-LC CRYPTO cmake config - static")
    include(${CMAKE_CURRENT_LIST_DIR}/static/crypto-targets.cmake)
endif()

