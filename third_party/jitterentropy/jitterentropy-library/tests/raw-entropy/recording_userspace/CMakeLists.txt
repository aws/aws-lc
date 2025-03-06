cmake_minimum_required(VERSION 3.14)

project(jitterentropy C)
set(CMAKE_C_STANDARD 99)

function(testprogram name)
    add_executable(${name} ${name}.c)
    target_link_libraries(${name} ${PROJECT_NAME})
    target_link_directories(${name} PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../../../build>)
    target_include_directories(${name} PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../../..>
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../../../src>)
    if(NOT MSVC)
        target_compile_options(${name} PRIVATE -fwrapv --param ssp-buffer-size=4 -fvisibility=hidden -Wcast-align -Wmissing-field-initializers -Wshadow -Wswitch-enum -Wextra -Wall -pedantic -O0 -fwrapv -Wconversion)
    endif()
    include(GNUInstallDirs)
    install(TARGETS ${name})
endfunction()

testprogram(jitterentropy-hashtime)
