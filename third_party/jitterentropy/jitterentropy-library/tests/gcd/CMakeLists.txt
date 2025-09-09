add_executable(gcd gcd.c)
target_include_directories(gcd PRIVATE ../../src)
target_link_libraries(gcd ${PROJECT_NAME})
