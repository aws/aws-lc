add_definitions(-DOPENSSL_NO_ASM=1)
remove_definitions(-DBORINGSSL_FIPS -DFIPS_ENTROPY_SOURCE_JITTER_CPU -DFIPS_ENTROPY_SOURCE_PASSIVE)

set(FIPS_HASHING_CRYPTO_OBJS "")

foreach(file ${CRYPTO_OBJ_SOURCES})
  set(modified_file "../${file}")
  list(APPEND FIPS_HASHING_CRYPTO_OBJS ${modified_file})
endforeach()

set(GENERATE_CODE_ROOT "${PROJECT_SOURCE_DIR}/generated-src")
file(COPY ${GENERATE_CODE_ROOT}/err_data.c DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/)

add_library(
  clean_crypto_objects
  OBJECT
  ${FIPS_HASHING_CRYPTO_OBJS}
#   ${DILITHIUM_SOURCES}
#   ${CRYPTO_ARCH_SOURCES}
  err_data.c
)

target_compile_definitions(clean_crypto_objects PRIVATE BORINGSSL_IMPLEMENTATION)
# For the prefix build, the object files need the prefix header files to build.
add_dependencies(clean_crypto_objects boringssl_prefix_symbols)
target_include_directories(clean_crypto_objects BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
target_include_directories(clean_crypto_objects PRIVATE ${PROJECT_SOURCE_DIR}/include)
add_library(fips_hashing $<TARGET_OBJECTS:clean_crypto_objects>)

SET_TARGET_PROPERTIES(fips_hashing PROPERTIES LINKER_LANGUAGE C)
target_link_libraries(fips_hashing PUBLIC nofipsmodule pthread)

add_dependencies(fips_hashing boringssl_prefix_symbols)
target_include_directories(fips_hashing BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)

target_include_directories(fips_hashing PUBLIC
        $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>)
