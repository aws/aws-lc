add_definitions(-DOPENSSL_NO_ASM)
remove_definitions(-DBORINGSSL_FIPS -DFIPS_ENTROPY_SOURCE_JITTER_CPU -DFIPS_ENTROPY_SOURCE_PASSIVE)

set(BCM_ASM_SOURCES_FIPS_HASHING "")

foreach(file ${BCM_ASM_SOURCES})
  set(modified_file "../${file}")
  list(APPEND BCM_ASM_SOURCES_FIPS_HASHING ${modified_file})
endforeach()

add_custom_target(BCM_SOURCES_HASHING_TARGET DEPENDS ${BCM_ASM_SOURCES_FIPS_HASHING})

# Create a non-FIPS version of bcm_library for use in a non-FIPS libcrypto so inject_hash can use it for hashing
add_library(
    nofipsmodule

    OBJECT

    ../bcm.c
    ../fips_shared_support.c
    ../cpucap/cpucap.c

    # ${BCM_ASM_SOURCES_FIPS_HASHING}
)
target_compile_definitions(nofipsmodule PRIVATE BORINGSSL_IMPLEMENTATION)
add_dependencies(nofipsmodule BCM_SOURCES_HASHING_TARGET)

add_dependencies(nofipsmodule boringssl_prefix_symbols)
target_include_directories(nofipsmodule BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
target_include_directories(nofipsmodule PRIVATE ${PROJECT_SOURCE_DIR}/include)