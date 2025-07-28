if(FIPS)
  add_definitions(-DOPENSSL_NO_ASM=1)
  remove_definitions(-DBORINGSSL_FIPS -DFIPS_ENTROPY_SOURCE_JITTER_CPU -DFIPS_ENTROPY_SOURCE_PASSIVE)

  add_library(
    fips_hashing
    
    STATIC

    fips_hashing.c

    ../mem.c
    ../thread_none.c
    ../thread_pthread.c

    ../err/err.c
    $<TARGET_OBJECTS:generated_err_data>
    ../decrepit/ripemd/ripemd.c
  )

  SET_TARGET_PROPERTIES(fips_hashing PROPERTIES LINKER_LANGUAGE C)
  target_include_directories(fips_hashing PUBLIC $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/include>)
endif()
