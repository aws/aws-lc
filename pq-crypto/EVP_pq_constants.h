//
// Created by lamjyoti on 8/11/2021.
//

#ifndef AWSLC_EVP_PQ_CONSTANTS_H
#define AWSLC_EVP_PQ_CONSTANTS_H


/* TLDR s2n: 0=true, -1=false,
 * TLDR aws-lc: 1=true, 0=false
 * current work around to keep following macros */
/* A value which indicates the outcome of a function */
#define EVP_PQ_SUCCESS 1
#define EVP_PQ_FAILURE 0

#define IN /* Indicates a necessary function input */
#define OUT /* Indicates a function output */


// Proposed work around for POSIX_GUARD and POSIX_GUARD_RESULT:
// Currently simplified to only two macros 1 (pass) and 0 (fail)
#define POSIX_GUARD(result) __EVP_ENSURE((result) == EVP_PQ_SUCCESS, return EVP_PQ_FAILURE)

/**
 * Ensures `cond` is true, otherwise `action` will be performed
 */
#define __EVP_ENSURE( cond, action ) do {if ( !(cond) ) { action; }} while (0)



/* SIKE PQ Algorithm Constants */
#define SIKE_P434_R3_PUBLIC_KEY_BYTES 330
#define SIKE_P434_R3_PRIVATE_KEY_BYTES 374
#define SIKE_P434_R3_CIPHERTEXT_BYTES 346
#define SIKE_P434_R3_SHARED_SECRET_BYTES 16


#endif  // AWSLC_EVP_PQ_CONSTANTS_H
