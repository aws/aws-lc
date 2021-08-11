/********************************************************************************************
* Supersingular Isogeny Key Encapsulation Library
*
* Abstract: supersingular isogeny key encapsulation (SIKE) protocol
*********************************************************************************************/

#include <stdio.h>
#include <string.h>
#include "sikep434r3.h"
#include "sikep434r3_fips202.h"
/*#include "utils/s2n_safety.h"
#include "pq-crypto/s2n_pq.h"
#include "pq-crypto/s2n_pq_random.h"
 delete later - line separator convert CRLF to LF
 */
#include "../../crypto/internal.h"  // for constant time function
#include "sikep434r3_temp_kem.h"
#include "../../include/openssl/rand.h" // generate random bytes
#include "sikep434r3_api.h"
#include "sikep434r3_fpx.h"
//#include "tls/s2n_kem.h"

/* SIKE's key generation
 * Outputs: secret key sk (S2N_SIKE_P434_R3_SECRET_KEY_BYTES = S2N_SIKE_P434_R3_MSG_BYTES + S2N_SIKE_P434_R3_SECRETKEY_B_BYTES + S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
 *          public key pk (S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES bytes) */
int s2n_sike_p434_r3_crypto_kem_keypair(unsigned char *pk, unsigned char *sk)
{
    // Should not be managed by awslc pq
    //POSIX_ENSURE(s2n_pq_is_enabled(), S2N_ERR_PQ_DISABLED);

    /* Generate lower portion of secret key sk <- s||SK
    POSIX_GUARD_RESULT(s2n_get_random_bytes(sk, S2N_SIKE_P434_R3_MSG_BYTES));
    POSIX_GUARD(random_mod_order_B(sk + S2N_SIKE_P434_R3_MSG_BYTES)); */

    /* Generate lower portion of secret key sk <- s||SK */
    POSIX_GUARD(RAND_bytes(sk, SIKE_P434_R3_MSG_BYTES));
    POSIX_GUARD(random_mod_order_B(sk + SIKE_P434_R3_MSG_BYTES));

    /* Generate public key pk */
    EphemeralKeyGeneration_B(sk + SIKE_P434_R3_MSG_BYTES, pk);

    /* Append public key pk to secret key sk */
    memcpy(&sk[SIKE_P434_R3_MSG_BYTES + SIKE_P434_R3_SECRETKEY_B_BYTES], pk, SIKE_P434_R3_PUBLIC_KEY_BYTES);

    return S2N_SUCCESS;
}

/* SIKE's encapsulation
 * Input:   public key pk         (S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
 * Outputs: shared secret ss      (S2N_SIKE_P434_R3_SHARED_SECRET_BYTES bytes)
 *          ciphertext message ct (S2N_SIKE_P434_R3_CIPHERTEXT_BYTES = S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES + S2N_SIKE_P434_R3_MSG_BYTES bytes) */
int s2n_sike_p434_r3_crypto_kem_enc(unsigned char *ct, unsigned char *ss, const unsigned char *pk)
{
    //POSIX_ENSURE(s2n_pq_is_enabled(), S2N_ERR_PQ_DISABLED);

    unsigned char ephemeralsk[SIKE_P434_R3_SECRETKEY_A_BYTES];
    unsigned char jinvariant[SIKE_P434_R3_FP2_ENCODED_BYTES];
    unsigned char h[SIKE_P434_R3_MSG_BYTES];
    unsigned char temp[SIKE_P434_R3_CIPHERTEXT_BYTES+SIKE_P434_R3_MSG_BYTES];

    /* Generate ephemeralsk <- G(m||pk) mod oA */
    //POSIX_GUARD_RESULT(s2n_get_random_bytes(temp, S2N_SIKE_P434_R3_MSG_BYTES));
    POSIX_GUARD(RAND_bytes(temp, SIKE_P434_R3_MSG_BYTES));
    memcpy(&temp[SIKE_P434_R3_MSG_BYTES], pk, SIKE_P434_R3_PUBLIC_KEY_BYTES);
    shake256(ephemeralsk, SIKE_P434_R3_SECRETKEY_A_BYTES, temp, SIKE_P434_R3_PUBLIC_KEY_BYTES+SIKE_P434_R3_MSG_BYTES);
    ephemeralsk[SIKE_P434_R3_SECRETKEY_A_BYTES - 1] &= SIKE_P434_R3_MASK_ALICE;

    /* Encrypt */
    EphemeralKeyGeneration_A(ephemeralsk, ct);
    EphemeralSecretAgreement_A(ephemeralsk, pk, jinvariant);
    shake256(h, SIKE_P434_R3_MSG_BYTES, jinvariant, SIKE_P434_R3_FP2_ENCODED_BYTES);
    for (int i = 0; i < SIKE_P434_R3_MSG_BYTES; i++) {
        ct[i + SIKE_P434_R3_PUBLIC_KEY_BYTES] = temp[i] ^ h[i];
    }

    /* Generate shared secret ss <- H(m||ct) */
    memcpy(&temp[SIKE_P434_R3_MSG_BYTES], ct, SIKE_P434_R3_CIPHERTEXT_BYTES);
    shake256(ss, SIKE_P434_R3_SHARED_SECRET_BYTES, temp, SIKE_P434_R3_CIPHERTEXT_BYTES+SIKE_P434_R3_MSG_BYTES);

    return S2N_SUCCESS;
}

/* SIKE's decapsulation
 * Input:   secret key sk         (S2N_SIKE_P434_R3_SECRET_KEY_BYTES = S2N_SIKE_P434_R3_MSG_BYTES + S2N_SIKE_P434_R3_SECRETKEY_B_BYTES + S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
 *          ciphertext message ct (S2N_SIKE_P434_R3_CIPHERTEXT_BYTES = S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES + S2N_SIKE_P434_R3_MSG_BYTES bytes)
 * Outputs: shared secret ss      (S2N_SIKE_P434_R3_SHARED_SECRET_BYTES bytes) */
int s2n_sike_p434_r3_crypto_kem_dec(unsigned char *ss, const unsigned char *ct, const unsigned char *sk)
{
    //POSIX_ENSURE(s2n_pq_is_enabled(), S2N_ERR_PQ_DISABLED);

    unsigned char ephemeralsk_[SIKE_P434_R3_SECRETKEY_A_BYTES];
    unsigned char jinvariant_[SIKE_P434_R3_FP2_ENCODED_BYTES];
    unsigned char h_[SIKE_P434_R3_MSG_BYTES];
    unsigned char c0_[SIKE_P434_R3_PUBLIC_KEY_BYTES];
    unsigned char temp[SIKE_P434_R3_CIPHERTEXT_BYTES+SIKE_P434_R3_MSG_BYTES];

    /* Decrypt */
    EphemeralSecretAgreement_B(sk + SIKE_P434_R3_MSG_BYTES, ct, jinvariant_);
    shake256(h_, SIKE_P434_R3_MSG_BYTES, jinvariant_, SIKE_P434_R3_FP2_ENCODED_BYTES);
    for (int i = 0; i < SIKE_P434_R3_MSG_BYTES; i++) {
        temp[i] = ct[i + SIKE_P434_R3_PUBLIC_KEY_BYTES] ^ h_[i];
    }

    /* Generate ephemeralsk_ <- G(m||pk) mod oA */
    memcpy(&temp[SIKE_P434_R3_MSG_BYTES], &sk[SIKE_P434_R3_MSG_BYTES + SIKE_P434_R3_SECRETKEY_B_BYTES], SIKE_P434_R3_PUBLIC_KEY_BYTES);
    shake256(ephemeralsk_, SIKE_P434_R3_SECRETKEY_A_BYTES, temp, SIKE_P434_R3_PUBLIC_KEY_BYTES+SIKE_P434_R3_MSG_BYTES);
    ephemeralsk_[SIKE_P434_R3_SECRETKEY_A_BYTES - 1] &= SIKE_P434_R3_MASK_ALICE;

    /* Generate shared secret ss <- H(m||ct), or output ss <- H(s||ct) in case of ct verification failure */
    EphemeralKeyGeneration_A(ephemeralsk_, c0_);

    /* Verify ciphertext.
     * If c0_ and ct are NOT equal, decaps failed and we overwrite the shared secret
     * with pseudorandom noise (ss = H(s||ct)) by performing the copy (dont_copy = false).
     *
     * If c0_ and ct are equal, then decaps succeeded and we skip the overwrite and output
     * the actual shared secret: ss = H(m||ct) (dont_copy = true). */
    //bool dont_copy = s2n_constant_time_equals(c0_, ct, S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES);
    int result = memcmp(c0_, ct, SIKE_P434_R3_PUBLIC_KEY_BYTES);
    bool dont_copy = true;
    if (result != 0) {
      dont_copy = false;
    }

    POSIX_GUARD(sike_copy_or_dont(temp, sk, SIKE_P434_R3_MSG_BYTES, dont_copy));


    memcpy(&temp[SIKE_P434_R3_MSG_BYTES], ct, SIKE_P434_R3_CIPHERTEXT_BYTES);
    shake256(ss, SIKE_P434_R3_SHARED_SECRET_BYTES, temp, SIKE_P434_R3_CIPHERTEXT_BYTES+SIKE_P434_R3_MSG_BYTES);

    return S2N_SUCCESS;
}


/* Current work around for constant time copy function.
 *
 * */

int sike_copy_or_dont(uint8_t * dest, const uint8_t * src, uint32_t len, bool dont)
{
    /* if copy, then copy */
    if (!dont) {
        memcpy(dest, src, len);
        return S2N_SUCCESS;
    }

    return S2N_FAILURE;

}