
#ifndef OPENSSL_HEADER_CRYPTO_TEST_UBE_TEST_H
#define OPENSSL_HEADER_CRYPTO_TEST_UBE_TEST_H

#include <gtest/gtest.h>

#include "../ube/internal.h"

class ubeTest : public::testing::Test {
  public:
    void SetUp() override {
      uint64_t current_generation_number = 0;
      if (CRYPTO_get_ube_generation_number(&current_generation_number) == 1) {
        ube_detection_supported_ = true;
      }
    }

    void TearDown() override {
      disable_mocked_ube_detection_FOR_TESTING();
    }

  protected:
    bool UbeIsSupported(void) const {
      return ube_detection_supported_;
    }

    void allowMockedUbe(void) const {
      allow_mocked_ube_detection_FOR_TESTING();
    }

    bool ube_detection_supported_ = false;
};

#endif // OPENSSL_HEADER_CRYPTO_TEST_UBE_TEST_H
