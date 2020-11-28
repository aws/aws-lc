#include <stdio.h>
#include <string.h>
#include <time.h>

#include <gtest/gtest.h>

TEST(SSLMem, Comparison) {
  const size_t local_len = 2;
  static const uint8_t ticket_key0[local_len] = {0x00, 0x00};
  uint8_t ticket_key1[local_len] = {0x00, 0x01};
  uint8_t ticket_key2[local_len] = {0x01, 0x00};
  uint8_t ticket_key3[local_len] = {0x01, 0x01};
  printf("memcmp ticket_key1 vs ticket_key0 %d.\n", memcmp(ticket_key1, ticket_key0, local_len));
  printf("memcmp ticket_key2 vs ticket_key0 %d.\n", memcmp(ticket_key2, ticket_key0, local_len));
  printf("memcmp ticket_key3 vs ticket_key0 %d.\n", memcmp(ticket_key3, ticket_key0, local_len));
}

