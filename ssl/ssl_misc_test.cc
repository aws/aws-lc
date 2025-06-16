// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include "ssl_test_common.h"
#include "internal.h"

BSSL_NAMESPACE_BEGIN

TEST(GrowableArrayTest, Resize) {
  GrowableArray<size_t> array;
  ASSERT_TRUE(array.empty());
  EXPECT_EQ(array.size(), 0u);

  ASSERT_TRUE(array.Push(42));
  ASSERT_TRUE(!array.empty());
  EXPECT_EQ(array.size(), 1u);

  // Force a resize operation to occur
  for (size_t i = 0; i < 16; i++) {
    ASSERT_TRUE(array.Push(i + 1));
  }

  EXPECT_EQ(array.size(), 17u);

  // Verify that expected values are still contained in array
  for (size_t i = 0; i < array.size(); i++) {
    EXPECT_EQ(array[i], i == 0 ? 42 : i);
  }
}

TEST(GrowableArrayTest, MoveConstructor) {
  GrowableArray<size_t> array;
  for (size_t i = 0; i < 100; i++) {
    ASSERT_TRUE(array.Push(i));
  }

  GrowableArray<size_t> array_moved(std::move(array));
  for (size_t i = 0; i < 100; i++) {
    EXPECT_EQ(array_moved[i], i);
  }
}

TEST(GrowableArrayTest, GrowableArrayContainingGrowableArrays) {
  // Representative example of a struct that contains a GrowableArray.
  struct TagAndArray {
    size_t tag;
    GrowableArray<size_t> array;
  };

  GrowableArray<TagAndArray> array;
  for (size_t i = 0; i < 100; i++) {
    TagAndArray elem;
    elem.tag = i;
    for (size_t j = 0; j < i; j++) {
      ASSERT_TRUE(elem.array.Push(j));
    }
    ASSERT_TRUE(array.Push(std::move(elem)));
  }
  EXPECT_EQ(array.size(), static_cast<size_t>(100));

  GrowableArray<TagAndArray> array_moved(std::move(array));
  EXPECT_EQ(array_moved.size(), static_cast<size_t>(100));
  size_t count = 0;
  for (const TagAndArray &elem : array_moved) {
    // Test the square bracket operator returns the same value as iteration.
    EXPECT_EQ(&elem, &array_moved[count]);

    EXPECT_EQ(elem.tag, count);
    EXPECT_EQ(elem.array.size(), count);
    for (size_t j = 0; j < count; j++) {
      EXPECT_EQ(elem.array[j], j);
    }
    count++;
  }
}

BSSL_NAMESPACE_END
