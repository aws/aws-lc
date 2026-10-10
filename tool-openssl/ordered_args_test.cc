// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include "internal.h"

namespace ordered_args {
namespace {

const argument_t kArguments[] = {
    {"-out", kOptionalArgument, "Output file"},
    {"-number", kOptionalArgument, "Number"},
    {"-pkeyopt", kDuplicateArgument, "Repeatable option"},
    {"-e", kBooleanArgument, "Encrypt"},
    {"-d", kBooleanArgument, "Decrypt"},
    {"-aes128", kBooleanArgument, "AES-128"},
    {"-aes256", kBooleanArgument, "AES-256"},
    {"-none", kBooleanArgument, "No cipher"},
    {"-sha256", kExclusiveBooleanArgument, "SHA-256"},
    {"-sha512", kExclusiveBooleanArgument, "SHA-512"},
    {"", kOptionalArgument, ""},
};

TEST(OrderedArgsTest, LastStringWinsWithoutChangingFirstString) {
  ordered_args_map_t args;
  args_list_t extra;
  ASSERT_TRUE(ParseOrderedKeyValueArguments(
      args, extra, {"-out", "first", "-e", "-out", "second", "-out", "last"},
      kArguments));
  EXPECT_TRUE(extra.empty());

  std::string value;
  GetLastString(&value, "-out", "fallback", args);
  EXPECT_EQ("last", value);
  ASSERT_TRUE(GetString(&value, "-out", "fallback", args));
  EXPECT_EQ("first", value);
  ASSERT_NE(args.end(), FindArg(args, "-out"));
  EXPECT_EQ("first", FindArg(args, "-out")->second);
  EXPECT_EQ(3u, CountArgument(args, "-out"));
}

TEST(OrderedArgsTest, LastStringDistinguishesEmptyFromAbsent) {
  ordered_args_map_t args;
  args_list_t extra;
  ASSERT_TRUE(ParseOrderedKeyValueArguments(
      args, extra, {"-out", "first", "-out", ""}, kArguments));
  std::string value = "previous";
  GetLastString(&value, "-out", "fallback", args);
  EXPECT_TRUE(value.empty());
  EXPECT_TRUE(HasArgument(args, "-out"));

  GetLastString(&value, "-number", "fallback", args);
  EXPECT_EQ("fallback", value);
  EXPECT_FALSE(HasArgument(args, "-number"));
  GetLastString(&value, "-out", "fallback", {});
  EXPECT_EQ("fallback", value);
}

TEST(OrderedArgsTest, InterleavedSelectionsFollowCommandLineOrder) {
  ordered_args_map_t args;
  args_list_t extra;
  ASSERT_TRUE(ParseOrderedKeyValueArguments(
      args, extra,
      {"-d", "-aes128", "-e", "-none", "-aes256", "-d", "-out", "-e"},
      kArguments));
  // The value of -out is not an occurrence of the -e flag.
  EXPECT_EQ("-d", GetLastOption({"-e", "-d"}, "-e", args));
  EXPECT_EQ("-d", GetLastOption({"-d", "-e"}, "-e", args));
  EXPECT_EQ("-aes256",
            GetLastOption({"-none", "-aes128", "-aes256"}, "-none", args));
  EXPECT_EQ("-aes256",
            GetLastOption({"-aes256", "-aes128", "-none"}, "-none", args));
}

TEST(OrderedArgsTest, LastSelectionCanRestoreDefault) {
  ordered_args_map_t args;
  args_list_t extra;
  ASSERT_TRUE(ParseOrderedKeyValueArguments(
      args, extra, {"-aes256", "-none", "-none", "-d", "-e"}, kArguments));
  EXPECT_EQ("-none",
            GetLastOption({"-none", "-aes128", "-aes256"}, "-none", args));
  EXPECT_EQ("-e", GetLastOption({"-e", "-d"}, "-e", args));
}

TEST(OrderedArgsTest, MissingSelectionUsesDefault) {
  const ordered_args_map_t args = {{"-out", "file"}};
  EXPECT_EQ("-e", GetLastOption({"-e", "-d"}, "-e", args));
  EXPECT_EQ("-none", GetLastOption({"-aes128", "-none"}, "-none", {}));
  EXPECT_EQ("fallback", GetLastOption({}, "fallback", args));
  EXPECT_EQ("", GetLastOption({"-e", "-d"}, "", args));
}

TEST(OrderedArgsTest, SelectionPreservesRepeatableArgumentsAndOrder) {
  ordered_args_map_t args;
  args_list_t extra;
  ASSERT_TRUE(ParseOrderedKeyValueArguments(
      args, extra,
      {"-pkeyopt", "first", "-out", "old", "-e", "-pkeyopt", "second", "-out",
       "new", "-d", "-pkeyopt", "first", "-pkeyopt", ""},
      kArguments));
  const ordered_args_map_t original = args;
  std::string value;
  GetLastString(&value, "-out", "fallback", args);
  EXPECT_EQ("new", value);
  EXPECT_EQ("-d", GetLastOption({"-e", "-d"}, "-e", args));

  std::vector<std::string> values;
  FindAll(values, "-pkeyopt", args);
  EXPECT_EQ((std::vector<std::string>{"first", "second", "first", ""}), values);
  EXPECT_EQ(original, args);
}

TEST(OrderedArgsTest, ExistingUnsignedAndBooleanBehaviorIsUnchanged) {
  ordered_args_map_t args;
  args_list_t extra;
  ASSERT_TRUE(ParseOrderedKeyValueArguments(
      args, extra, {"-number", "7", "-number", "invalid", "-e", "-e"},
      kArguments));
  unsigned number = 0;
  ASSERT_TRUE(GetUnsigned(&number, "-number", 42, args));
  EXPECT_EQ(7u, number);
  ASSERT_TRUE(GetUnsigned(&number, "-number", 42, {}));
  EXPECT_EQ(42u, number);

  bool flag = false;
  ASSERT_TRUE(GetBoolArgument(&flag, "-e", args));
  EXPECT_TRUE(flag);
  ASSERT_TRUE(GetBoolArgument(&flag, "-d", args));
  EXPECT_FALSE(flag);
}

TEST(OrderedArgsTest, ExistingExclusivityIsUnchanged) {
  ordered_args_map_t args;
  args_list_t extra;
  ASSERT_TRUE(
      ParseOrderedKeyValueArguments(args, extra, {"-sha512"}, kArguments));
  std::string digest;
  ASSERT_TRUE(ordered_args::GetExclusiveBoolArgument(
      &digest, kArguments, "-sha256", args));
  EXPECT_EQ("-sha512", digest);
  ASSERT_TRUE(ordered_args::GetExclusiveBoolArgument(
      &digest, kArguments, "-sha256", {}));
  EXPECT_EQ("-sha256", digest);
  EXPECT_FALSE(ParseOrderedKeyValueArguments(
      args, extra, {"-sha256", "-sha512"}, kArguments));
}

}  // namespace
}  // namespace ordered_args
