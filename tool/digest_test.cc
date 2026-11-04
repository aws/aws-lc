// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <openssl/sha.h>

#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <utility>
#include <vector>

#include "../crypto/test/test_util.h"
#include "internal.h"

namespace {

// ScopedTempFile is a temporary file that is removed when it goes out of scope.
// It uses |createTempFILEpath| rather than a hard-coded directory so that the
// tests work on platforms without a writable /tmp, such as Android.
class ScopedTempFile {
 public:
  ScopedTempFile() = default;
  ScopedTempFile(const ScopedTempFile &) = delete;
  ScopedTempFile &operator=(const ScopedTempFile &) = delete;

  ~ScopedTempFile() {
    if (!path_.empty()) {
      remove(path_.c_str());
    }
  }

  // Init creates the file and writes |content| to it. It returns true on
  // success.
  bool Init(const std::string &content) {
    char path[PATH_MAX];
    if (createTempFILEpath(path) == 0) {
      return false;
    }
    path_ = path;

    ScopedFILE file(fopen(path, "wb"));
    return file &&
           fwrite(content.data(), 1, content.size(), file.get()) ==
               content.size() &&
           fflush(file.get()) == 0;
  }

  const std::string &path() const { return path_; }

 private:
  std::string path_;
};

std::string HexSHA256(const std::string &data) {
  uint8_t digest[SHA256_DIGEST_LENGTH];
  SHA256(reinterpret_cast<const uint8_t *>(data.data()), data.size(), digest);
  static const char kHex[] = "0123456789abcdef";
  std::string ret;
  for (uint8_t b : digest) {
    ret += kHex[b >> 4];
    ret += kHex[b & 0xf];
  }
  return ret;
}

class DigestCheckTest : public testing::Test {
 protected:
  void SetUp() override {
    static const char kData[] = "hello world\n";
    ASSERT_TRUE(data_.Init(kData));
    digest_ = HexSHA256(kData);
    // A syntactically valid digest that does not match |data_|.
    wrong_digest_ = std::string(digest_.size(), '0');
  }

  // Line returns a well-formed checksum line naming |data_|.
  std::string Line(const std::string &digest) {
    return digest + "  " + data_.path() + "\n";
  }

  std::string GoodLine() { return Line(digest_); }
  std::string BadLine() { return Line(wrong_digest_); }

  // Check runs the *sum check mode over a file containing |contents| and
  // returns whether it reported success. |extra_args| is passed on the command
  // line before the file name.
  bool Check(const std::string &contents,
             const std::vector<std::string> &extra_args = {}) {
    ScopedTempFile check_file;
    if (!check_file.Init(contents)) {
      ADD_FAILURE() << "could not write the checksum file";
      return false;
    }
    // These keep the test output quiet without changing the result.
    args_list_t args = {"-c", "--status", "--quiet"};
    args.insert(args.end(), extra_args.begin(), extra_args.end());
    args.push_back(check_file.path());
    return SHA256Sum(args);
  }

  ScopedTempFile data_;
  std::string digest_;
  std::string wrong_digest_;
};

TEST_F(DigestCheckTest, MatchingDigest) { EXPECT_TRUE(Check(GoodLine())); }

TEST_F(DigestCheckTest, MismatchedDigest) { EXPECT_FALSE(Check(BadLine())); }

TEST_F(DigestCheckTest, NoValidLines) { EXPECT_FALSE(Check("garbage\n")); }

TEST_F(DigestCheckTest, StrictRejectsMalformedLines) {
  EXPECT_TRUE(Check("garbage\n" + GoodLine()));
  EXPECT_FALSE(Check("garbage\n" + GoodLine(), {"--strict"}));
}

// A line containing a NUL byte is not a valid checksum line. Rejecting it must
// not consume the line that follows: |strlen| stops at the NUL, which used to
// make such a line look truncated and start skipping input.
TEST_F(DigestCheckTest, LineWithEmbeddedNUL) {
  std::string contents = digest_ + "  " + data_.path();
  contents.push_back('\0');
  contents += "junk\n";
  // The following line does not match, so the check must fail. If the NUL line
  // were treated as truncated, this line would be skipped instead.
  contents += BadLine();
  contents += GoodLine();
  EXPECT_FALSE(Check(contents));

  // The line after the NUL line is checked, not merely counted.
  std::string ok_contents = digest_ + "  " + data_.path();
  ok_contents.push_back('\0');
  ok_contents += "junk\n";
  ok_contents += GoodLine();
  EXPECT_TRUE(Check(ok_contents));
  EXPECT_FALSE(Check(ok_contents, {"--strict"}));
}

// Likewise for a line whose very first byte is a NUL.
TEST_F(DigestCheckTest, LineStartingWithNUL) {
  std::string contents;
  contents.push_back('\0');
  contents += "junk\n";
  contents += BadLine();
  contents += GoodLine();
  EXPECT_FALSE(Check(contents));

  std::string ok_contents;
  ok_contents.push_back('\0');
  ok_contents += "junk\n";
  ok_contents += GoodLine();
  EXPECT_TRUE(Check(ok_contents));
  EXPECT_FALSE(Check(ok_contents, {"--strict"}));
}

// A line too long for the input buffer is skipped in its entirety. The lines
// after it must still be checked, including when the overlong line contains NUL
// bytes.
TEST_F(DigestCheckTest, OverlongLine) {
  for (const bool with_nuls : {false, true}) {
    SCOPED_TRACE(with_nuls);
    std::string overlong(100000, 'A');
    if (with_nuls) {
      // Fill the second half of the line with NUL bytes. The first half is
      // longer than the input buffer, so the reader is already skipping the line
      // by the time it sees them. |strlen| reports zero for those chunks, which
      // used to leave the reader out of sync with the start of the next line.
      overlong.replace(overlong.size() / 2, std::string::npos,
                       overlong.size() / 2, '\0');
    }
    overlong += "\n";

    EXPECT_FALSE(Check(overlong + BadLine() + GoodLine()));
    EXPECT_TRUE(Check(overlong + GoodLine()));
    EXPECT_FALSE(Check(overlong + GoodLine(), {"--strict"}));
  }
}

}  // namespace
