// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "openssl/x509.h"
#include "test_util.h"

struct TestCorpus {
  std::string name;
  std::string hex;
  std::string format;
  bool awslc_success;
  bool match_openssl;
};

#define FORMAT_PEM "PEM"
#define FORMAT_DER "DER"

static const TestCorpus kTestCorpora[] = {
    // SEQUENCE using definite length encoding
    TestCorpus{"DerSimpleSeq", "300702012A0C024869", FORMAT_DER, true, true},

    // SEQUENCE using definite length encoding, with a nested SEQUENCE within
    // using definite length encoding
    TestCorpus{"DerNestedSeq", "300B0201013006020102020103", FORMAT_DER, true,
               true},

    // SEQUENCE using indefinite length encoding
    TestCorpus{"BerIndefSeqSimple", "30800201010201020000", FORMAT_DER, true,
               true},

    // SEQUENCE using indefinite length encoding, with a nested sequence within
    // it also indefinite length encoded
    TestCorpus{"BerIndefSeqNested", "3080308002010500000C0248690000",
               FORMAT_DER, true, true},

    // OCTET STRING using indefinite length encoding
    TestCorpus{"BerOctetConstructedIndef", "248004030102030402A0A10000",
               FORMAT_DER, true, true},

    // BIT STRING using indefinite length encoding
    TestCorpus{"BerBitConstructedIndef", "2380030200AA030203A00000", FORMAT_DER,
               true, true},

    // SEQUENCE with a non-minimal long-form length
    TestCorpus{
        "BerNonMinimalLength",
        "30817f047d00000000000000000000000000000000000000000000000000000000"
        "000000000000000000000000000000000000000000000000000000000000000000"
        "000000000000000000000000000000000000000000000000000000000000000000"
        "00000000000000000000000000000000000000000000000000000000000000",
        FORMAT_DER, true, true},

    // SET requires an order to the components, namely ascending order by tag,
    // for DER
    TestCorpus{"BerSetNonCanonical", "3106020102020101", FORMAT_DER, true,
               true},

    // INTEGER with extra leading zeros (non-minimal encoding) inside a
    // SEQUENCE. BER permits it; DER wouldn’t.
    TestCorpus{"BerIntegerLeadingZeros", "30050203000080", FORMAT_DER, true,
               true},

    // SEQUENCE containing a UTCTime and a GeneralizedTime using BER-legal
    // variants (offsets, fractional seconds).
    TestCorpus{"BerTimesUtcGeneralized",
               "302C17113939313233313233353935392B3035303018173230323431323"
               "3313233353935392E3132332D31313330",
               FORMAT_DER, true, true},

    // Context-specific EXPLICIT tag [0] around a SEQUENCE, plus an extra
    // INTEGER sibling.
    TestCorpus{"CtxExplicitTagged", "300AA0053003020105020109", FORMAT_DER,
               true, true},

    // Context-specific high-tag-number [31] primitive OCTET STRING "A" inside a
    // SEQUENCE.
    TestCorpus{"CtxHighTag31", "30049F1F0141", FORMAT_DER, true, true},

    // Indefinite-length SEQUENCE with no end-of-contents marker.
    TestCorpus{"MalformedMissingEoc", "3080020101", FORMAT_DER, true, true},

    // Definite-length SEQUENCE whose length says 5, but only 3 bytes follow, 2
    // bytes missing
    TestCorpus{"MalformedTruncatedLength", "3005020101", FORMAT_DER, false,
               true},

    // BIT STRING with an invalid unused-bits value (8). The first value byte of
    // a BIT STRING must be 0–7.
    TestCorpus{"MalformedBitstringUnusedBits", "3003030108", FORMAT_DER, true,
               true},

    // PEM PKCS#8 RSA-2048 private key
    TestCorpus{
        "PemPkcs8Rsa2049PrivateKey",
        "2d2d2d2d2d424547494e2050524956415445204b45592d2d2d2d2d0a4d494945764149"
        "424144414e42676b71686b6947397730424151454641415343424b5977676753694167"
        "4541416f4942415144575a2b63342b637854553668450a387a5268316f746253727869"
        "73386d7552462b7a616b79563074647663724c5254682b6f4b553534436a686269664a"
        "76767a74427759756d66467652574568590a51794e527534676d4b665454582f6a4548"
        "386f647171707948446a72547a4a713777436370796b4972776673712f6a6e6932724e"
        "50716f6a6a5870416a5162510a467851654e6469667447306471324546635572324951"
        "6165634b475832377844312f4c316c4932433337536f7244744d68522b796566366341"
        "6a48685249346e0a65477730796c4c534e3058676f47417a41655350356b79426c7762"
        "7a304673666b386b36427a56364e5275447070576c6e44794f4d626a514e3668522b31"
        "6b320a51456a4d57505534535957706538376d313058756d76385944756a69342f5746"
        "6a566373734e73794643536d6f6e62447a764361654c632b38717845723963410a546d"
        "454b5530762f41674d424141454367674541442b53663153396649415968675172754a"
        "5270384e6759794e4c6254436d487a48682b5245634952536965630a6262743279555a"
        "576c4c74644e687668707272734c35476a516e4952644645772b366e75596b36655a77"
        "58524b694942464c6975694d687633676d4e687050570a547572736872413163486c5a"
        "4177673061535743677a685438464b36627a4b46414d50564c2f415a344b7a464d642f"
        "5554307a346d346f544c5964333077504b0a4161434a4766457a6a4f4e744372736f70"
        "515846596172316161525977754c4841554b6b31644e2f6a6e47364441394547653453"
        "783553593462562b79576c4c0a6f36357249664344617038573862336d366768794a41"
        "3147756e385077737768655357525a336a6a5133475175753748665136594856325761"
        "484d724a416c6f0a75356e5759702f674d6554364935754e7268563643356b774b6565"
        "6b3257654e57364b774a6b6f3255514b42675144356353575669444f75357a487a5677"
        "5a480a4e3745753378327465673234386c4664552b474d3973315461755548734d5758"
        "2b636954384c4b4b6f34623157616667433534543065764a534e32515a4a5a6f0a7147"
        "41522f53304d6c686c774e5568754337797a4c7876595a457669784b5062364551304b"
        "45566a576c726f505379577946697459733546732b4f4d784f78690a637a7132695130"
        "6d51454d7538794439414b74584574644652514b426751446343764b347879684d3244"
        "70316258596a536261657751455953306769495438760a57566f4f48676c6365414c62"
        "494f7a4c766d3641527942584d594f6f734335543066734b634b6d687879387a592f49"
        "617033714d784555683235646f593731570a6d59736b79656a34574463722b2f4e5552"
        "2b7838696b616e69776746763449324841654f516251502b4d35436533372f43324651"
        "71384755616b31554b5058690a79663145545a4a5763774b42674450593173304c3847"
        "4973582b2b4b6152326f6238576b547044655337666a646849462b31334864736f6437"
        "396a33587a72460a696e466c6d4662457771714170696f6c674166796e43584d5a5845"
        "3731782b4e7a396f74573433414c5331726864434a3141455369364567783730737a6a"
        "704a0a507450776775757876692b446435386e715862776b4a74675671334e794b7831"
        "3877413534476651393658736c7a432f554e33615a72425a416f4741633157740a755a"
        "707944693038487661372b473058736f68356558466b4972654964646f41734f756666"
        "6e394e422b787645624145485771716b656c624742305965306a520a71377733765a73"
        "3471316755753148546b31734133576c4c4b43553352642f2f4a63354c4e5869506d70"
        "6461434841576a595377326671757673794e684b30570a624d4d566a5657645477324b"
        "474561767747663264454e76757441706162447a396b77756975384367594231523142"
        "542f59385152786a7a4f677a4a506a76790a676e4479304e7257714266677a746b734a"
        "5776756656786751723268435777682b4477696537746a685149444137473336525772"
        "4b31673566613861516147310a504d646a4e766a6a763658736947474c304f31324347"
        "61417a4c6e41536e454e6d776b6f6f696a6c526844646d38705769475a3951416c356b"
        "4e72424b6f75380a69576d3149424c5538434966523346534250764361673d3d0a2d2d"
        "2d2d2d454e442050524956415445204b45592d2d2d2d2d0a",
        FORMAT_PEM, true, true},

    // PEM RSA-2048 public key
    TestCorpus{
        "PemRsa2049PublicKey",
        "2d2d2d2d2d424547494e205055424c4943204b45592d2d2d2d2d0a4d494942496a414e"
        "42676b71686b6947397730424151454641414f43415138414d49494243674b43415145"
        "41316d666e4f506e4d55314f6f52504d305964614c0a573071385972504a726b526673"
        "32704d6c644c5862334b793055346671436c4f65416f3457346e79623738375163474c"
        "706e78623056684957454d6a556275490a4a696e3030312f3478422f4b486171716368"
        "773436303879617538416e4b6370434b3848374b7634353474717a5436714934313651"
        "49304730426355486a58590a6e375274486174684258464b396945476e6e43686c3975"
        "3851396679395a534e67742b30714b773754495566736e6e2b6e4149783455534f4a33"
        "68734e4d70530a306a6446344b42674d77486b6a2b5a4d675a6347383942624835504a"
        "4f676331656a556267366156705a77386a6a47343044656f5566745a4e6b42497a466a"
        "310a4f456d467158764f357464463770722f4741376f34755031685931584c4c44624d"
        "68516b70714a32773837776d6e693350764b73524b2f5841453568436c4e4c0a2f7749"
        "44415141420a2d2d2d2d2d454e44205055424c4943204b45592d2d2d2d2d0a",
        FORMAT_PEM, true, true},

    // PEM PKCS#8 EC P-256 private key
    TestCorpus{
        "PemPkcs8EcP256PrivateKey",
        "2d2d2d2d2d424547494e2050524956415445204b45592d2d2d2d2d0a4d494748416745"
        "414d424d4742797147534d34394167454743437147534d343941774548424730776177"
        "494241515167587158694a5259516770516f622f74770a55353162344f71447877332f"
        "30364251656668576f5634626c4d476852414e434141526366725374766b7a76314632"
        "3265577a6c4b6a554d6b7632774e754d590a664c5a772f364d6d6933325a7769396d64"
        "653052615a69716545536565634a624c6f31544e5a776b4e7a322b2f387a6564654b43"
        "323762410a2d2d2d2d2d454e442050524956415445204b45592d2d2d2d2d0a",
        FORMAT_PEM, true, true},

    // PEM EC P-256 public key
    TestCorpus{"PemEcP256PublicKey",
               "2d2d2d2d2d424547494e205055424c4943204b45592d2d2d2d2d0a4d466b774"
               "57759484b6f5a497a6a3043415159494b6f5a497a6a30444151634451674145"
               "584836307262354d37395264746e6c7335536f31444a4c397344626a0a47487"
               "93263502b6a4a6f74396d6349765a6e587445576d59716e68456e6e6e435779"
               "364e557a57634a44633976762f4d336e58696774753277413d3d0a2d2d2d2d2"
               "d454e44205055424c4943204b45592d2d2d2d2d0a",
               FORMAT_PEM, true, true},

    // PEM PKCS#8 Ed25519 Private Key
    TestCorpus{"PemPkcs8Ed25519PrivateKey",
               "2d2d2d2d2d424547494e2050524956415445204b45592d2d2d2d2d0a4d43344"
               "341514177425159444b32567742434945494f304e69786672794364392b4851"
               "626f373156634b6539497a2b6b7a356d7546416d58395251744c7558560a2d2"
               "d2d2d2d454e442050524956415445204b45592d2d2d2d2d0a",
               FORMAT_PEM, true, true},

    // PEM Ed25519 Public Key
    TestCorpus{"PemEd25519PublicKey",
               "2d2d2d2d2d424547494e205055424c4943204b45592d2d2d2d2d0a4d436f774"
               "25159444b32567741794541394e3455724a42356d744e65384a6f7a3941784a"
               "65394c33695053574e4b5a6f416272654158686d674e553d0a2d2d2d2d2d454"
               "e44205055424c4943204b45592d2d2d2d2d0a",
               FORMAT_PEM, true, true},

    // Self-signed X.509 certificate using EC P-256
    TestCorpus{
        "SelfSignedCertificate",
        "2d2d2d2d2d424547494e2043455254494649434154452d2d2d2d2d0a4d494942677a43"
        "4341536d6741774942416749554459504549716e635851584447564c356e5251547278"
        "4e5434747377436759494b6f5a497a6a3045417749770a467a45564d424d4741315545"
        "4177774d5a586868625842735a5335305a584e304d423458445449314d5449774e4449"
        "774e5467314f466f58445449324d5449770a4e4449774e5467314f466f77467a45564d"
        "424d47413155454177774d5a586868625842735a5335305a584e304d466b7745775948"
        "4b6f5a497a6a3043415159490a4b6f5a497a6a30444151634451674145584836307262"
        "354d37395264746e6c7335536f31444a4c397344626a4748793263502b6a4a6f74396d"
        "6349765a6e58740a45576d59716e68456e6e6e435779364e557a57634a44633976762f"
        "4d336e586967747532774b4e544d464577485159445652304f4242594546436a323277"
        "794f0a41475a4a54616e70633878724a45456a797367574d4238474131556449775159"
        "4d42614146436a323277794f41475a4a54616e70633878724a45456a797367570a4d41"
        "384741315564457745422f7751464d414d4241663877436759494b6f5a497a6a304541"
        "774944534141775251496841505738336d465030687834784e44470a59352b68306961"
        "3466354a7a3079344a45377375314b63576f482f70416941614e772f793579784b714d"
        "79732b665243364a6175335968424f79516944495a560a4d43474c78716b5875773d3d"
        "0a2d2d2d2d2d454e442043455254494649434154452d2d2d2d2d0a",
        FORMAT_PEM, true, true}};

class CorpusTest : public ::testing::TestWithParam<TestCorpus> {
 protected:
  void SetUp() override {
    const auto &param = GetParam();
    std::vector<uint8_t> data = HexToBytes(param.hex.c_str());
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_file()));
    ASSERT_TRUE(bio);
    ASSERT_TRUE(BIO_write_filename(bio.get(), in_path));
    ASSERT_TRUE(BIO_write_all(bio.get(), data.data(), data.size()));
    ASSERT_TRUE(BIO_flush(bio.get()));
  }

  void TearDown() override { RemoveFile(in_path); }

  char in_path[PATH_MAX];
};

TEST_P(CorpusTest, AwsLcParseAsExpected) {
  const auto &param = GetParam();

  args_list_t args = {"-in", in_path, "-inform", param.format};
  bool ok = asn1parseTool(args);

  if (param.awslc_success) {
    EXPECT_TRUE(ok) << "Expected success for: " << param.name;
  } else {
    EXPECT_FALSE(ok) << "Expected failure for: " << param.name;
  }
}

class CorpusComparisonTest : public ::testing::TestWithParam<TestCorpus> {
 protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or "
                      "OPENSSL_TOOL_PATH environment variables are not set";
    }

    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);

    const auto &param = GetParam();
    std::vector<uint8_t> data = HexToBytes(param.hex.c_str());
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_file()));
    ASSERT_TRUE(bio);
    ASSERT_TRUE(BIO_write_filename(bio.get(), in_path));
    ASSERT_TRUE(BIO_write_all(bio.get(), data.data(), data.size()));
    ASSERT_TRUE(BIO_flush(bio.get()));
  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(in_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
    }
  }

  char in_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  const char *tool_executable_path;
  const char *openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

TEST_P(CorpusComparisonTest, asn1parseCompare) {
  const auto &param = GetParam();
  if (!(param.awslc_success && param.match_openssl)) {
    GTEST_SKIP() << "Skipping test: negative aws-lc test-case, or expected "
                    "mismatch on output";
  }
  std::string tool_command = std::string(tool_executable_path) +
                             " asn1parse -inform " + param.format + " -in " +
                             in_path + " > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " asn1parse -inform " + param.format + " -in " +
                                in_path + " > " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);
}

static std::string makeNiceTestName(std::string name) {
  // GTest requires only [A-Za-z0-9_]; sanitize just in case
  std::string n = name;
  for (char &c : n) {
    if (!std::isalnum(static_cast<unsigned char>(c)))
      c = '_';
  }
  return n;
}

INSTANTIATE_TEST_SUITE_P(
    asn1parse, CorpusTest, ::testing::ValuesIn(kTestCorpora),
    [](const ::testing::TestParamInfo<CorpusTest::ParamType> &info) {
      return makeNiceTestName(info.param.name);
    });

INSTANTIATE_TEST_SUITE_P(
    asn1parse, CorpusComparisonTest, ::testing::ValuesIn(kTestCorpora),
    [](const ::testing::TestParamInfo<CorpusComparisonTest::ParamType> &info) {
      return makeNiceTestName(info.param.name);
    });
