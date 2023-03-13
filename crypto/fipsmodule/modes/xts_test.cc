// Copyright (c) 2020, Google Inc.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

#include <openssl/cipher.h>
#include <openssl/aes.h>

#include <vector>

#include <gtest/gtest.h>

#include "../../internal.h"
#include "internal.h"
#include "../../test/test_util.h"


struct XTSTestCase {
  const char *key_hex;
  const char *iv_hex;
  const char *plaintext_hex;
  const char *ciphertext_hex;
};

static const XTSTestCase kXTSTestCases[] = {
    // Test vectors from OpenSSL 1.1.1d.
    // plaintext length = 32 blocks = 512 bytes
    {
        "2718281828459045235360287471352662497757247093699959574966967627314159"
        "2653589793238462643383279502884197169399375105820974944592",
        "ff000000000000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122"
        "232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445"
        "464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768"
        "696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b"
        "8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadae"
        "afb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1"
        "d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4"
        "f5f6f7f8f9fafbfcfdfeff000102030405060708090a0b0c0d0e0f1011121314151617"
        "18191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a"
        "3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d"
        "5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f80"
        "8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3"
        "a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6"
        "c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9"
        "eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
        "1c3b3a102f770386e4836c99e370cf9bea00803f5e482357a4ae12d414a3e63b5d31e2"
        "76f8fe4a8d66b317f9ac683f44680a86ac35adfc3345befecb4bb188fd5776926c49a3"
        "095eb108fd1098baec70aaa66999a72a82f27d848b21d4a741b0c5cd4d5fff9dac89ae"
        "ba122961d03a757123e9870f8acf1000020887891429ca2a3e7a7d7df7b10355165c8b"
        "9a6d0a7de8b062c4500dc4cd120c0f7418dae3d0b5781c34803fa75421c790dfe1de18"
        "34f280d7667b327f6c8cd7557e12ac3a0f93ec05c52e0493ef31a12d3d9260f79a289d"
        "6a379bc70c50841473d1a8cc81ec583e9645e07b8d9670655ba5bbcfecc6dc3966380a"
        "d8fecb17b6ba02469a020a84e18e8f84252070c13e9f1f289be54fbc481457778f6160"
        "15e1327a02b140f1505eb309326d68378f8374595c849d84f4c333ec4423885143cb47"
        "bd71c5edae9be69a2ffeceb1bec9de244fbe15992b11b77c040f12bd8f6a975a44a0f9"
        "0c29a9abc3d4d893927284c58754cce294529f8614dcd2aba991925fedc4ae74ffac6e"
        "333b93eb4aff0479da9a410e4450e0dd7ae4c6e2910900575da401fc07059f645e8b7e"
        "9bfdef33943054ff84011493c27b3429eaedb4ed5376441a77ed43851ad77f16f541df"
        "d269d50d6a5f14fb0aab1cbb4c1550be97f7ab4066193c4caa773dad38014bd2092fa7"
        "55c824bb5e54c4f36ffda9fcea70b9c6e693e148c151",
    },
    {
        "2718281828459045235360287471352662497757247093699959574966967627314159"
        "2653589793238462643383279502884197169399375105820974944592",
        "ffff0000000000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122"
        "232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445"
        "464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768"
        "696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b"
        "8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadae"
        "afb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1"
        "d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4"
        "f5f6f7f8f9fafbfcfdfeff000102030405060708090a0b0c0d0e0f1011121314151617"
        "18191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a"
        "3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d"
        "5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f80"
        "8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3"
        "a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6"
        "c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9"
        "eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
        "77a31251618a15e6b92d1d66dffe7b50b50bad552305ba0217a610688eff7e11e1d022"
        "5438e093242d6db274fde801d4cae06f2092c728b2478559df58e837c2469ee4a4fa79"
        "4e4bbc7f39bc026e3cb72c33b0888f25b4acf56a2a9804f1ce6d3d6e1dc6ca181d4b54"
        "6179d55544aa7760c40d06741539c7e3cd9d2f6650b2013fd0eeb8c2b8e3d8d240ccae"
        "2d4c98320a7442e1c8d75a42d6e6cfa4c2eca1798d158c7aecdf82490f24bb9b38e108"
        "bcda12c3faf9a21141c3613b58367f922aaa26cd22f23d708dae699ad7cb40a8ad0b6e"
        "2784973dcb605684c08b8d6998c69aac049921871ebb65301a4619ca80ecb485a31d74"
        "4223ce8ddc2394828d6a80470c092f5ba413c3378fa6054255c6f9df4495862bbb3287"
        "681f931b687c888abf844dfc8fc28331e579928cd12bd2390ae123cf03818d14dedde5"
        "c0c24c8ab018bfca75ca096f2d531f3d1619e785f1ada437cab92e980558b3dce1474a"
        "fb75bfedbf8ff54cb2618e0244c9ac0d3c66fb51598cd2db11f9be39791abe447c6309"
        "4f7c453b7ff87cb5bb36b7c79efb0872d17058b83b15ab0866ad8a58656c5a7e20dbdf"
        "308b2461d97c0ec0024a2715055249cf3b478ddd4740de654f75ca686e0d7345c69ed5"
        "0cdc2a8b332b1f8824108ac937eb050585608ee734097fc09054fbff89eeaeea791f4a"
        "7ab1f9868294a4f9e27b42af8100cb9d59cef9645803",
    },
    {
        "2718281828459045235360287471352662497757247093699959574966967627314159"
        "2653589793238462643383279502884197169399375105820974944592",
        "ffffff00000000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122"
        "232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445"
        "464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768"
        "696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b"
        "8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadae"
        "afb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1"
        "d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4"
        "f5f6f7f8f9fafbfcfdfeff000102030405060708090a0b0c0d0e0f1011121314151617"
        "18191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a"
        "3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d"
        "5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f80"
        "8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3"
        "a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6"
        "c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9"
        "eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
        "e387aaa58ba483afa7e8eb469778317ecf4cf573aa9d4eac23f2cdf914e4e200a8b490"
        "e42ee646802dc6ee2b471b278195d60918ececb44bf79966f83faba0499298ebc699c0"
        "c8634715a320bb4f075d622e74c8c932004f25b41e361025b5a87815391f6108fc4afa"
        "6a05d9303c6ba68a128a55705d415985832fdeaae6c8e19110e84d1b1f199a2692119e"
        "dc96132658f09da7c623efcec712537a3d94c0bf5d7e352ec94ae5797fdb377dc15511"
        "50721adf15bd26a8efc2fcaad56881fa9e62462c28f30ae1ceaca93c345cf243b73f54"
        "2e2074a705bd2643bb9f7cc79bb6e7091ea6e232df0f9ad0d6cf502327876d82207abf"
        "2115cdacf6d5a48f6c1879a65b115f0f8b3cb3c59d15dd8c769bc014795a1837f3901b"
        "5845eb491adfefe097b1fa30a12fc1f65ba22905031539971a10f2f36c321bb51331cd"
        "efb39e3964c7ef079994f5b69b2edd83a71ef549971ee93f44eac3938fcdd61d01fa71"
        "799da3a8091c4c48aa9ed263ff0749df95d44fef6a0bb578ec69456aa5408ae32c7af0"
        "8ad7ba8921287e3bbee31b767be06a0e705c864a769137df28292283ea81a2480241b4"
        "4d9921cdbec1bc28dc1fda114bd8e5217ac9d8ebafa720e9da4f9ace231cc949e5b96f"
        "e76ffc21063fddc83a6b8679c00d35e09576a875305bed5f36ed242c8900dd1fa965bc"
        "950dfce09b132263a1eef52dd6888c309f5a7d712826",
    },
    {
        "2718281828459045235360287471352662497757247093699959574966967627314159"
        "2653589793238462643383279502884197169399375105820974944592",
        "ffffffff000000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122"
        "232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445"
        "464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768"
        "696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b"
        "8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadae"
        "afb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1"
        "d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4"
        "f5f6f7f8f9fafbfcfdfeff000102030405060708090a0b0c0d0e0f1011121314151617"
        "18191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a"
        "3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d"
        "5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f80"
        "8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3"
        "a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6"
        "c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9"
        "eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
        "bf53d2dade78e822a4d949a9bc6766b01b06a8ef70d26748c6a7fc36d80ae4c5520f7c"
        "4ab0ac8544424fa405162fef5a6b7f229498063618d39f0003cb5fb8d1c86b643497da"
        "1ff945c8d3bedeca4f479702a7a735f043ddb1d6aaade3c4a0ac7ca7f3fa5279bef56f"
        "82cd7a2f38672e824814e10700300a055e1630b8f1cb0e919f5e942010a416e2bf48cb"
        "46993d3cb6a51c19bacf864785a00bc2ecff15d350875b246ed53e68be6f55bd7e05cf"
        "c2b2ed6432198a6444b6d8c247fab941f569768b5c429366f1d3f00f0345b96123d562"
        "04c01c63b22ce78baf116e525ed90fdea39fa469494d3866c31e05f295ff21fea8d4e6"
        "e13d67e47ce722e9698a1c1048d68ebcde76b86fcf976eab8aa9790268b7068e017a8b"
        "9b749409514f1053027fd16c3786ea1bac5f15cb79711ee2abe82f5cf8b13ae73030ef"
        "5b9e4457e75d1304f988d62dd6fc4b94ed38ba831da4b7634971b6cd8ec325d9c61c00"
        "f1df73627ed3745a5e8489f3a95c69639c32cd6e1d537a85f75cc844726e8a72fc0077"
        "ad22000f1d5078f6b866318c668f1ad03d5a5fced5219f2eabbd0aa5c0f460d183f044"
        "04a0d6f469558e81fab24a167905ab4c7878502ad3e38fdbe62a41556cec3732575953"
        "3ce8f25f367c87bb5578d667ae93f9e2fd99bcbc5f2fbba88cf6516139420fcff3b736"
        "1d86322c4bd84c82f335abb152c4a93411373aaa8220",
    },
    {
        "2718281828459045235360287471352662497757247093699959574966967627314159"
        "2653589793238462643383279502884197169399375105820974944592",
        "ffffffffff0000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122"
        "232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445"
        "464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768"
        "696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b"
        "8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadae"
        "afb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1"
        "d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4"
        "f5f6f7f8f9fafbfcfdfeff000102030405060708090a0b0c0d0e0f1011121314151617"
        "18191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a"
        "3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d"
        "5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f80"
        "8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3"
        "a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6"
        "c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9"
        "eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
        "64497e5a831e4a932c09be3e5393376daa599548b816031d224bbf50a818ed2350eae7"
        "e96087c8a0db51ad290bd00c1ac1620857635bf246c176ab463be30b808da548081ac8"
        "47b158e1264be25bb0910bbc92647108089415d45fab1b3d2604e8a8eff1ae4020cfa3"
        "9936b66827b23f371b92200be90251e6d73c5f86de5fd4a950781933d79a28272b782a"
        "2ec313efdfcc0628f43d744c2dc2ff3dcb66999b50c7ca895b0c64791eeaa5f29499fb"
        "1c026f84ce5b5c72ba1083cddb5ce45434631665c333b60b11593fb253c5179a2c8db8"
        "13782a004856a1653011e93fb6d876c18366dd8683f53412c0c180f9c848592d593f86"
        "09ca736317d356e13e2bff3a9f59cd9aeb19cd482593d8c46128bb32423b37a9adfb48"
        "2b99453fbe25a41bf6feb4aa0bef5ed24bf73c762978025482c13115e4015aac992e56"
        "13a3b5c2f685b84795cb6e9b2656d8c88157e52c42f978d8634c43d06fea928f2822e4"
        "65aa6576e9bf419384506cc3ce3c54ac1a6f67dc66f3b30191e698380bc999b05abce1"
        "9dc0c6dcc2dd001ec535ba18deb2df1a101023108318c75dc98611a09dc48a0acdec67"
        "6fabdf222f07e026f059b672b56e5cbc8e1d21bbd867dd927212054681d70ea737134c"
        "dfce93b6f82ae22423274e58a0821cc5502e2d0ab4585e94de6975be5e0b4efce51cd3"
        "e70c25a1fbbbd609d273ad5b0d59631c531f6a0a57b9",
    },
    // https://github.com/BrianGladman/modes/blob/master/testvals/xts.6#L313
    // VEC 30, len = 16 bytes = 1 block
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f",
        "c30ca8f2ed57307edc87e544867ac888",
    },
    // https://github.com/BrianGladman/modes/blob/master/testvals/xts.6#L321
    // VEC 31, len = 17 bytes = 1 block + 1 byte
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f10",
        "7f117752cc598a8b0d81d88af9f9bec8c3",
    },
    // https://github.com/BrianGladman/modes/blob/master/testvals/xts.6#L361
    // VEC 36, len = 22 bytes = 1 block + 6 bytes
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415",
        "75e8188bcce59ada939f57de2cb9a489c30ca8f2ed57",
    },
    // https://github.com/BrianGladman/modes/blob/master/testvals/xts.6#L433
    // VEC 45, len = 31 bytes = 1 block + 15 bytes
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e",
        "581ea1fee5516ad432ddebe75fd27c6fc30ca8f2ed57307edc87e544867ac8",
    },
    // https://github.com/BrianGladman/modes/blob/master/testvals/xts.12#L2611
    // VEC 301, len = 32 bytes = 2 blocks (decryption vector)
    // This vector did not pass, the output below is the same for
    // the C implementation, |CRYPTO_xts128_encrypt|, and the AArch64 assembly.
    {
        "1b278f1086f30d9f3b18a8dc2a258efea106b45bd18c760e360ba3c69859de47"
        "1c1c73d5f3de874486fa1d2c0573dfec5567d07468649a24dc9e72f421fa0b83",
        "28000000000000000000000000000000",
        "208e5d0fa5ce130b294265e6430b98772eaae086a922391b98f0dec159a4f9c0",
        //"7091c013f06ae69848144b65c7a9ad557b8dc9d2c9bc031fa40ba63cce594280",
        "7b8dc9d2c9bc031fa40ba63cce59428e09fccc48a96a95da120a592d2da9ff9c",
    },
    // https://github.com/BrianGladman/modes/blob/master/testvals/xts.12#L3411
    // VEC 401, len = 48 bytes = 3 blocks (decryption vector)
    {
        "1338d7d3d66137abf00c8f33050cff7e0a6fa10ff2e2bd860119dfa68ee815c4"
        "4aa1bfc76f2e084d81b862c05aae29711bf167fff7432a7b9c5899ab069fff0f",
        "54000000000000000000000000000000",
        "922489de313fceb72a5ef2594d49eeb908afec966e89f0c7fbb4f6d37a559294"
        "2c53e3a65b37193d693467006595f811",
        "6f229c1b60833e2a50a041b360d99181a679f1361a011bf37b2e1565fda4a6b9"
        "22e5aabda21b167c030935e843d60c60",
    },
    //
    // The following tests were generated by the C implementation to ensure
    // the AArch64 implementation produces the same output.
    // The plaintext lengths were chosen such that one or more vectors
    // exercise a certain path in the assembly code.
    // len = 44 blocks = 2 blocks + 12 bytes
    {
        "1338d7d3d66137abf00c8f33050cff7e0a6fa10ff2e2bd860119dfa68ee815c4"
        "4aa1bfc76f2e084d81b862c05aae29711bf167fff7432a7b9c5899ab069fff0f",
        "54000000000000000000000000000000",
        "922489de313fceb72a5ef2594d49eeb908afec966e89f0c7fbb4f6d37a559294"
        "2c53e3a65b37193d69346700",
        "6f229c1b60833e2a50a041b360d991814c6ec7f3199d8b2482f5b19b64c32013"
        "a679f1361a011bf37b2e1565"
    },
    // len = 51 bytes = 3 blocks + 3 bytes
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "bea47768aa25376e924cce6a102ca2e4e1c241",
    },
    // len = 64 bytes = 4 blocks
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "e1c241d0ff691de6b47ad81eac2b925b474e1fd14311edb95219ce64677f497b",
    },
    // len = 74 bytes = 4 blocks + 10 bytes
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"
        "40414243444546474849",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "e1c241d0ff691de6b47ad81eac2b925b0f451eb8847b98d48b1407f64a4f9ee3"
        "474e1fd14311edb95219",
    },
    // len = 80 bytes = 5 blocks
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"
        "404142434445464748494a4b4c4d4e4f",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "e1c241d0ff691de6b47ad81eac2b925b474e1fd14311edb95219ce64677f497b"
        "8917567652e9b4ef3838baf35e400fe1"
    },
    // len = 87 bytes = 5 blocks + 7 bytes
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"
        "404142434445464748494a4b4c4d4e4f50515253545556",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "e1c241d0ff691de6b47ad81eac2b925b474e1fd14311edb95219ce64677f497b"
        "a436b967e79bb8e8e4c29d1099fe1bbf8917567652e9b4"
    },
    // len = 96 bytes = 6 blocks
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"
        "404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "e1c241d0ff691de6b47ad81eac2b925b474e1fd14311edb95219ce64677f497b"
        "8917567652e9b4ef3838baf35e400fe1ffe2f16cfa1900d7ae2b67f0e6f43b71",
    },
    // len = 128 bytes = 8 blocks
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"
        "404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f"
        "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "e1c241d0ff691de6b47ad81eac2b925b474e1fd14311edb95219ce64677f497b"
        "8917567652e9b4ef3838baf35e400fe1ffe2f16cfa1900d7ae2b67f0e6f43b71"
        "769d1b0e0c0b99ea11de58fcd3b72e1bce3d9a8750b87e945d77f4dc39d73b04",
    },
    // len = 134 bytes = 8 blocks + 6 bytes
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"
        "404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f"
        "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f"
        "808182838485",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "e1c241d0ff691de6b47ad81eac2b925b474e1fd14311edb95219ce64677f497b"
        "8917567652e9b4ef3838baf35e400fe1ffe2f16cfa1900d7ae2b67f0e6f43b71"
        "769d1b0e0c0b99ea11de58fcd3b72e1be0ad32884698e15420e52c96b698bba1"
        "ce3d9a8750b8",
    },

    // len = 144 bytes = 9 blocks
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"
        "404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f"
        "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f"
        "808182838485868788898a8b8c8d8e8f",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "e1c241d0ff691de6b47ad81eac2b925b474e1fd14311edb95219ce64677f497b"
        "8917567652e9b4ef3838baf35e400fe1ffe2f16cfa1900d7ae2b67f0e6f43b71"
        "769d1b0e0c0b99ea11de58fcd3b72e1bce3d9a8750b87e945d77f4dc39d73b04"
        "e11b6adce343e1f38c6a879463c080d7",
    },
    // len = 158 bytes = 9 blocks + 14 bytes
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"
        "404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f"
        "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f"
        "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "e1c241d0ff691de6b47ad81eac2b925b474e1fd14311edb95219ce64677f497b"
        "8917567652e9b4ef3838baf35e400fe1ffe2f16cfa1900d7ae2b67f0e6f43b71"
        "769d1b0e0c0b99ea11de58fcd3b72e1bce3d9a8750b87e945d77f4dc39d73b04"
        "a5da920d96beb388ade417027054dbd0e11b6adce343e1f38c6a879463c0",
    },
    // len = 160 bytes = 10 blocks
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"
        "404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f"
        "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f"
        "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "e1c241d0ff691de6b47ad81eac2b925b474e1fd14311edb95219ce64677f497b"
        "8917567652e9b4ef3838baf35e400fe1ffe2f16cfa1900d7ae2b67f0e6f43b71"
        "769d1b0e0c0b99ea11de58fcd3b72e1bce3d9a8750b87e945d77f4dc39d73b04"
        "e11b6adce343e1f38c6a879463c080d74a72a90b1e6fe46b7bc95a929f79947e",
    },
    // len = 165 bytes = 10 blocks + 5 bytes
    {
        "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
        "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
        "9a785634120000000000000000000000",
        "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
        "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"
        "404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f"
        "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f"
        "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
        "a0a1a2a3a4",
        "c30ca8f2ed57307edc87e544867ac888348c208928d7406269954551cb627b5b"
        "e1c241d0ff691de6b47ad81eac2b925b474e1fd14311edb95219ce64677f497b"
        "8917567652e9b4ef3838baf35e400fe1ffe2f16cfa1900d7ae2b67f0e6f43b71"
        "769d1b0e0c0b99ea11de58fcd3b72e1bce3d9a8750b87e945d77f4dc39d73b04"
        "e11b6adce343e1f38c6a879463c080d7254c4d65cf40e04934108bcde6bda824"
        "4a72a90b1e",
    },
    // Test vectors from NIST
    // https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program
    // 256-bit key, 256-bit data
    {
        "1ea661c58d943a0e4801e42f4b0947149e7f9f8e3e68d0c7505210bd311a0e7c"
        "d6e13ffdf2418d8d1911c004cda58da3d619b7e2b9141e58318eea392cf41b08",
        "adf8d92627464ad2f0428e84a9f87564",
        "2eedea52cd8215e1acc647e810bbc3642e87287f8d2e57e36c0a24fbc12a202e",
        "cbaad0e2f6cea3f50b37f934d46a9b130b9d54f07e34f36af793e86f73c6d7db",
    },
    // 256-bit key, 384-bit data
    {
        "266c336b3b01489f3267f52835fd92f674374b88b4e1ebd2d36a5f457581d9d0"
        "42c3eef7b0b7e5137b086496b4d9e6ac658d7196a23f23f036172fdb8faee527",
        "06b209a7a22f486ecbfadb0f3137ba42",
        "ca7d65ef8d3dfad345b61ccddca1ad81de830b9e86c7b426d76cb7db766852d9"
        "81c6b21409399d78f42cc0b33a7bbb06",
        "c73256870cc2f4dd57acc74b5456dbd776912a128bc1f77d72cdebbf270044b7"
        "a43ceed29025e1e8be211fa3c3ed002d",
    },
    // 256-bit key, 384-bit data
    {
        "33e89e817ff8d037d6ac5a2296657503f20885d94c483e26449066bd9284d130"
        "2dbdbb4b66b6b9f4687f13dd028eb6aa528ca91deb9c5f40db93218806033801",
        "a78c04335ab7498a52b81ed74b48e6cf",
        "14c3ac31291b075f40788247c3019e88c7b40bac3832da45bbc6c4fe7461371b"
        "4dfffb63f71c9f8edb98f28ff4f33121",
        "dead7e587519bc78c70d99279fbe3d9b1ad13cdaae69824e0ab8135413230bfd"
        "b13babe8f986fbb30d46ab5ec56b916e",
    },
};

TEST(XTSTest, TestVectors) {
  unsigned test_num = 0;
  for (const auto &test : kXTSTestCases) {
    test_num++;
    SCOPED_TRACE(test_num);

    const EVP_CIPHER *cipher = EVP_aes_256_xts();

    std::vector<uint8_t> key, iv, plaintext, ciphertext;
    ASSERT_TRUE(DecodeHex(&key, test.key_hex));
    ASSERT_TRUE(DecodeHex(&iv, test.iv_hex));
    ASSERT_TRUE(DecodeHex(&plaintext, test.plaintext_hex));
    ASSERT_TRUE(DecodeHex(&ciphertext, test.ciphertext_hex));

    ASSERT_EQ(EVP_CIPHER_key_length(cipher), key.size());
    ASSERT_EQ(EVP_CIPHER_iv_length(cipher), iv.size());
    ASSERT_EQ(plaintext.size(), ciphertext.size());

    // Note XTS doesn't support streaming, so we only test single-shot inputs.
    for (bool in_place : {false, true}) {
      SCOPED_TRACE(in_place);

      // Test encryption.
      bssl::Span<const uint8_t> in = plaintext;
      std::vector<uint8_t> out(plaintext.size());
      if (in_place) {
        out = plaintext;
        in = out;
      }

      bssl::ScopedEVP_CIPHER_CTX ctx;
      ASSERT_TRUE(EVP_EncryptInit_ex(ctx.get(), cipher, nullptr, key.data(),
                                     iv.data()));
      int len;
      ASSERT_TRUE(
          EVP_EncryptUpdate(ctx.get(), out.data(), &len, in.data(), in.size()));
      out.resize(len);
      EXPECT_EQ(Bytes(ciphertext), Bytes(out));

      // Test decryption.
      in = ciphertext;
      out.clear();
      out.resize(plaintext.size());
      if (in_place) {
        out = ciphertext;
        in = out;
      }

      ctx.Reset();
      ASSERT_TRUE(EVP_DecryptInit_ex(ctx.get(), cipher, nullptr, key.data(),
                                     iv.data()));
      ASSERT_TRUE(
          EVP_DecryptUpdate(ctx.get(), out.data(), &len, in.data(), in.size()));
      out.resize(len);
      EXPECT_EQ(Bytes(plaintext), Bytes(out));
    }
  }
}

// Negative test for key1 = key2
TEST(XTSTest, DuplicateKey) {

  // The 2 halves of the key below are identical.
  // The ciphertext is not correct which does not matter since it will fail in Init.
  const XTSTestCase kXTSDuplicateKey = {
    "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
    "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0",
    "9a785634120000000000000000000000",
    "000102030405060708090a0b0c0d0e0f10",
    "000102030405060708090a0b0c0d0e0f10",
  };

  const EVP_CIPHER *cipher = EVP_aes_256_xts();

  std::vector<uint8_t> key, iv, plaintext, ciphertext;
  ASSERT_TRUE(DecodeHex(&key, kXTSDuplicateKey.key_hex));
  ASSERT_TRUE(DecodeHex(&iv, kXTSDuplicateKey.iv_hex));

  bssl::ScopedEVP_CIPHER_CTX ctx;
  ASSERT_FALSE(EVP_EncryptInit_ex(ctx.get(), cipher, nullptr, key.data(),
                                 iv.data()));
}

// Negative test for input length
TEST(XTSTest, InputTooLong) {

  // The length of the input will be (wrongly) provided as larger than
  // XTS_MAX_BLOCKS_PER_DATA_UNIT.
  // The ciphertext does not correspond to the plaintext
  // which does not matter since it will fail on length check.
  const XTSTestCase kXTSWrongVector = {
    "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0"
    "bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0",
    "9a785634120000000000000000000000",
    "000102030405060708090a0b0c0d0e0f10",
    "000102030405060708090a0b0c0d0e0f10",
  };

  const EVP_CIPHER *cipher = EVP_aes_256_xts();

  std::vector<uint8_t> key, iv, plaintext, ciphertext;
  ASSERT_TRUE(DecodeHex(&key, kXTSWrongVector.key_hex));
  ASSERT_TRUE(DecodeHex(&iv, kXTSWrongVector.iv_hex));
  ASSERT_TRUE(DecodeHex(&plaintext, kXTSWrongVector.plaintext_hex));
  ASSERT_TRUE(DecodeHex(&ciphertext, kXTSWrongVector.ciphertext_hex));

  bssl::ScopedEVP_CIPHER_CTX ctx;
  ASSERT_TRUE(EVP_EncryptInit_ex(ctx.get(), cipher, nullptr, key.data(),
                                 iv.data()));
  int len;
  std::vector<uint8_t> out(plaintext.size());
  ASSERT_FALSE(
    EVP_EncryptUpdate(ctx.get(), out.data(), &len, plaintext.data(),
                      (XTS_MAX_BLOCKS_PER_DATA_UNIT * AES_BLOCK_SIZE) + 1));

  // Test Decryption
  ctx.Reset();
  ASSERT_TRUE(EVP_DecryptInit_ex(ctx.get(), cipher, nullptr, key.data(),
                                 iv.data()));
  ASSERT_FALSE(
    EVP_DecryptUpdate(ctx.get(), out.data(), &len, ciphertext.data(),
                      (XTS_MAX_BLOCKS_PER_DATA_UNIT * AES_BLOCK_SIZE) + 1));

}
