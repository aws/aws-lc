// Copyright (c) 2018, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/sha.h>

#include <memory>
#include <vector>

#include <gtest/gtest.h>

#include "../../test/abi_test.h"
#include "../../test/test_util.h"
#include "internal.h"

#if defined(SUPPORTS_ABI_TEST) && defined(OPENSSL_X86_64) && \
    defined(OPENSSL_WINDOWS) && defined(_MSC_VER)
OPENSSL_MSVC_PRAGMA(warning(push, 3))
#include <windows.h>
OPENSSL_MSVC_PRAGMA(warning(pop))
#endif

#if defined(SUPPORTS_ABI_TEST) && !defined(SHA1_ALTIVEC)
TEST(SHATest, SHA1ABI) {
  SHA_CTX ctx;
  SHA1_Init(&ctx);

  static const uint8_t kBuf[SHA_CBLOCK * 8] = {0};
  for (size_t blocks : {1, 2, 4, 8}) {
#if defined(SHA1_ASM)
    CHECK_ABI(sha1_block_data_order, ctx.h, kBuf, blocks);
#endif
#if defined(SHA1_ASM_HW)
    if (sha1_hw_capable()) {
      CHECK_ABI(sha1_block_data_order_hw, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA1_ASM_AVX2) && !defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)
    if (sha1_avx2_capable()) {
      CHECK_ABI(sha1_block_data_order_avx2, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA1_ASM_AVX) && !defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)
    if (sha1_avx_capable()) {
      CHECK_ABI(sha1_block_data_order_avx, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA1_ASM_SSSE3)
    if (sha1_ssse3_capable()) {
      CHECK_ABI(sha1_block_data_order_ssse3, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA1_ASM_NEON)
    if (CRYPTO_is_NEON_capable()) {
      CHECK_ABI(sha1_block_data_order_neon, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA1_ASM_NOHW)
    CHECK_ABI(sha1_block_data_order_nohw, ctx.h, kBuf, blocks);
#endif
  }
}

TEST(SHATest, SHA256ABI) {
  SHA256_CTX ctx;
  SHA256_Init(&ctx);

  static const uint8_t kBuf[SHA256_CBLOCK * 8] = {0};
  for (size_t blocks : {1, 2, 4, 8}) {
#if defined(SHA256_ASM)
    CHECK_ABI(sha256_block_data_order, ctx.h, kBuf, blocks);
#endif
#if defined(SHA256_ASM_HW)
    if (sha256_hw_capable()) {
      CHECK_ABI(sha256_block_data_order_hw, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA256_ASM_AVX) && !defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)
    if (sha256_avx_capable()) {
      CHECK_ABI(sha256_block_data_order_avx, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA256_ASM_SSSE3)
    if (sha256_ssse3_capable()) {
      CHECK_ABI(sha256_block_data_order_ssse3, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA256_ASM_NEON)
    if (CRYPTO_is_NEON_capable()) {
      CHECK_ABI(sha256_block_data_order_neon, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA256_ASM_NOHW)
    CHECK_ABI(sha256_block_data_order_nohw, ctx.h, kBuf, blocks);
#endif
  }
}

TEST(SHATest, SHA512ABI) {
  SHA512_CTX ctx;
  SHA512_Init(&ctx);

  static const uint8_t kBuf[SHA512_CBLOCK * 4] = {0};
  for (size_t blocks : {1, 2, 3, 4}) {
#if defined(SHA512_ASM)
    CHECK_ABI(sha512_block_data_order, ctx.h, kBuf, blocks);
#endif
#if defined(SHA512_ASM_HW)
    if (sha512_hw_capable()) {
      CHECK_ABI(sha512_block_data_order_hw, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA512_ASM_AVX) && !defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)
    if (sha512_avx_capable()) {
      CHECK_ABI(sha512_block_data_order_avx, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA512_ASM_NEON)
    if (CRYPTO_is_NEON_capable()) {
      CHECK_ABI(sha512_block_data_order_neon, ctx.h, kBuf, blocks);
    }
#endif
#if defined(SHA512_ASM_NOHW)
    CHECK_ABI(sha512_block_data_order_nohw, ctx.h, kBuf, blocks);
#endif
  }
}

#endif // defined(SUPPORTS_ABI_TEST) && !defined(SHA1_ALTIVEC)

#if defined(SUPPORTS_ABI_TEST) && defined(OPENSSL_X86_64) && \
    defined(OPENSSL_WINDOWS) && defined(_MSC_VER)
// The SHA-256 and SHA-512 x86_64 assembly installs |se_handler| as its Win64
// SEH language handler, to restore the caller's non-volatile registers when an
// exception unwinds through it. |CHECK_ABI_SEH| does not cover this, because
// the unwind tester calls |RtlVirtualUnwind| with |UNW_FLAG_NHANDLER| and never
// invokes language handlers. Instead, fault inside each variant on a
// |PAGE_NOACCESS| page and invoke its language handler as the exception
// dispatcher would.

namespace {

struct SEHHandlerResult {
  bool faulted;
  bool invoked_handler;
  // unwound receives the context of |abi_test_trampoline| after the language
  // handler unwinds the faulting function.
  CONTEXT *unwound;
};

// InvokeLanguageHandler is an exception filter. If |info| is an access
// violation on |guard|, it invokes the language handler of the faulting
// function, as the exception dispatcher would, and records the unwound context
// in |out|. It must run as a filter, while the faulting frame is still on the
// stack.
LONG InvokeLanguageHandler(EXCEPTION_POINTERS *info, uintptr_t guard,
                           size_t guard_len, SEHHandlerResult *out) {
  EXCEPTION_RECORD *record = info->ExceptionRecord;
  if (record->ExceptionCode != EXCEPTION_ACCESS_VIOLATION ||
      record->NumberParameters < 2 ||
      record->ExceptionInformation[1] < guard ||
      record->ExceptionInformation[1] - guard >= guard_len) {
    return EXCEPTION_CONTINUE_SEARCH;
  }
  out->faulted = true;

  const DWORD64 pc = info->ContextRecord->Rip;
  DWORD64 image_base = 0;
  PRUNTIME_FUNCTION entry = RtlLookupFunctionEntry(pc, &image_base, nullptr);
  if (entry == nullptr) {
    return EXCEPTION_EXECUTE_HANDLER;
  }

  // Look up the language handler and its HandlerData. This also unwinds
  // |scratch|, which is discarded.
  CONTEXT scratch = *info->ContextRecord;
  void *handler_data = nullptr;
  DWORD64 establisher_frame = 0;
  PEXCEPTION_ROUTINE handler =
      RtlVirtualUnwind(UNW_FLAG_EHANDLER, image_base, pc, entry, &scratch,
                       &handler_data, &establisher_frame, nullptr);
  if (handler == nullptr) {
    return EXCEPTION_EXECUTE_HANDLER;
  }

  // The handler fixes up |context|, copies it to |disp.ContextRecord|, and
  // unwinds that copy to the caller.
  CONTEXT context = *info->ContextRecord;
  DISPATCHER_CONTEXT disp;
  OPENSSL_memset(&disp, 0, sizeof(disp));
  disp.ControlPc = pc;
  disp.ImageBase = image_base;
  disp.FunctionEntry = entry;
  disp.EstablisherFrame = establisher_frame;
  disp.ContextRecord = out->unwound;
  disp.LanguageHandler = handler;
  disp.HandlerData = handler_data;
  handler(record, reinterpret_cast<void *>(establisher_frame), &context, &disp);
  out->invoked_handler = true;
  return EXCEPTION_EXECUTE_HANDLER;
}

// CallUntilFault calls |func| on |argv| through |abi_test_trampoline|, with
// the callee-saved registers loaded from |state|. |func| is expected to fault
// on |guard|. This function must not have objects with destructors, so that it
// may use |__try|.
void CallUntilFault(crypto_word_t func, abi_test::internal::CallerState *state,
                    const crypto_word_t *argv, size_t argc, uintptr_t guard,
                    size_t guard_len, SEHHandlerResult *out) {
  __try {
    abi_test_trampoline(func, state, argv, argc, /*unwind=*/0);
  } __except (InvokeLanguageHandler(GetExceptionInformation(), guard,
                                    guard_len, out)) {
  }
}

struct VirtualFreeDeleter {
  void operator()(uint8_t *ptr) { VirtualFree(ptr, 0, MEM_RELEASE); }
};

}  // namespace

TEST(SHATest, SEHHandlerRestoresCallerState) {
  struct Variant {
    const char *name;
    crypto_word_t func;
    size_t block_size;
    bool capable;
  };
  const Variant kVariants[] = {
#if defined(SHA256_ASM_NOHW)
      {"sha256_block_data_order_nohw",
       reinterpret_cast<crypto_word_t>(sha256_block_data_order_nohw),
       SHA256_CBLOCK, true},
#endif
#if defined(SHA256_ASM_SSSE3)
      {"sha256_block_data_order_ssse3",
       reinterpret_cast<crypto_word_t>(sha256_block_data_order_ssse3),
       SHA256_CBLOCK, sha256_ssse3_capable() != 0},
#endif
#if defined(SHA256_ASM_AVX) && !defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)
      {"sha256_block_data_order_avx",
       reinterpret_cast<crypto_word_t>(sha256_block_data_order_avx),
       SHA256_CBLOCK, sha256_avx_capable() != 0},
#endif
#if defined(SHA512_ASM_NOHW)
      {"sha512_block_data_order_nohw",
       reinterpret_cast<crypto_word_t>(sha512_block_data_order_nohw),
       SHA512_CBLOCK, true},
#endif
#if defined(SHA512_ASM_AVX) && !defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)
      {"sha512_block_data_order_avx",
       reinterpret_cast<crypto_word_t>(sha512_block_data_order_avx),
       SHA512_CBLOCK, sha512_avx_capable() != 0},
#endif
  };

  // Map two pages and make the second inaccessible. The first block of input
  // ends at the page boundary, so each variant faults when it reads the
  // second block, inside its body.
  SYSTEM_INFO system_info;
  GetSystemInfo(&system_info);
  const size_t page_size = system_info.dwPageSize;
  std::unique_ptr<uint8_t, VirtualFreeDeleter> pages(
      static_cast<uint8_t *>(VirtualAlloc(nullptr, 2 * page_size,
                                          MEM_COMMIT | MEM_RESERVE,
                                          PAGE_READWRITE)));
  ASSERT_TRUE(pages);
  uint8_t *guard = pages.get() + page_size;
  DWORD old_protect;
  ASSERT_TRUE(VirtualProtect(guard, page_size, PAGE_NOACCESS, &old_protect));

  for (const Variant &variant : kVariants) {
    SCOPED_TRACE(variant.name);
    if (!variant.capable) {
      continue;
    }
    // |se_handler| decides whether to restore xmm6+ by where the fault is.
    // The caller's %rbx must not influence that, so test a value below and a
    // value above every code address.
    for (uint64_t rbx : {uint64_t{0}, ~uint64_t{0}}) {
      SCOPED_TRACE(rbx);
      abi_test::internal::CallerState state;
      uint8_t *state_bytes = reinterpret_cast<uint8_t *>(&state);
      for (size_t i = 0; i < sizeof(state); i++) {
        state_bytes[i] = static_cast<uint8_t>(0x80 + i);
      }
      state.rbx = rbx;
      const abi_test::internal::CallerState expected = state;

      alignas(16) uint64_t hash_state[8] = {0};
      uint8_t *data = guard - variant.block_size;
      OPENSSL_memset(data, 'a', variant.block_size);
      const crypto_word_t argv[] = {
          reinterpret_cast<crypto_word_t>(hash_state),
          reinterpret_cast<crypto_word_t>(data),
          2,  // The second block is on the guard page.
      };
      CONTEXT unwound;
      OPENSSL_memset(&unwound, 0, sizeof(unwound));
      SEHHandlerResult result = {false, false, &unwound};
      CallUntilFault(variant.func, &state, argv, OPENSSL_ARRAY_SIZE(argv),
                     reinterpret_cast<uintptr_t>(guard), page_size, &result);
      ASSERT_TRUE(result.faulted);
      ASSERT_TRUE(result.invoked_handler);

      // The unwound context must hold the caller's callee-saved registers.
      const CONTEXT &ctx = unwound;
      abi_test::internal::CallerState actual;
      actual.rbx = ctx.Rbx;
      actual.rbp = ctx.Rbp;
      actual.rdi = ctx.Rdi;
      actual.rsi = ctx.Rsi;
      actual.r12 = ctx.R12;
      actual.r13 = ctx.R13;
      actual.r14 = ctx.R14;
      actual.r15 = ctx.R15;
      OPENSSL_memcpy(&actual.xmm6, &ctx.Xmm6, sizeof(actual.xmm6));
      OPENSSL_memcpy(&actual.xmm7, &ctx.Xmm7, sizeof(actual.xmm7));
      OPENSSL_memcpy(&actual.xmm8, &ctx.Xmm8, sizeof(actual.xmm8));
      OPENSSL_memcpy(&actual.xmm9, &ctx.Xmm9, sizeof(actual.xmm9));
      OPENSSL_memcpy(&actual.xmm10, &ctx.Xmm10, sizeof(actual.xmm10));
      OPENSSL_memcpy(&actual.xmm11, &ctx.Xmm11, sizeof(actual.xmm11));
      OPENSSL_memcpy(&actual.xmm12, &ctx.Xmm12, sizeof(actual.xmm12));
      OPENSSL_memcpy(&actual.xmm13, &ctx.Xmm13, sizeof(actual.xmm13));
      OPENSSL_memcpy(&actual.xmm14, &ctx.Xmm14, sizeof(actual.xmm14));
      OPENSSL_memcpy(&actual.xmm15, &ctx.Xmm15, sizeof(actual.xmm15));
#define CALLER_STATE_REGISTER(type, name)                                   \
  EXPECT_EQ(Bytes(reinterpret_cast<const uint8_t *>(&expected.name),       \
                  sizeof(expected.name)),                                  \
            Bytes(reinterpret_cast<const uint8_t *>(&actual.name),         \
                  sizeof(expected.name)))                                 \
      << #name;
      LOOP_CALLER_STATE_REGISTERS()
#undef CALLER_STATE_REGISTER
    }
  }
}
#endif  // SUPPORTS_ABI_TEST && X86_64 && WINDOWS && _MSC_VER
