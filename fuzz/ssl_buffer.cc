// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/span.h>
#include "../ssl/internal.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  CBS cbs;
  CBS_init(&cbs, buf, len);

  bssl::SSLBuffer buffer;

  if (!buffer.DoDeserialization(cbs)) {
    return 0;
  }

  // See if we can serialize it back
  bssl::ScopedCBB cbb;
  CBB_init(cbb.get(), len);
  if (!buffer.DoSerialization(*cbb.get())) {
    return 1;
  }
  cbb.Reset();

  // If the restore buffer is not empty lets use it
  if (!buffer.empty()) {
    // Get a view to the written but not discarded data and verify
    // we can safely read it all.
    auto span = buffer.span();
    {
      volatile const uint8_t *vp = span.data();
      for (size_t i = 0; i < span.size(); i++) {
        uint8_t v = vp[i];
        (void)v;
      }
    }
    // Now "consume" the content we read which moves offset_ forward and reduces size_ and cap_.
    buffer.Consume(span.size());

    // Serialize the read span we were using. This is valid and allowed use case
    // as the data is still kept until we call discard.
    bssl::ScopedCBB spanCBB;
    CBB_init(spanCBB.get(), span.size());
    if (!buffer.SerializeBufferView(*spanCBB.get(), span)) {
      return 1;
    }

    // Serialize the current buffer state, we should be able to restore it
    // and restore the span and use it safely.
    CBB_init(cbb.get(), len);
    if (!buffer.DoSerialization(*cbb.get())) {
      return 1;
    }

    // Now let's try to fill the rest of the buffer's remaining space
    {
      // Fill the remaining capacity with 1's
      auto remaining = buffer.remaining();
      memset(remaining.data(), 1, remaining.size());
      buffer.DidWrite(remaining.size());

      // Since we told the buffer we wrote remaining.size(), then the
      // buffer.span() should now point to that content.
      auto remSpan = buffer.span();
      if (remSpan.size() != remaining.size()) {
        return 1;
      }

      // Validate we read all 1's
      for (size_t i = 0; i < remSpan.size(); i++) {
        uint8_t v = remSpan.data()[i];
        if (v != 1) {
          return 1;
        }
      }

      // Inform that we have now consumed the data
      buffer.Consume(remSpan.size());
      remaining = buffer.remaining();

      // There should be no space left...
      if (remaining.size() != 0) {
        return 1;
      }

      // This should cause the buffer to be free'd
      buffer.DiscardConsumed();
      if (buffer.buf_ptr() != nullptr) {
        return 1;
      }
    }

    // Reset to the serialized version before the above writes
    CBS_init(&cbs, CBB_data(cbb.get()), CBB_len(cbb.get()));
    if (!buffer.DoDeserialization(cbs)) {
      return 1;
    }

    // Restore the span to the earlier data we consumed
    CBS_init(&cbs, CBB_data(spanCBB.get()), CBB_len(spanCBB.get()));
    if (!buffer.DeserializeBufferView(cbs, span)) {
      return 1;
    }

    // We should still be able to safely read the data the span referred to.
    {
      volatile const uint8_t *vp = span.data();
      for (size_t i = 0; i < span.size(); i++) {
        uint8_t v = vp[i];
        (void)v;
      }
    }
  }

  // let's try to fill the rest of the buffer's remaining space.
  // We did this earlier if the buffer was not empty as well.
  {
    // Fill the remaining capacity with 1's
    auto remaining = buffer.remaining();
    memset(remaining.data(), 1, remaining.size());
    buffer.DidWrite(remaining.size());

    // Since we told the buffer we wrote remaining.size(), then the
    // buffer.span() should now point to that content.
    auto span = buffer.span();
    if (span.size() != remaining.size()) {
      return 1;
    }

    // Validate we read all 1's
    for (size_t i = 0; i < span.size(); i++) {
      uint8_t v = span.data()[i];
      if (v != 1) {
        return 1;
      }
    }

    // Inform that we have now consumed the data
    buffer.Consume(span.size());
    remaining = buffer.remaining();

    // There should be no space left...
    if (remaining.size() != 0) {
      return 1;
    }

    // This should cause the buffer to be free'd
    buffer.DiscardConsumed();
    if (buffer.buf_ptr() != nullptr) {
      return 1;
    }
  }

  return 0;
}
