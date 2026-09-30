// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include "x509_view.h"

#include <limits.h>
#include <string.h>

#include "../internal.h"

#if defined(__GNUC__) || defined(__clang__)
#define C_VIEW_INLINE static inline __attribute__((always_inline))
#define C_VIEW_FLATTEN __attribute__((flatten))
#define C_VIEW_LIKELY(x) __builtin_expect(!!(x), 1)
#define C_VIEW_UNLIKELY(x) __builtin_expect(!!(x), 0)
#else
#define C_VIEW_INLINE static inline
#define C_VIEW_FLATTEN
#define C_VIEW_LIKELY(x) (x)
#define C_VIEW_UNLIKELY(x) (x)
#endif

typedef struct {
  const uint8_t *root;
  const uint8_t *ptr;
  const uint8_t *end;
} C_VIEW_CURSOR;

typedef struct {
  const uint8_t *encoded;
  const uint8_t *content;
  uint32_t encoded_len;
  uint32_t content_len;
  uint8_t first_octet;
} C_VIEW_TLV;

// Keep the view parser within the bound enforced by x_name.c's legacy decoder.
#define C_VIEW_X509_NAME_MAX (1024u * 1024u)

C_VIEW_INLINE C_VIEW_CURSOR c_view_cursor(const uint8_t *root,
                                          const uint8_t *content,
                                          uint32_t content_len) {
  C_VIEW_CURSOR cursor = {root, content, content + content_len};
  return cursor;
}

C_VIEW_INLINE AWSLC_X509_DER_RANGE c_view_range(const C_VIEW_CURSOR *cursor,
                                                const C_VIEW_TLV *tlv) {
  AWSLC_X509_DER_RANGE range = {
      (uint32_t)(tlv->encoded - cursor->root),
      tlv->encoded_len,
  };
  return range;
}

C_VIEW_INLINE AWSLC_X509_DER_RANGE
c_view_content_range(const C_VIEW_CURSOR *cursor, const C_VIEW_TLV *tlv) {
  AWSLC_X509_DER_RANGE range = {
      (uint32_t)(tlv->content - cursor->root),
      tlv->content_len,
  };
  return range;
}

C_VIEW_INLINE uint32_t c_view_read_body(C_VIEW_CURSOR *cursor,
                                        const uint8_t *encoded,
                                        uint8_t first_octet, C_VIEW_TLV *out) {
  if (C_VIEW_UNLIKELY(cursor->ptr == cursor->end)) {
    return AWSLC_X509_PARSE_TRUNCATED;
  }

  const uint8_t first_len = *cursor->ptr++;
  uint32_t content_len = 0;
  if (C_VIEW_LIKELY((first_len & 0x80) == 0)) {
    content_len = first_len;
  } else {
    const uint32_t octets = first_len & 0x7f;
    if (C_VIEW_UNLIKELY(octets == 0 || octets > sizeof(uint32_t))) {
      return AWSLC_X509_PARSE_INVALID_LENGTH;
    }
    if (C_VIEW_UNLIKELY((size_t)(cursor->end - cursor->ptr) < octets)) {
      return AWSLC_X509_PARSE_TRUNCATED;
    }
    if (C_VIEW_UNLIKELY(cursor->ptr[0] == 0)) {
      return AWSLC_X509_PARSE_INVALID_LENGTH;
    }

    content_len = 0;
    for (uint32_t i = 0; i < octets; i++) {
      content_len = (content_len << 8) | cursor->ptr[i];
    }
    cursor->ptr += octets;
    if (C_VIEW_UNLIKELY(content_len < 128)) {
      return AWSLC_X509_PARSE_INVALID_LENGTH;
    }
  }

  if (C_VIEW_UNLIKELY((size_t)(cursor->end - cursor->ptr) < content_len)) {
    return AWSLC_X509_PARSE_TRUNCATED;
  }

  out->encoded = encoded;
  out->content = cursor->ptr;
  out->content_len = content_len;
  cursor->ptr += content_len;
  out->encoded_len = (uint32_t)(cursor->ptr - encoded);
  out->first_octet = first_octet;
  return AWSLC_X509_PARSE_OK;
}

C_VIEW_INLINE uint32_t c_view_read_tlv(C_VIEW_CURSOR *cursor, C_VIEW_TLV *out) {
  if (C_VIEW_UNLIKELY(cursor->ptr == cursor->end)) {
    return AWSLC_X509_PARSE_TRUNCATED;
  }

  const uint8_t *encoded = cursor->ptr;
  const uint8_t first = *cursor->ptr++;
  if (C_VIEW_UNLIKELY((first & 0x1f) == 0x1f)) {
    uint32_t number = 0;
    int is_first = 1;
    for (;;) {
      if (C_VIEW_UNLIKELY(cursor->ptr == cursor->end)) {
        return AWSLC_X509_PARSE_TRUNCATED;
      }
      const uint8_t byte = *cursor->ptr++;
      if (C_VIEW_UNLIKELY(is_first && (byte & 0x7f) == 0)) {
        return AWSLC_X509_PARSE_INVALID_TAG;
      }
      is_first = 0;
      if (C_VIEW_UNLIKELY(number > (UINT32_MAX - (byte & 0x7f)) / 128)) {
        return AWSLC_X509_PARSE_INVALID_TAG;
      }
      number = number * 128 + (byte & 0x7f);
      if ((byte & 0x80) == 0) {
        break;
      }
    }
    if (C_VIEW_UNLIKELY(number < 31)) {
      return AWSLC_X509_PARSE_INVALID_TAG;
    }
  }

  return c_view_read_body(cursor, encoded, first, out);
}

C_VIEW_INLINE uint32_t c_view_expect(C_VIEW_CURSOR *cursor, uint8_t expected,
                                     C_VIEW_TLV *out) {
  if (C_VIEW_UNLIKELY(cursor->ptr == cursor->end)) {
    return AWSLC_X509_PARSE_TRUNCATED;
  }
  if (C_VIEW_UNLIKELY(*cursor->ptr != expected)) {
    return AWSLC_X509_PARSE_INVALID_TAG;
  }

  const uint8_t *encoded = cursor->ptr++;
  return c_view_read_body(cursor, encoded, expected, out);
}

C_VIEW_INLINE uint32_t c_view_finish(const C_VIEW_CURSOR *cursor) {
  return cursor->ptr == cursor->end ? AWSLC_X509_PARSE_OK
                                    : AWSLC_X509_PARSE_TRAILING_DATA;
}

C_VIEW_INLINE uint32_t c_view_validate_integer_content(const C_VIEW_TLV *tlv) {
  if (C_VIEW_UNLIKELY(tlv->content_len == 0)) {
    return AWSLC_X509_PARSE_INVALID_VALUE;
  }
  if (tlv->content_len > 1) {
    const uint8_t first = tlv->content[0];
    const uint8_t second = tlv->content[1];
    if (C_VIEW_UNLIKELY((first == 0 && (second & 0x80) == 0) ||
                        (first == 0xff && (second & 0x80) != 0))) {
      return AWSLC_X509_PARSE_INVALID_VALUE;
    }
  }
  return AWSLC_X509_PARSE_OK;
}

C_VIEW_INLINE uint32_t c_view_validate_integer(const C_VIEW_TLV *tlv) {
  if (C_VIEW_UNLIKELY(tlv->first_octet != 0x02)) {
    return AWSLC_X509_PARSE_INVALID_TAG;
  }
  return c_view_validate_integer_content(tlv);
}

C_VIEW_INLINE uint32_t c_view_validate_oid(const C_VIEW_TLV *tlv) {
  if (C_VIEW_UNLIKELY(tlv->first_octet != 0x06)) {
    return AWSLC_X509_PARSE_INVALID_TAG;
  }
  if (C_VIEW_UNLIKELY(tlv->content_len == 0)) {
    return AWSLC_X509_PARSE_INVALID_VALUE;
  }

  const uint8_t *ptr = tlv->content;
  const uint8_t *end = ptr + tlv->content_len;
  while (ptr != end) {
    // A subidentifier may not begin with 0x80: that is a non-minimal encoding.
    if (C_VIEW_UNLIKELY(*ptr == 0x80)) {
      return AWSLC_X509_PARSE_INVALID_VALUE;
    }
    // Consume continuation octets, then the subidentifier's final octet. Both
    // bounds are explicit, so the loop is bounded by |content_len|.
    while (*ptr & 0x80) {
      ptr++;
      if (C_VIEW_UNLIKELY(ptr == end)) {
        return AWSLC_X509_PARSE_TRUNCATED;
      }
    }
    ptr++;
  }
  return AWSLC_X509_PARSE_OK;
}

C_VIEW_INLINE uint32_t c_view_validate_bit_string_content(
    const uint8_t *content, uint32_t content_len) {
  if (C_VIEW_UNLIKELY(content_len == 0)) {
    return AWSLC_X509_PARSE_INVALID_VALUE;
  }
  const uint8_t unused = content[0];
  if (C_VIEW_UNLIKELY(unused > 7 || (content_len == 1 && unused != 0))) {
    return AWSLC_X509_PARSE_INVALID_VALUE;
  }
  if (unused != 0) {
    const uint8_t mask = (uint8_t)((1u << unused) - 1);
    if (C_VIEW_UNLIKELY((content[content_len - 1] & mask) != 0)) {
      return AWSLC_X509_PARSE_INVALID_VALUE;
    }
  }
  return AWSLC_X509_PARSE_OK;
}

C_VIEW_INLINE uint32_t c_view_validate_bit_string(const C_VIEW_TLV *tlv) {
  if (C_VIEW_UNLIKELY(tlv->first_octet != 0x03)) {
    return AWSLC_X509_PARSE_INVALID_TAG;
  }
  return c_view_validate_bit_string_content(tlv->content, tlv->content_len);
}

static uint32_t c_view_validate_any(const C_VIEW_TLV *tlv);

static uint32_t c_view_validate_algorithm(const C_VIEW_CURSOR *parent,
                                          const C_VIEW_TLV *algorithm) {
  C_VIEW_CURSOR fields =
      c_view_cursor(parent->root, algorithm->content, algorithm->content_len);
  C_VIEW_TLV oid;
  uint32_t result = c_view_expect(&fields, 0x06, &oid);
  if (result != AWSLC_X509_PARSE_OK ||
      c_view_validate_oid(&oid) != AWSLC_X509_PARSE_OK) {
    return AWSLC_X509_PARSE_INVALID_ALGORITHM;
  }
  if (fields.ptr != fields.end) {
    C_VIEW_TLV parameters;
    if (c_view_read_tlv(&fields, &parameters) != AWSLC_X509_PARSE_OK ||
        c_view_validate_any(&parameters) != AWSLC_X509_PARSE_OK) {
      return AWSLC_X509_PARSE_INVALID_ALGORITHM;
    }
  }
  return fields.ptr == fields.end ? AWSLC_X509_PARSE_OK
                                  : AWSLC_X509_PARSE_INVALID_ALGORITHM;
}

C_VIEW_INLINE int c_view_der_less_or_equal(const C_VIEW_TLV *left,
                                           const C_VIEW_TLV *right) {
  // X.690 compares SET OF encodings after zero-padding the shorter value. For
  // equal-tag TLVs, unequal lengths differ in the length octets before padding
  // can affect the result.
  const size_t common = left->encoded_len < right->encoded_len
                            ? left->encoded_len
                            : right->encoded_len;
  const int order = memcmp(left->encoded, right->encoded, common);
  return order < 0 || (order == 0 && left->encoded_len <= right->encoded_len);
}

static int c_view_valid_code_point(uint32_t value) {
  return value <= 0x10ffff && (value & 0xfffe) != 0xfffe &&
         (value < 0xfdd0 || value > 0xfdef) &&
         (value < 0xd800 || value > 0xdfff);
}

static int c_view_validate_utf8(const uint8_t *data, uint32_t len) {
  const uint8_t *end = data + len;
  while (data != end) {
    const uint8_t first = *data++;
    uint32_t value = 0;
    uint32_t remaining = 0;
    uint32_t minimum = 0;
    if (first <= 0x7f) {
      continue;
    } else if ((first & 0xe0) == 0xc0) {
      value = first & 0x1f;
      remaining = 1;
      minimum = 0x80;
    } else if ((first & 0xf0) == 0xe0) {
      value = first & 0x0f;
      remaining = 2;
      minimum = 0x800;
    } else if ((first & 0xf8) == 0xf0) {
      value = first & 0x07;
      remaining = 3;
      minimum = 0x10000;
    } else {
      return 0;
    }
    if ((size_t)(end - data) < remaining) {
      return 0;
    }
    for (uint32_t i = 0; i < remaining; i++) {
      if ((data[i] & 0xc0) != 0x80) {
        return 0;
      }
      value = (value << 6) | (data[i] & 0x3f);
    }
    data += remaining;
    if (value < minimum || !c_view_valid_code_point(value)) {
      return 0;
    }
  }
  return 1;
}

// ASN1_mbstring_ncopy rejects a byte-order mark as the first character of a
// BMPString or UniversalString, and X509_NAME canonicalization always runs it
// for these types. Reject it here too so the view parser's accepted language
// stays a strict subset of the legacy decoder's: otherwise d2i_X509 accepts a
// certificate whose issuer or subject can never be materialized.
#define C_VIEW_BYTE_ORDER_MARK 0xfeffu

static int c_view_validate_bmp_string(const uint8_t *data, uint32_t len) {
  if ((len & 1) != 0) {
    return 0;
  }
  for (uint32_t i = 0; i < len; i += 2) {
    const uint32_t value = ((uint32_t)data[i] << 8) | data[i + 1];
    if (!c_view_valid_code_point(value)) {
      return 0;
    }
    if (i == 0 && value == C_VIEW_BYTE_ORDER_MARK) {
      return 0;
    }
  }
  return 1;
}

static int c_view_validate_universal_string(const uint8_t *data, uint32_t len) {
  if ((len & 3) != 0) {
    return 0;
  }
  for (uint32_t i = 0; i < len; i += 4) {
    const uint32_t value = ((uint32_t)data[i] << 24) |
                           ((uint32_t)data[i + 1] << 16) |
                           ((uint32_t)data[i + 2] << 8) | data[i + 3];
    if (!c_view_valid_code_point(value)) {
      return 0;
    }
    if (i == 0 && value == C_VIEW_BYTE_ORDER_MARK) {
      return 0;
    }
  }
  return 1;
}

static uint32_t c_view_validate_name_value(const C_VIEW_TLV *value) {
  // X509_NAME_ENTRY uses ASN1_PRINTABLE, an OpenSSL-specific MSTRING. Keep
  // this list in sync with B_ASN1_PRINTABLE and tag2bit in tasn_dec.c. This
  // parser only accepts primitive string encodings, except for SEQUENCE.
  switch (value->first_octet) {
    case 0x03:  // BIT STRING
      return c_view_validate_bit_string(value);
    case 0x0a:  // ENUMERATED maps to B_ASN1_UNKNOWN.
      return c_view_validate_integer_content(value);
    case 0x0c:  // UTF8STRING
      return c_view_validate_utf8(value->content, value->content_len)
                 ? AWSLC_X509_PARSE_OK
                 : AWSLC_X509_PARSE_INVALID_NAME;
    case 0x1c:  // UNIVERSALSTRING
      return c_view_validate_universal_string(value->content,
                                              value->content_len)
                 ? AWSLC_X509_PARSE_OK
                 : AWSLC_X509_PARSE_INVALID_NAME;
    case 0x1e:  // BMPSTRING
      return c_view_validate_bmp_string(value->content, value->content_len)
                 ? AWSLC_X509_PARSE_OK
                 : AWSLC_X509_PARSE_INVALID_NAME;
    case 0x30:  // SEQUENCE
      return AWSLC_X509_PARSE_OK;
    case 0x07:  // ObjectDescriptor
    case 0x08:  // EXTERNAL
    case 0x09:  // REAL
    case 0x0b:  // EMBEDDED PDV
    case 0x0d:  // RELATIVE-OID
    case 0x0e:  // TIME
    case 0x0f:  // Reserved
    case 0x12:  // NUMERICSTRING
    case 0x13:  // PRINTABLESTRING
    case 0x14:  // T61STRING
    case 0x16:  // IA5STRING
    case 0x1d:  // CHARACTER STRING
      return AWSLC_X509_PARSE_OK;
    default:
      return AWSLC_X509_PARSE_INVALID_NAME;
  }
}

static uint32_t c_view_validate_attribute(const C_VIEW_CURSOR *parent,
                                          const C_VIEW_TLV *attribute) {
  C_VIEW_CURSOR fields =
      c_view_cursor(parent->root, attribute->content, attribute->content_len);
  C_VIEW_TLV oid, value;
  uint32_t result = c_view_expect(&fields, 0x06, &oid);
  if (result != AWSLC_X509_PARSE_OK ||
      c_view_validate_oid(&oid) != AWSLC_X509_PARSE_OK ||
      c_view_read_tlv(&fields, &value) != AWSLC_X509_PARSE_OK ||
      c_view_validate_name_value(&value) != AWSLC_X509_PARSE_OK ||
      fields.ptr != fields.end) {
    return AWSLC_X509_PARSE_INVALID_NAME;
  }
  return AWSLC_X509_PARSE_OK;
}

static uint32_t c_view_validate_rdn(const C_VIEW_CURSOR *parent,
                                    const C_VIEW_TLV *rdn) {
  if (C_VIEW_UNLIKELY(rdn->content_len == 0)) {
    return AWSLC_X509_PARSE_INVALID_NAME;
  }

  C_VIEW_CURSOR set =
      c_view_cursor(parent->root, rdn->content, rdn->content_len);
  C_VIEW_TLV previous;
  OPENSSL_memset(&previous, 0, sizeof(previous));
  int have_previous = 0;
  while (set.ptr != set.end) {
    C_VIEW_TLV attribute;
    if (c_view_expect(&set, 0x30, &attribute) != AWSLC_X509_PARSE_OK) {
      return AWSLC_X509_PARSE_INVALID_NAME;
    }
    if (have_previous && !c_view_der_less_or_equal(&previous, &attribute)) {
      return AWSLC_X509_PARSE_INVALID_NAME;
    }
    if (c_view_validate_attribute(parent, &attribute) != AWSLC_X509_PARSE_OK) {
      return AWSLC_X509_PARSE_INVALID_NAME;
    }
    previous = attribute;
    have_previous = 1;
  }
  return AWSLC_X509_PARSE_OK;
}

static uint32_t c_view_validate_name(const C_VIEW_CURSOR *parent,
                                     const C_VIEW_TLV *name) {
  if (C_VIEW_UNLIKELY(name->first_octet != 0x30 ||
                      name->encoded_len > C_VIEW_X509_NAME_MAX)) {
    return AWSLC_X509_PARSE_INVALID_NAME;
  }

  C_VIEW_CURSOR sequence =
      c_view_cursor(parent->root, name->content, name->content_len);
  while (sequence.ptr != sequence.end) {
    C_VIEW_TLV rdn;
    if (c_view_expect(&sequence, 0x31, &rdn) != AWSLC_X509_PARSE_OK ||
        c_view_validate_rdn(parent, &rdn) != AWSLC_X509_PARSE_OK) {
      return AWSLC_X509_PARSE_INVALID_NAME;
    }
  }
  return AWSLC_X509_PARSE_OK;
}

C_VIEW_INLINE int c_view_decimal2(const uint8_t *input, uint32_t *out) {
  const uint8_t a = input[0];
  const uint8_t b = input[1];
  if (C_VIEW_UNLIKELY(a < '0' || a > '9' || b < '0' || b > '9')) {
    return 0;
  }
  *out = (uint32_t)(a - '0') * 10 + (uint32_t)(b - '0');
  return 1;
}

static uint32_t c_view_validate_time(const C_VIEW_TLV *time) {
  uint32_t year = 0;
  uint32_t month_offset = 0;
  if (time->first_octet == 0x17) {
    if (C_VIEW_UNLIKELY(time->content_len != 13) ||
        !c_view_decimal2(time->content, &year)) {
      return AWSLC_X509_PARSE_INVALID_TIME;
    }
    year += year >= 50 ? 1900 : 2000;
    month_offset = 2;
  } else if (time->first_octet == 0x18) {
    uint32_t century = 0, short_year = 0;
    if (C_VIEW_UNLIKELY(time->content_len != 15) ||
        !c_view_decimal2(time->content, &century) ||
        !c_view_decimal2(time->content + 2, &short_year)) {
      return AWSLC_X509_PARSE_INVALID_TIME;
    }
    year = century * 100 + short_year;
    month_offset = 4;
  } else {
    return AWSLC_X509_PARSE_INVALID_TIME;
  }

  if (C_VIEW_UNLIKELY(time->content[time->content_len - 1] != 'Z')) {
    return AWSLC_X509_PARSE_INVALID_TIME;
  }

  uint32_t month = 0, day = 0, hour = 0, minute = 0, second = 0;
  if (C_VIEW_UNLIKELY(
          !c_view_decimal2(time->content + month_offset, &month) ||
          !c_view_decimal2(time->content + month_offset + 2, &day) ||
          !c_view_decimal2(time->content + month_offset + 4, &hour) ||
          !c_view_decimal2(time->content + month_offset + 6, &minute) ||
          !c_view_decimal2(time->content + month_offset + 8, &second))) {
    return AWSLC_X509_PARSE_INVALID_TIME;
  }

  uint32_t days = 31;
  if (month == 2) {
    days = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) ? 29 : 28;
  } else if (month == 4 || month == 6 || month == 9 || month == 11) {
    days = 30;
  }
  if (C_VIEW_UNLIKELY(month == 0 || month > 12 || day == 0 || day > days ||
                      hour > 23 || minute > 59 || second > 59)) {
    return AWSLC_X509_PARSE_INVALID_TIME;
  }
  return AWSLC_X509_PARSE_OK;
}

static uint32_t c_view_validate_any(const C_VIEW_TLV *tlv) {
  const uint8_t first = tlv->first_octet;

  // ASN1_ANY stores non-universal values as V_ASN1_OTHER in encoded form.
  if ((first & 0xc0) != 0) {
    return AWSLC_X509_PARSE_OK;
  }
  // High-tag-number universal values are not needed by AlgorithmIdentifier and
  // rejecting them keeps this parser a strict subset of the legacy decoder.
  if ((first & 0x1f) == 0x1f) {
    return AWSLC_X509_PARSE_INVALID_VALUE;
  }

  switch (first) {
    case 0x01:  // BOOLEAN
      return tlv->content_len == 1 ? AWSLC_X509_PARSE_OK
                                   : AWSLC_X509_PARSE_INVALID_VALUE;
    case 0x02:  // INTEGER
    case 0x0a:  // ENUMERATED
      return c_view_validate_integer_content(tlv);
    case 0x03:  // BIT STRING
      return c_view_validate_bit_string(tlv);
    case 0x05:  // NULL
      return tlv->content_len == 0 ? AWSLC_X509_PARSE_OK
                                   : AWSLC_X509_PARSE_INVALID_VALUE;
    case 0x06:  // OBJECT IDENTIFIER
      return c_view_validate_oid(tlv);
    case 0x10:  // Primitive SEQUENCE
    case 0x11:  // Primitive SET
      return AWSLC_X509_PARSE_INVALID_VALUE;
    case 0x17:  // UTCTime
    case 0x18:  // GeneralizedTime
      return c_view_validate_time(tlv);
    case 0x1c:  // UNIVERSALSTRING
      return (tlv->content_len & 3) == 0 ? AWSLC_X509_PARSE_OK
                                         : AWSLC_X509_PARSE_INVALID_VALUE;
    case 0x1e:  // BMPSTRING
      return (tlv->content_len & 1) == 0 ? AWSLC_X509_PARSE_OK
                                         : AWSLC_X509_PARSE_INVALID_VALUE;
    case 0x30:  // Constructed SEQUENCE
    case 0x31:  // Constructed SET
      return AWSLC_X509_PARSE_OK;
    default:
      // The legacy decoder accepts other primitive universal values as
      // ASN1_STRINGs. Constructed string encodings require recursive BER
      // collection, so leave those to the compatibility fallback.
      return (first & 0x20) == 0 && first != 0 ? AWSLC_X509_PARSE_OK
                                               : AWSLC_X509_PARSE_INVALID_VALUE;
  }
}

static uint32_t c_view_validate_validity(const C_VIEW_CURSOR *parent,
                                         const C_VIEW_TLV *validity) {
  C_VIEW_CURSOR fields =
      c_view_cursor(parent->root, validity->content, validity->content_len);
  C_VIEW_TLV not_before, not_after;
  uint32_t result = c_view_read_tlv(&fields, &not_before);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_time(&not_before);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_read_tlv(&fields, &not_after);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_time(&not_after);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  return c_view_finish(&fields);
}

static uint32_t c_view_validate_spki(const C_VIEW_CURSOR *parent,
                                     const C_VIEW_TLV *spki) {
  C_VIEW_CURSOR fields =
      c_view_cursor(parent->root, spki->content, spki->content_len);
  C_VIEW_TLV algorithm, public_key;
  uint32_t result = c_view_expect(&fields, 0x30, &algorithm);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_algorithm(parent, &algorithm);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_expect(&fields, 0x03, &public_key);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_bit_string(&public_key);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  return c_view_finish(&fields);
}

C_VIEW_INLINE int c_view_cached_extension_slot(const uint8_t *oid,
                                               uint32_t oid_len) {
  if (oid_len == 3 && oid[0] == 0x55 && oid[1] == 0x1d) {
    switch (oid[2]) {
      case 0x13:
        return AWSLC_X509_EXTENSION_BASIC_CONSTRAINTS;
      case 0x0f:
        return AWSLC_X509_EXTENSION_KEY_USAGE;
      case 0x25:
        return AWSLC_X509_EXTENSION_EXTENDED_KEY_USAGE;
      case 0x0e:
        return AWSLC_X509_EXTENSION_SUBJECT_KEY_IDENTIFIER;
      case 0x23:
        return AWSLC_X509_EXTENSION_AUTHORITY_KEY_IDENTIFIER;
      case 0x11:
        return AWSLC_X509_EXTENSION_SUBJECT_ALT_NAME;
      case 0x1e:
        return AWSLC_X509_EXTENSION_NAME_CONSTRAINTS;
      case 0x1f:
        return AWSLC_X509_EXTENSION_CRL_DISTRIBUTION_POINTS;
      default:
        return -1;
    }
  }
  static const uint8_t kNetscapeCertType[] = {0x60, 0x86, 0x48, 0x01, 0x86,
                                              0xf8, 0x42, 0x01, 0x01};
  if (oid_len == sizeof(kNetscapeCertType) &&
      memcmp(oid, kNetscapeCertType, sizeof(kNetscapeCertType)) == 0) {
    return AWSLC_X509_EXTENSION_NETSCAPE_CERT_TYPE;
  }
  return -1;
}

C_VIEW_INLINE int c_view_supported_critical_extension(const uint8_t *oid,
                                                      uint32_t oid_len) {
  if (oid_len == 3 && oid[0] == 0x55 && oid[1] == 0x1d) {
    switch (oid[2]) {
      case 0x0f:
      case 0x11:
      case 0x13:
      case 0x20:
      case 0x1f:
      case 0x25:
      case 0x24:
      case 0x1e:
      case 0x21:
      case 0x36:
        return 1;
      default:
        return 0;
    }
  }
  static const uint8_t kNetscapeCertType[] = {0x60, 0x86, 0x48, 0x01, 0x86,
                                              0xf8, 0x42, 0x01, 0x01};
  return oid_len == sizeof(kNetscapeCertType) &&
         memcmp(oid, kNetscapeCertType, sizeof(kNetscapeCertType)) == 0;
}

static uint32_t c_view_validate_extension(const C_VIEW_CURSOR *parent,
                                          const C_VIEW_TLV *extension,
                                          AWSLC_X509_CERTIFICATE_VIEW *view) {
  C_VIEW_CURSOR fields =
      c_view_cursor(parent->root, extension->content, extension->content_len);
  C_VIEW_TLV oid, value;
  if (c_view_expect(&fields, 0x06, &oid) != AWSLC_X509_PARSE_OK ||
      c_view_validate_oid(&oid) != AWSLC_X509_PARSE_OK) {
    return AWSLC_X509_PARSE_INVALID_EXTENSIONS;
  }

  int is_critical = 0;
  if (fields.ptr != fields.end && fields.ptr[0] == 0x01) {
    C_VIEW_TLV critical;
    if (c_view_expect(&fields, 0x01, &critical) != AWSLC_X509_PARSE_OK ||
        critical.content_len != 1 || critical.content[0] != 0xff) {
      return AWSLC_X509_PARSE_INVALID_EXTENSIONS;
    }
    is_critical = 1;
  }

  if (c_view_expect(&fields, 0x04, &value) != AWSLC_X509_PARSE_OK ||
      fields.ptr != fields.end) {
    return AWSLC_X509_PARSE_INVALID_EXTENSIONS;
  }

  const int slot = c_view_cached_extension_slot(oid.content, oid.content_len);
  if (slot >= 0) {
    const uint32_t present = 1u << (uint32_t)slot;
    if ((view->extension_flags & present) != 0) {
      view->extension_flags |=
          1u << (AWSLC_X509_EXTENSION_DUPLICATE_SHIFT + (uint32_t)slot);
    } else {
      view->extension_flags |= present;
      view->extension_values[slot] = c_view_content_range(parent, &value);
      if (is_critical) {
        view->extension_flags |=
            1u << (AWSLC_X509_EXTENSION_CRITICAL_SHIFT + (uint32_t)slot);
      }
    }
  }
  if (is_critical &&
      !c_view_supported_critical_extension(oid.content, oid.content_len)) {
    view->extension_flags |= AWSLC_X509_EXTENSION_UNSUPPORTED_CRITICAL;
  }
  return AWSLC_X509_PARSE_OK;
}

static uint32_t c_view_validate_extensions(
    const C_VIEW_CURSOR *parent, const C_VIEW_TLV *explicit_extensions,
    AWSLC_X509_CERTIFICATE_VIEW *view) {
  C_VIEW_CURSOR wrapper =
      c_view_cursor(parent->root, explicit_extensions->content,
                    explicit_extensions->content_len);
  C_VIEW_TLV extensions;
  if (c_view_expect(&wrapper, 0x30, &extensions) != AWSLC_X509_PARSE_OK ||
      wrapper.ptr != wrapper.end) {
    return AWSLC_X509_PARSE_INVALID_EXTENSIONS;
  }

  C_VIEW_CURSOR sequence =
      c_view_cursor(parent->root, extensions.content, extensions.content_len);
  while (sequence.ptr != sequence.end) {
    C_VIEW_TLV extension;
    if (c_view_expect(&sequence, 0x30, &extension) != AWSLC_X509_PARSE_OK ||
        c_view_validate_extension(parent, &extension, view) !=
            AWSLC_X509_PARSE_OK) {
      return AWSLC_X509_PARSE_INVALID_EXTENSIONS;
    }
  }
  return AWSLC_X509_PARSE_OK;
}

static uint32_t c_view_parse_tbs(const C_VIEW_CURSOR *parent,
                                 const C_VIEW_TLV *tbs,
                                 AWSLC_X509_CERTIFICATE_VIEW *view) {
  C_VIEW_CURSOR fields =
      c_view_cursor(parent->root, tbs->content, tbs->content_len);
  C_VIEW_TLV field;
  uint32_t result = 0;

  if (fields.ptr != fields.end && fields.ptr[0] == 0xa0) {
    C_VIEW_TLV explicit_version, version;
    result = c_view_expect(&fields, 0xa0, &explicit_version);
    if (result != AWSLC_X509_PARSE_OK) {
      return result;
    }
    C_VIEW_CURSOR wrapper = c_view_cursor(
        parent->root, explicit_version.content, explicit_version.content_len);
    result = c_view_expect(&wrapper, 0x02, &version);
    if (result != AWSLC_X509_PARSE_OK) {
      return result;
    }
    result = c_view_validate_integer(&version);
    if (result != AWSLC_X509_PARSE_OK) {
      return result;
    }
    result = c_view_finish(&wrapper);
    if (result != AWSLC_X509_PARSE_OK) {
      return result;
    }
    if (version.content_len != 1 || version.content[0] > 2) {
      return AWSLC_X509_PARSE_INVALID_VERSION;
    }
    view->version = version.content[0];
  }

  result = c_view_expect(&fields, 0x02, &field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_integer(&field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  view->serial = c_view_range(parent, &field);

  result = c_view_expect(&fields, 0x30, &field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_algorithm(parent, &field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  view->tbs_signature_algorithm = c_view_range(parent, &field);

  result = c_view_expect(&fields, 0x30, &field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_name(parent, &field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  view->issuer = c_view_range(parent, &field);

  result = c_view_expect(&fields, 0x30, &field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_validity(parent, &field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  view->validity = c_view_range(parent, &field);

  result = c_view_expect(&fields, 0x30, &field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_name(parent, &field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  view->subject = c_view_range(parent, &field);

  result = c_view_expect(&fields, 0x30, &field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_spki(parent, &field);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  view->spki = c_view_range(parent, &field);

  if (fields.ptr != fields.end && fields.ptr[0] == 0x81) {
    result = c_view_expect(&fields, 0x81, &field);
    if (result != AWSLC_X509_PARSE_OK) {
      return result;
    }
    result =
        c_view_validate_bit_string_content(field.content, field.content_len);
    if (result != AWSLC_X509_PARSE_OK) {
      return result;
    }
    view->flags |= AWSLC_X509_FLAG_ISSUER_UID;
    view->issuer_uid = c_view_range(parent, &field);
  }
  if (fields.ptr != fields.end && fields.ptr[0] == 0x82) {
    result = c_view_expect(&fields, 0x82, &field);
    if (result != AWSLC_X509_PARSE_OK) {
      return result;
    }
    result =
        c_view_validate_bit_string_content(field.content, field.content_len);
    if (result != AWSLC_X509_PARSE_OK) {
      return result;
    }
    view->flags |= AWSLC_X509_FLAG_SUBJECT_UID;
    view->subject_uid = c_view_range(parent, &field);
  }
  if (fields.ptr != fields.end && fields.ptr[0] == 0xa3) {
    result = c_view_expect(&fields, 0xa3, &field);
    if (result != AWSLC_X509_PARSE_OK) {
      return result;
    }
    result = c_view_validate_extensions(parent, &field, view);
    if (result != AWSLC_X509_PARSE_OK) {
      return result;
    }
    view->flags |= AWSLC_X509_FLAG_EXTENSIONS;
    view->extensions = c_view_range(parent, &field);
  }

  result = c_view_finish(&fields);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  if (view->version == 0 &&
      (view->flags &
       (AWSLC_X509_FLAG_ISSUER_UID | AWSLC_X509_FLAG_SUBJECT_UID)) != 0) {
    return AWSLC_X509_PARSE_INVALID_FIELD_FOR_VERSION;
  }
  if (view->version != 2 && (view->flags & AWSLC_X509_FLAG_EXTENSIONS) != 0) {
    return AWSLC_X509_PARSE_INVALID_FIELD_FOR_VERSION;
  }
  return AWSLC_X509_PARSE_OK;
}

C_VIEW_FLATTEN uint32_t x509_parse_der_view(const uint8_t *der, size_t der_len,
                                            uint8_t exact,
                                            AWSLC_X509_CERTIFICATE_VIEW *out) {
  if (out == NULL || (der == NULL && der_len != 0)) {
    return AWSLC_X509_PARSE_NULL_POINTER;
  }
  if (der_len > UINT32_MAX || der_len > INT_MAX / 2) {
    return AWSLC_X509_PARSE_INPUT_TOO_LARGE;
  }
  if (der_len == 0) {
    return AWSLC_X509_PARSE_TRUNCATED;
  }

  C_VIEW_CURSOR input = {der, der, der + der_len};
  C_VIEW_TLV certificate, tbs, signature_algorithm, signature;
  AWSLC_X509_CERTIFICATE_VIEW view;
  OPENSSL_memset(&view, 0, sizeof(view));

  uint32_t result = c_view_expect(&input, 0x30, &certificate);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  C_VIEW_CURSOR fields =
      c_view_cursor(der, certificate.content, certificate.content_len);

  result = c_view_expect(&fields, 0x30, &tbs);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_parse_tbs(&input, &tbs, &view);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_expect(&fields, 0x30, &signature_algorithm);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_algorithm(&input, &signature_algorithm);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_expect(&fields, 0x03, &signature);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_validate_bit_string(&signature);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }
  result = c_view_finish(&fields);
  if (result != AWSLC_X509_PARSE_OK) {
    return result;
  }

  view.certificate = c_view_range(&input, &certificate);
  view.tbs_certificate = c_view_range(&input, &tbs);
  view.signature_algorithm = c_view_range(&input, &signature_algorithm);
  view.signature = c_view_range(&input, &signature);

  if (exact && certificate.encoded_len != der_len) {
    return AWSLC_X509_PARSE_TRAILING_DATA;
  }
  *out = view;
  return AWSLC_X509_PARSE_OK;
}
