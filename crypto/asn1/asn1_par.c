/* Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com)
 * All rights reserved.
 *
 * This package is an SSL implementation written
 * by Eric Young (eay@cryptsoft.com).
 * The implementation was written so as to conform with Netscapes SSL.
 *
 * This library is free for commercial and non-commercial use as long as
 * the following conditions are aheared to.  The following conditions
 * apply to all code found in this distribution, be it the RC4, RSA,
 * lhash, DES, etc., code; not just the SSL code.  The SSL documentation
 * included with this distribution is covered by the same copyright terms
 * except that the holder is Tim Hudson (tjh@cryptsoft.com).
 *
 * Copyright remains Eric Young's, and as such any Copyright notices in
 * the code are not to be removed.
 * If this package is used in a product, Eric Young should be given attribution
 * as the author of the parts of the library used.
 * This can be in the form of a textual message at program startup or
 * in documentation (online or textual) provided with the package.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    "This product includes cryptographic software written by
 *     Eric Young (eay@cryptsoft.com)"
 *    The word 'cryptographic' can be left out if the rouines from the library
 *    being used are not cryptographic related :-).
 * 4. If you include any Windows specific code (or a derivative thereof) from
 *    the apps directory (application code) you must include an acknowledgement:
 *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
 *
 * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * The licence and distribution terms for any publically available version or
 * derivative of this code cannot be changed.  i.e. this code cannot simply be
 * copied and put under another distribution licence
 * [including the GNU Public Licence.] */

#include <openssl/asn1.h>
#include <openssl/bio.h>
#include "../internal.h"

// Forward declarations
static int asn1_parse2(BIO *bp, const uint8_t **pp, long length, int offset,
                       int depth, int indent, int dump);
static int asn1_print_info(BIO *bp, int tag, int xclass, int constructed,
                           int indent);
static int asn1_parse_constructed_type(
    BIO *bp, const unsigned char **current_pos, const unsigned char *total_end,
    const unsigned char *original_start, long *object_length, int parse_flags,
    int offset, int depth, int indent, int dump);
static int asn1_parse_primitive_type(BIO *bp, const unsigned char *object_start,
                                     const unsigned char *current_pos,
                                     long object_length, int header_length,
                                     int tag, int dump);

const char *ASN1_tag2str(int tag) {
  static const char *const tag2str[] = {
      "EOC",
      "BOOLEAN",
      "INTEGER",
      "BIT STRING",
      "OCTET STRING",
      "NULL",
      "OBJECT",
      "OBJECT DESCRIPTOR",
      "EXTERNAL",
      "REAL",
      "ENUMERATED",
      "<ASN1 11>",
      "UTF8STRING",
      "<ASN1 13>",
      "<ASN1 14>",
      "<ASN1 15>",
      "SEQUENCE",
      "SET",
      "NUMERICSTRING",
      "PRINTABLESTRING",
      "T61STRING",
      "VIDEOTEXSTRING",
      "IA5STRING",
      "UTCTIME",
      "GENERALIZEDTIME",
      "GRAPHICSTRING",
      "VISIBLESTRING",
      "GENERALSTRING",
      "UNIVERSALSTRING",
      "<ASN1 29>",
      "BMPSTRING",
  };

  if ((tag == V_ASN1_NEG_INTEGER) || (tag == V_ASN1_NEG_ENUMERATED)) {
    tag &= ~V_ASN1_NEG;
  }

  if (tag < 0 || tag > 30) {
    return "(unknown)";
  }
  return tag2str[tag];
}

int ASN1_parse(BIO *bp, const unsigned char *pp, long len, int indent) {
  GUARD_PTR(bp);
  GUARD_PTR(pp);
  return asn1_parse2(bp, &pp, len, 0, 0, indent, 0);
}

// Constants
#define ASN1_PARSE_MAXDEPTH 128
#define ASN1_DUMP_INDENT 6  // Because we know BIO_dump_indent()

// Copy of helper functions from original (these remain unchanged)
static int asn1_print_info(BIO *bp, int tag, int xclass, int constructed,
                           int indent) {
  static const char fmt[] = "%-18s";
  char str[128];
  const char *p;

  if (constructed & V_ASN1_CONSTRUCTED) {
    p = "cons: ";
  } else {
    p = "prim: ";
  }
  if (BIO_write(bp, p, 6) < 6) {
    goto err;
  }
  BIO_indent(bp, indent, 128);

  p = str;
  if ((xclass & V_ASN1_PRIVATE) == V_ASN1_PRIVATE) {
    BIO_snprintf(str, sizeof(str), "priv [ %d ] ", tag);
  } else if ((xclass & V_ASN1_CONTEXT_SPECIFIC) == V_ASN1_CONTEXT_SPECIFIC) {
    BIO_snprintf(str, sizeof(str), "cont [ %d ]", tag);
  } else if ((xclass & V_ASN1_APPLICATION) == V_ASN1_APPLICATION) {
    BIO_snprintf(str, sizeof(str), "appl [ %d ]", tag);
  } else if (tag > 30) {
    BIO_snprintf(str, sizeof(str), "<ASN1 %d>", tag);
  } else {
    p = ASN1_tag2str(tag);
  }

  if (BIO_printf(bp, fmt, p) <= 0) {
    goto err;
  }
  return 1;
err:
  return 0;
}

static int BIO_dump_indent(BIO *bp, const char *s, int len, int indent) {
  // Use BIO_hexdump as a replacement for BIO_dump_indent
  return BIO_hexdump(bp, (const uint8_t *)s, len, indent);
}

// Helper function to parse constructed ASN.1 types (SEQUENCE, SET, etc.)
static int asn1_parse_constructed_type(
    BIO *bp, const unsigned char **current_pos, const unsigned char *total_end,
    const unsigned char *original_start, long *object_length, int parse_flags,
    int offset, int depth, int indent, int dump) {
  const unsigned char *start_pos = *current_pos;

  GUARD_PTR(bp);
  GUARD_PTR(current_pos);
  GUARD_PTR(total_end);
  GUARD_PTR(original_start);
  GUARD_PTR(object_length);

  if (BIO_write(bp, "\n", 1) <= 0) {
    return 0;
  }

  if ((parse_flags == (V_ASN1_CONSTRUCTED | 1)) && (*object_length == 0)) {
    // Indefinite length constructed object
    for (;;) {
      const int parse_result = asn1_parse2(
          bp, current_pos, (long)(total_end - *current_pos),
          offset + (*current_pos - original_start), depth + 1, indent, dump);
      if (parse_result == 0) {
        return 0;
      }
      if ((parse_result == 2) || (*current_pos >= total_end)) {
        *object_length = *current_pos - start_pos;
        break;
      }
    }
  } else {
    // Definite length constructed object
    const unsigned char *constructed_end = *current_pos + *object_length;
    long remaining_length = *object_length;

    if(constructed_end > total_end) {
      return 0;
    }

    while (*current_pos < constructed_end) {
      start_pos = *current_pos;
      const int parse_result = asn1_parse2(
          bp, current_pos, remaining_length,
          offset + (*current_pos - original_start), depth + 1, indent, dump);
      if (parse_result == 0) {
        return 0;
      }
      remaining_length -= *current_pos - start_pos;
    }
  }
  return 1;
}

// Helper function to parse primitive ASN.1 types
static int asn1_parse_primitive_type(BIO *bp, const unsigned char *object_start,
                                     const unsigned char *current_pos,
                                     long object_length, int header_length,
                                     int tag, int dump) {
  const unsigned char *parse_pos;
  ASN1_OBJECT *asn1_object = NULL;
  ASN1_OCTET_STRING *octet_string = NULL;
  ASN1_INTEGER *asn1_integer = NULL;
  ASN1_ENUMERATED *asn1_enumerated = NULL;
  int newline_printed = 0;
  int dump_as_hex = 0;
  int dump_indent = 6;
  int return_code = 0;

  if (!bp || !object_start || !current_pos) {
    return 0;
  }

  if ((tag == V_ASN1_PRINTABLESTRING) || (tag == V_ASN1_T61STRING) ||
      (tag == V_ASN1_IA5STRING) || (tag == V_ASN1_VISIBLESTRING) ||
      (tag == V_ASN1_NUMERICSTRING) || (tag == V_ASN1_UTF8STRING) ||
      (tag == V_ASN1_UTCTIME) || (tag == V_ASN1_GENERALIZEDTIME)) {
    if (BIO_write(bp, ":", 1) <= 0) {
      goto end;
    }
    if(object_length > INT_MAX) {
      return 0;
    }
    if ((object_length > 0) &&
        BIO_write(bp, (const char *)current_pos, (int)object_length) !=
            (int)object_length) {
      goto end;
    }
  } else if (tag == V_ASN1_OBJECT) {
    parse_pos = object_start;
    if (d2i_ASN1_OBJECT(&asn1_object, &parse_pos,
                        object_length + header_length) != NULL) {
      if (BIO_write(bp, ":", 1) <= 0) {
        goto end;
      }
      i2a_ASN1_OBJECT(bp, asn1_object);
    } else {
      if (BIO_puts(bp, ":BAD OBJECT") <= 0) {
        goto end;
      }
      dump_as_hex = 1;
    }
  } else if (tag == V_ASN1_BOOLEAN) {
    if (object_length != 1) {
      if (BIO_puts(bp, ":BAD BOOLEAN") <= 0) {
        goto end;
      }
      dump_as_hex = 1;
    }
    if (object_length > 0) {
      BIO_printf(bp, ":%u", current_pos[0]);
    }
  } else if (tag == V_ASN1_BMPSTRING) {
    /* do the BMP thang */
  } else if (tag == V_ASN1_OCTET_STRING) {
    int i, printable = 1;

    parse_pos = object_start;
    octet_string =
        d2i_ASN1_OCTET_STRING(NULL, &parse_pos, object_length + header_length);
    if (octet_string != NULL && octet_string->length > 0) {
      parse_pos = octet_string->data;
      /*
       * testing whether the octet string is printable
       */
      for (i = 0; i < octet_string->length; i++) {
        if (((parse_pos[i] < ' ') && (parse_pos[i] != '\n') &&
             (parse_pos[i] != '\r') && (parse_pos[i] != '\t')) ||
            (parse_pos[i] > '~')) {
          printable = 0;
          break;
        }
      }
      if (printable)
      /* printable string */
      {
        if (BIO_write(bp, ":", 1) <= 0) {
          goto end;
        }
        if (BIO_write(bp, (const char *)parse_pos, octet_string->length) <= 0) {
          goto end;
        }
      } else if (!dump)
      /*
       * not printable => print octet string as hex dump
       */
      {
        if (BIO_write(bp, "[HEX DUMP]:", 11) <= 0) {
          goto end;
        }
        for (i = 0; i < octet_string->length; i++) {
          if (BIO_printf(bp, "%02X", parse_pos[i]) <= 0) {
            goto end;
          }
        }
      } else
      /* print the normal dump */
      {
        if (!newline_printed) {
          if (BIO_write(bp, "\n", 1) <= 0) {
            goto end;
          }
        }
        if (BIO_dump_indent(bp, (const char *)parse_pos,
                            ((dump == -1 || dump > octet_string->length)
                                 ? octet_string->length
                                 : dump),
                            dump_indent) <= 0) {
          goto end;
        }
        newline_printed = 1;
      }
    }
  } else if (tag == V_ASN1_INTEGER) {
    int i;

    parse_pos = object_start;
    asn1_integer =
        d2i_ASN1_INTEGER(NULL, &parse_pos, object_length + header_length);
    if (asn1_integer != NULL) {
      if (BIO_write(bp, ":", 1) <= 0) {
        goto end;
      }
      if (asn1_integer->type == V_ASN1_NEG_INTEGER) {
        if (BIO_write(bp, "-", 1) <= 0) {
          goto end;
        }
      }
      for (i = 0; i < asn1_integer->length; i++) {
        if (BIO_printf(bp, "%02X", asn1_integer->data[i]) <= 0) {
          goto end;
        }
      }
      if (asn1_integer->length == 0) {
        if (BIO_write(bp, "00", 2) <= 0) {
          goto end;
        }
      }
    } else {
      if (BIO_puts(bp, ":BAD INTEGER") <= 0) {
        goto end;
      }
      dump_as_hex = 1;
    }
  } else if (tag == V_ASN1_ENUMERATED) {
    int i;

    parse_pos = object_start;
    asn1_enumerated =
        d2i_ASN1_ENUMERATED(NULL, &parse_pos, object_length + header_length);
    if (asn1_enumerated != NULL) {
      if (BIO_write(bp, ":", 1) <= 0) {
        goto end;
      }
      if (asn1_enumerated->type == V_ASN1_NEG_ENUMERATED) {
        if (BIO_write(bp, "-", 1) <= 0) {
          goto end;
        }
      }
      for (i = 0; i < asn1_enumerated->length; i++) {
        if (BIO_printf(bp, "%02X", asn1_enumerated->data[i]) <= 0) {
          goto end;
        }
      }
      if (asn1_enumerated->length == 0) {
        if (BIO_write(bp, "00", 2) <= 0) {
          goto end;
        }
      }
    } else {
      if (BIO_puts(bp, ":BAD ENUMERATED") <= 0) {
        goto end;
      }
      dump_as_hex = 1;
    }
  } else if (object_length > 0 && dump) {
    if (!newline_printed) {
      if (BIO_write(bp, "\n", 1) <= 0) {
        goto end;
      }
    }
    if (BIO_dump_indent(
            bp, (const char *)current_pos,
            ((dump == -1 || dump > object_length) ? object_length : dump),
            dump_indent) <= 0) {
      goto end;
    }
    newline_printed = 1;
  }

  if (dump_as_hex) {
    int i;
    const unsigned char *hex_data = object_start + header_length;
    if (BIO_puts(bp, ":[") <= 0) {
      goto end;
    }
    for (i = 0; i < object_length; i++) {
      if (BIO_printf(bp, "%02X", hex_data[i]) <= 0) {
        goto end;
      }
    }
    if (BIO_puts(bp, "]") <= 0) {
      goto end;
    }
  }

  if (!newline_printed) {
    if (BIO_write(bp, "\n", 1) <= 0) {
      goto end;
    }
  }

  return_code = 1;

end:
  ASN1_OBJECT_free(asn1_object);
  ASN1_OCTET_STRING_free(octet_string);
  ASN1_INTEGER_free(asn1_integer);
  ASN1_ENUMERATED_free(asn1_enumerated);
  return return_code;
}

static int asn1_parse2(BIO *bp, const unsigned char **pp, long length,
                       int offset, int depth, int indent, int dump) {
  const unsigned char *current_pos, *total_end, *object_start;
  long object_length = 0;
  int tag, xclass, return_value = 0;
  int header_length = 0, parse_flags = 0;

  GUARD_PTR(bp);
  GUARD_PTR(pp);

  if (depth > ASN1_PARSE_MAXDEPTH) {
    BIO_puts(bp, "BAD RECURSION DEPTH\n");
    return 0;
  }

  current_pos = *pp;
  total_end = current_pos + length;
  while (length > 0) {
    object_start = current_pos;
    parse_flags =
        ASN1_get_object(&current_pos, &object_length, &tag, &xclass, length);
    if (parse_flags & 0x80) {
      if (BIO_write(bp, "Error in encoding\n", 18) <= 0) {
        goto end;
      }
      return_value = 0;
      goto end;
    }
    header_length = (current_pos - object_start);
    length -= header_length;
    /*
     * if parse_flags == 0x21 it is a constructed indefinite length object
     */
    if (BIO_printf(bp, "%5ld:", (long)offset + (long)(object_start - *pp)) <=
        0) {
      goto end;
    }

    if (parse_flags != (V_ASN1_CONSTRUCTED | 1)) {
      if (BIO_printf(bp, "d=%-2d hl=%ld l=%4ld ", depth, (long)header_length,
                     object_length) <= 0) {
        goto end;
      }
    } else {
      if (BIO_printf(bp, "d=%-2d hl=%ld l=inf  ", depth, (long)header_length) <=
          0) {
        goto end;
      }
    }
    if (!asn1_print_info(bp, tag, xclass, parse_flags, (indent) ? depth : 0)) {
      goto end;
    }
    if (parse_flags & V_ASN1_CONSTRUCTED) {
      if (object_length > length) {
        BIO_printf(bp, "length is greater than %ld\n", length);
        return_value = 0;
        goto end;
      }
      if (!asn1_parse_constructed_type(bp, &current_pos, total_end, *pp,
                                       &object_length, parse_flags, offset,
                                       depth, indent, dump)) {
        return_value = 0;
        goto end;
      }
    } else if (xclass != 0) {
      current_pos += object_length;
      if (BIO_write(bp, "\n", 1) <= 0) {
        goto end;
      }
    } else {
      if (!asn1_parse_primitive_type(bp, object_start, current_pos,
                                     object_length, header_length, tag, dump)) {
        goto end;
      }
      current_pos += object_length;
      if ((tag == V_ASN1_EOC) && (xclass == 0)) {
        return_value = 2; /* End of sequence */
        goto end;
      }
    }
    length -= object_length;
  }
  return_value = 1;
end:
  *pp = current_pos;
  return return_value;
}
