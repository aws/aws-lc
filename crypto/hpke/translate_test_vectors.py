#!/usr/bin/env python3
# coding=utf-8
# Copyright (c) 2020, Google Inc.
# SPDX-License-Identifier: ISC

"""This script translates JSON test vectors to BoringSSL's "FileTest" format.

Usage: translate_test_vectors.py

It expects two JSON files in the working directory:
- test-vectors.json, from [TestVectors] in RFC 9180
- test-vectors-pq.json, from [TestVectors] in draft-ietf-hpke-pq, published at
  https://github.com/hpkewg/hpke-pq/blob/main/test-vectors.json

The output is written to hpke_test_vectors.txt and hpke_test_vectors_pq.txt,
respectively.
"""

import collections
import json
import sys

HPKE_MODE_BASE = 0
HPKE_MODE_PSK = 1
HPKE_MODE_AUTH = 2

HPKE_DHKEM_X25519_SHA256 = 0x0020
HPKE_MLKEM512 = 0x0040
HPKE_MLKEM768 = 0x0041
HPKE_MLKEM1024 = 0x0042

HPKE_HKDF_SHA256 = 0x0001
HPKE_HKDF_SHA384 = 0x0002

HPKE_AEAD_EXPORT_ONLY = 0xffff

# The ML-KEM KEMs this library implements, and the KDFs it can pair them with.
# draft-ietf-hpke-pq also registers the single-stage SHAKE and TurboSHAKE KDFs
# (0x0010-0x0013), which this library does not implement, so vectors using them
# are skipped.
MLKEM_KEMS = (HPKE_MLKEM512, HPKE_MLKEM768, HPKE_MLKEM1024)
SUPPORTED_KDFS = (HPKE_HKDF_SHA256, HPKE_HKDF_SHA384)


def format_test(test, keys):
  """Formats one test case as FileTest attributes."""
  lines = []
  for key in keys:
    lines.append("{} = {}".format(key, str(test[key])))

  for i, enc in enumerate(test["encryptions"]):
    lines.append("# encryptions[{}]".format(i))
    for key in ("aad", "ct", "pt"):
      lines.append("{} = {}".format(key, str(enc[key])))

  for i, exp in enumerate(test["exports"]):
    lines.append("# exports[{}]".format(i))
    for key in ("exporter_context", "L", "exported_value"):
      lines.append("{} = {}".format(key, str(exp[key])))

  lines.append("")
  return lines


def translate_dhkem_vectors(test_vecs):
  """Translates the RFC 9180 DHKEM(X25519, HKDF-SHA256) vectors.

    "kem_id" is not emitted for these, because they are all DHKEM(X25519); the
    reader defaults to it when the attribute is absent.
  """
  lines = []
  for test in test_vecs:
    # Filter out test cases that we don't use.
    if (test["mode"] not in (HPKE_MODE_BASE, HPKE_MODE_AUTH) or
        test["kem_id"] != HPKE_DHKEM_X25519_SHA256 or
        test["aead_id"] == HPKE_AEAD_EXPORT_ONLY or
        test["kdf_id"] != HPKE_HKDF_SHA256):
      continue

    keys = ["mode", "kdf_id", "aead_id", "info", "skRm", "skEm", "pkRm", "pkEm"]

    if test["mode"] == HPKE_MODE_AUTH:
      keys.append("pkSm")
      keys.append("skSm")

    lines.extend(format_test(test, keys))
  return lines


def translate_mlkem_vectors(test_vecs):
  """Translates the draft-ietf-hpke-pq ML-KEM vectors.

    ML-KEM has no ephemeral key pair: Encap takes a 32-byte encapsulation
    entropy value ("ikmE") and emits a ciphertext ("enc"), so those replace the
    "skEm" and "pkEm" attributes used for DHKEM. "skRm" is the 64-byte (d || z)
    seed, per Nsk = 64. ML-KEM does not support mode_auth.

    Note the upstream JSON double-encodes "info" and "pt": their values are the
    hex encoding of an ASCII hex string, so "info" decodes to the *text*
    "4f6465206f6e2061204772656369616e2055726e" rather than to "Ode on a Grecian
    Urn". The published ciphertexts were computed over those literal bytes, so
    they are copied through verbatim and must not be "corrected".
  """
  lines = []
  for test in test_vecs:
    if (test["mode"] != HPKE_MODE_BASE or
        test["kem_id"] not in MLKEM_KEMS or
        test["aead_id"] == HPKE_AEAD_EXPORT_ONLY or
        test["kdf_id"] not in SUPPORTED_KDFS):
      continue

    keys = ["mode", "kem_id", "kdf_id", "aead_id", "info", "skRm", "pkRm",
            "ikmE", "enc"]
    lines.extend(format_test(test, keys))
  return lines


def main(argv):
  if len(argv) != 1:
    print(__doc__)
    sys.exit(1)

  with open("test-vectors.json") as file_in:
    lines = translate_dhkem_vectors(json.load(file_in))
  with open("hpke_test_vectors.txt", "w") as file_out:
    file_out.write("\n".join(lines))

  with open("test-vectors-pq.json") as file_in:
    lines = translate_mlkem_vectors(json.load(file_in))
  with open("hpke_test_vectors_pq.txt", "w") as file_out:
    file_out.write("\n".join(lines))


if __name__ == "__main__":
  main(sys.argv)
