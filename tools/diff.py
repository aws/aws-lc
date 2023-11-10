#!/usr/bin/python3

# A script to get the diff inputs used by equiv checkers
# See also: arm/proofs/bignum_mul_8_16_neon.ml
import difflib
import sys

l1 = open(sys.argv[1], "r").readlines()
l2 = open(sys.argv[2], "r").readlines()

s = difflib.SequenceMatcher(None, l1, l2)

# https://docs.python.org/3/library/difflib.html#sequencematcher-objects
for tag,i1,i2,j1,j2 in s.get_opcodes():
  print('("%s", %d, %d, %d, %d);' % (tag,i1,i2,j1,j2))
