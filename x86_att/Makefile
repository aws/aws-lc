#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
#
#  http://aws.amazon.com/apache2.0
#
# or in the "LICENSE" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
#############################################################################

# These are the object files corresponding to sources for translation

OBJ = p256/bignum_add_p256.o \
      p256/bignum_bigendian_4.o \
      p256/bignum_cmul_p256.o \
      p256/bignum_deamont_p256.o \
      p256/bignum_demont_p256.o \
      p256/bignum_double_p256.o \
      p256/bignum_half_p256.o \
      p256/bignum_mod_n256.o \
      p256/bignum_mod_n256_4.o \
      p256/bignum_mod_p256.o \
      p256/bignum_mod_p256_4.o \
      p256/bignum_montmul_p256.o \
      p256/bignum_montsqr_p256.o \
      p256/bignum_mux_4.o \
      p256/bignum_neg_p256.o \
      p256/bignum_nonzero_4.o \
      p256/bignum_optneg_p256.o \
      p256/bignum_sub_p256.o \
      p256/bignum_tomont_p256.o \
      p256/bignum_triple_p256.o \
      p384/bignum_add_p384.o \
      p384/bignum_bigendian_6.o \
      p384/bignum_cmul_p384.o \
      p384/bignum_deamont_p384.o \
      p384/bignum_demont_p384.o \
      p384/bignum_double_p384.o \
      p384/bignum_half_p384.o \
      p384/bignum_mod_n384.o \
      p384/bignum_mod_n384_6.o \
      p384/bignum_mod_p384.o \
      p384/bignum_mod_p384_6.o \
      p384/bignum_montmul_p384.o \
      p384/bignum_montsqr_p384.o \
      p384/bignum_mux_6.o \
      p384/bignum_neg_p384.o \
      p384/bignum_nonzero_6.o \
      p384/bignum_optneg_p384.o \
      p384/bignum_sub_p384.o \
      p384/bignum_tomont_p384.o \
      p384/bignum_triple_p384.o

# The AT&T syntax source files

ATTSOURCES = $(OBJ:.o=.S)

code: $(ATTSOURCES)

all: $(OBJ);

%.o : %.S ; (cpp $< | as -o $@ -); (cd ../x86; cpp $< | as -o /tmp/original_object.o); cmp -s $@ /tmp/original_object.o

fastmul/%.S :: ../x86/fastmul/%.S ; (cat $< | sed -E -f ./attrofy.sed >$@) && (cpp $@ | as -o /tmp/translated_object.o) ; (cpp $< | as -o /tmp/original_object.o); cmp -s /tmp/translated_object.o /tmp/original_object.o
generic/%.S :: ../x86/generic/%.S ; (cat $< | sed -E -f ./attrofy.sed >$@) && (cpp $@ | as -o /tmp/translated_object.o) ; (cpp $< | as -o /tmp/original_object.o); cmp -s /tmp/translated_object.o /tmp/original_object.o
p256/%.S :: ../x86/p256/%.S ; (cat $< | sed -E -f ./attrofy.sed >$@) && (cpp $@ | as -o /tmp/translated_object.o) ; (cpp $< | as -o /tmp/original_object.o); cmp -s /tmp/translated_object.o /tmp/original_object.o
p384/%.S :: ../x86/p384/%.S ; (cat $< | sed -E -f ./attrofy.sed >$@) && (cpp $@ | as -o /tmp/translated_object.o) ; (cpp $< | as -o /tmp/original_object.o); cmp -s /tmp/translated_object.o /tmp/original_object.o
p521/%.S :: ../x86/p521/%.S ; (cat $< | sed -E -f ./attrofy.sed >$@) && (cpp $@ | as -o /tmp/translated_object.o) ; (cpp $< | as -o /tmp/original_object.o); cmp -s /tmp/translated_object.o /tmp/original_object.o

clean:; rm -f */*.o

clobber:; rm -f */*.o */*.S
