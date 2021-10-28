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

# The x86 assembly (.S) files are all written for the GNU assembler

OBJ = bignum_add_p256.o \
      bignum_bigendian_4.o \
      bignum_cmul_p256.o \
      bignum_deamont_p256.o \
      bignum_demont_p256.o \
      bignum_double_p256.o \
      bignum_half_p256.o \
      bignum_littleendian_4.o \
      bignum_mod_n256.o \
      bignum_mod_n256_4.o \
      bignum_mod_p256.o \
      bignum_mod_p256_4.o \
      bignum_montmul_p256.o \
      bignum_montsqr_p256.o \
      bignum_mux_4.o \
      bignum_neg_p256.o \
      bignum_nonzero_4.o \
      bignum_optneg_p256.o \
      bignum_sub_p256.o \
      bignum_tomont_p256.o \
      bignum_triple_p256.o

%.o : %.S ; cpp $< | as -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
