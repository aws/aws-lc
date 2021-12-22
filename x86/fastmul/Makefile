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

OBJ = bignum_emontredc_8n.o \
      bignum_kmul_16_32.o \
      bignum_kmul_32_64.o \
      bignum_ksqr_16_32.o \
      bignum_ksqr_32_64.o \
      bignum_mul_4_8.o \
      bignum_mul_4_8_alt.o \
      bignum_mul_6_12.o \
      bignum_mul_8_16.o \
      bignum_sqr_4_8.o \
      bignum_sqr_4_8_alt.o \
      bignum_sqr_6_12.o \
      bignum_sqr_8_16.o

%.o : %.S ; cpp $< | as -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
