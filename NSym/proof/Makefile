# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

DEFAULT_OPTIONS?=-vno -q -vnoosi

.PHONY: all clean sha512_spec sha384_spec sha2_grav2 sha2_grav3

SHA384_SPEC_FILE := \
  sha384rec_spec

SHA512_SPEC_FILE := \
  sha512rec_spec

SHA2_GRAVITON2_FILES := \
  sha512_block_data_order_bounded \
  sha512_block_data_order_unbounded

SHA2_GRAVITON3_FILES := \
  sha512_block_armv8_bounded \
  sha512_block_armv8_unbounded

all: sha384_spec sha512_spec sha2_grav2 sha2_grav3

sha384_spec: $(SHA384_SPEC_FILE)
sha512_spec: $(SHA512_SPEC_FILE)

sha2_grav2: $(SHA2_GRAVITON2_FILES)
sha2_grav3: $(SHA2_GRAVITON3_FILES)

$(SHA512_SPEC_FILE) $(SHA384_SPEC_FILE) $(SHA2_GRAVITON2_FILES) $(SHA2_GRAVITON3_FILES): %: proofs/SHA512/%.ml
	time -p dune exec -- _build/default/proofs/$(*F).exe $(DEFAULT_OPTIONS)

clean:
	dune clean && rm -f *.opam
