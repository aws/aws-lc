# Makefile for generating ML-DSA test vectors
#
# Usage:
#   make                    # Build the generator
#   make generate           # Generate test vectors
#   make clean              # Clean build artifacts

# Paths relative to this directory
BUILD_DIR = ../../../build
CRYPTO_LIB = $(BUILD_DIR)/crypto/libcrypto.a
OUTPUT_FILE = ../../evp_extra/mldsa_corrupted_key_tests.txt

# Compiler settings
CXX = c++
CXXFLAGS = -std=c++11 -Wall -I../../../include -I../../.. -I.
LDFLAGS = $(CRYPTO_LIB)

.PHONY: all generate clean

all: make_corrupted_key_tests

make_corrupted_key_tests: make_corrupted_key_tests.cc
	@if [ ! -f "$(CRYPTO_LIB)" ]; then \
		echo "Error: libcrypto.a not found at $(CRYPTO_LIB)"; \
		echo "Please build aws-lc first in ./build"; \
		exit 1; \
	fi
	$(CXX) $(CXXFLAGS) -o $@ $< $(LDFLAGS)

generate: make_corrupted_key_tests
	@echo "Generating test vectors to $(OUTPUT_FILE)..."
	./make_corrupted_key_tests > $(OUTPUT_FILE)
	@echo "Successfully generated $(OUTPUT_FILE)"

clean:
	rm make_corrupted_key_tests
