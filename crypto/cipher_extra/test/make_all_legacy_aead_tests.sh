#!/bin/sh
# Copyright (c) 2014, Google Inc.
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
# SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
# OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
# CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

set -xe

go run make_legacy_aead_tests.go -cipher aes128 -mac sha1 > aes_128_cbc_sha1_tls_tests.txt
go run make_legacy_aead_tests.go -cipher aes128 -mac sha1 -implicit-iv > aes_128_cbc_sha1_tls_implicit_iv_tests.txt
go run make_legacy_aead_tests.go -cipher aes128 -mac sha256 > aes_128_cbc_sha256_tls_tests.txt

go run make_legacy_aead_tests.go -cipher aes256 -mac sha1 > aes_256_cbc_sha1_tls_tests.txt
go run make_legacy_aead_tests.go -cipher aes256 -mac sha1 -implicit-iv > aes_256_cbc_sha1_tls_implicit_iv_tests.txt
go run make_legacy_aead_tests.go -cipher aes256 -mac sha256 > aes_256_cbc_sha256_tls_tests.txt
go run make_legacy_aead_tests.go -cipher aes256 -mac sha384 > aes_256_cbc_sha384_tls_tests.txt

go run make_legacy_aead_tests.go -cipher 3des -mac sha1 > des_ede3_cbc_sha1_tls_tests.txt
go run make_legacy_aead_tests.go -cipher 3des -mac sha1 -implicit-iv > des_ede3_cbc_sha1_tls_implicit_iv_tests.txt
