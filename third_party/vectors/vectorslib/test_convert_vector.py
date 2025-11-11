"""
Test that convert_vector.py produces the same output as convert_wycheproof.go

Run from root of repo as
```
python third_party/vectors/test_convert_vector.py
```
"""

import pathlib
import tempfile
import subprocess
import filecmp
import sys
import os
import difflib

# From line 196 of convert_wycheproof.go
existingFiles = [
    "aes_cbc_pkcs5_test.json",
    "aes_cmac_test.json",
    "aes_gcm_siv_test.json",
    "aes_gcm_test.json",
    "chacha20_poly1305_test.json",
    "dsa_test.json",
    "ecdh_secp224r1_test.json",
    "ecdh_secp256r1_test.json",
    "ecdh_secp384r1_test.json",
    "ecdh_secp521r1_test.json",
    "ecdsa_secp224r1_sha224_test.json",
    "ecdsa_secp224r1_sha256_test.json",
    "ecdsa_secp224r1_sha512_test.json",
    "ecdsa_secp256r1_sha256_test.json",
    "ecdsa_secp256r1_sha512_test.json",
    "ecdsa_secp384r1_sha384_test.json",
    "ecdsa_secp384r1_sha512_test.json",
    "ecdsa_secp521r1_sha512_test.json",
    "ecdsa_secp256k1_sha256_test.json",
    "ecdsa_secp256k1_sha512_test.json",
    "eddsa_test.json",
    "hkdf_sha1_test.json",
    "hkdf_sha256_test.json",
    "hkdf_sha384_test.json",
    "hkdf_sha512_test.json",
    "hmac_sha1_test.json",
    "hmac_sha224_test.json",
    "hmac_sha256_test.json",
    "hmac_sha384_test.json",
    "hmac_sha512_test.json",
    "hmac_sha512_224_test.json",
    "hmac_sha512_256_test.json",
    "hmac_sha3_224_test.json",
    "hmac_sha3_256_test.json",
    "hmac_sha3_384_test.json",
    "hmac_sha3_512_test.json",
    "kw_test.json",
    "kwp_test.json",
    "primality_test.json",
    "rsa_oaep_2048_sha1_mgf1sha1_test.json",
    "rsa_oaep_2048_sha224_mgf1sha1_test.json",
    "rsa_oaep_2048_sha224_mgf1sha224_test.json",
    "rsa_oaep_2048_sha256_mgf1sha1_test.json",
    "rsa_oaep_2048_sha256_mgf1sha256_test.json",
    "rsa_oaep_2048_sha384_mgf1sha1_test.json",
    "rsa_oaep_2048_sha384_mgf1sha384_test.json",
    "rsa_oaep_2048_sha512_mgf1sha1_test.json",
    "rsa_oaep_2048_sha512_mgf1sha512_test.json",
    "rsa_oaep_3072_sha256_mgf1sha1_test.json",
    "rsa_oaep_3072_sha256_mgf1sha256_test.json",
    "rsa_oaep_3072_sha512_mgf1sha1_test.json",
    "rsa_oaep_3072_sha512_mgf1sha512_test.json",
    "rsa_oaep_4096_sha256_mgf1sha1_test.json",
    "rsa_oaep_4096_sha256_mgf1sha256_test.json",
    "rsa_oaep_4096_sha512_mgf1sha1_test.json",
    "rsa_oaep_4096_sha512_mgf1sha512_test.json",
    "rsa_oaep_misc_test.json",
    "rsa_pkcs1_2048_test.json",
    "rsa_pkcs1_3072_test.json",
    "rsa_pkcs1_4096_test.json",
    "rsa_pss_2048_sha1_mgf1_20_test.json",
    "rsa_pss_2048_sha256_mgf1_0_test.json",
    "rsa_pss_2048_sha256_mgf1_32_test.json",
    "rsa_pss_3072_sha256_mgf1_32_test.json",
    "rsa_pss_4096_sha256_mgf1_32_test.json",
    "rsa_pss_4096_sha512_mgf1_32_test.json",
    "rsa_pss_misc_test.json",
    "rsa_sig_gen_misc_test.json",
    "rsa_signature_2048_sha224_test.json",
    "rsa_signature_2048_sha256_test.json",
    "rsa_signature_2048_sha384_test.json",
    "rsa_signature_2048_sha512_test.json",
    "rsa_signature_3072_sha256_test.json",
    "rsa_signature_3072_sha384_test.json",
    "rsa_signature_3072_sha512_test.json",
    "rsa_signature_4096_sha384_test.json",
    "rsa_signature_4096_sha512_test.json",
    "rsa_signature_test.json",
    "x25519_test.json",
    "xchacha20_poly1305_test.json",
]


def test_file_conversion(json_file):
    sources_dir = pathlib.Path("third_party/wycheproof_testvectors")
    input_file = sources_dir / json_file

    if not input_file.exists():
        print(f"Skipping {json_file} - source file not found")
        return True

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = pathlib.Path(tmpdir)

        # temporary output files
        go_file = tmpdir_path / f"go_{json_file.replace('.json', '.txt')}"
        python_file = tmpdir_path / f"python_{json_file.replace('.json', '.txt')}"

        result = subprocess.run(
            [
                "go",
                "run",
                "util/convert_wycheproof/convert_wycheproof.go",
                str(input_file),
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        with open(go_file, "w") as f:
            f.write(result.stdout)

        result = subprocess.run(
            [
                sys.executable,
                "third_party/vectors/convert_vector.py",
                "--input",
                str(input_file),
                "--output",
                str(python_file),
            ],
            capture_output=True,
            text=True,
            check=True,
        )

        if filecmp.cmp(go_file, python_file, shallow=False):
            print(f"PASS: {json_file}")
            return True
        else:
            print(f"FAIL: {json_file}")
            with open(go_file, "r") as f:
                go_content = f.read()
            with open(python_file, "r") as f:
                python_content = f.read()
            print("Diff from Go to Python:")
            difference = difflib.unified_diff(
                go_content.splitlines(keepends=True),
                python_content.splitlines(keepends=True),
                fromfile=str(go_file),
                tofile=str(python_file),
            )
            print("".join(difference))
            return False


def main():
    passed = 0
    failed = 0

    for json_file in existingFiles:
        if test_file_conversion(json_file):
            passed += 1
        else:
            failed += 1

    print("=" * 60)
    print(f"Results: {passed} passed, {failed} failed")

    if failed > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
