#!/usr/bin/env python3

# Converts Wycheproof test vectors from JSON to file_test.h format.
# Inspired by util/convert_wycheproof/convert_wycheproof.go

import sys
import tempfile
import pathlib
import json
from typing import Union

# Handle imports for both direct execution and module import
try:
    from vectorslib import utils
except ModuleNotFoundError:
    import utils


def format_header(filename: str, algorithm: str) -> str:
    """Format the file header comment"""
    return f"""# Imported from Wycheproof's {filename}
# Converted to file_test.h format by third_party/vectors/sync.py
# Do not edit by hand.
#
# Algorithm: {algorithm}

"""


def write_instruction(out, name: str, value: Union[str, int, dict, None]) -> None:
    """Write an instruction line: [name = value]"""
    if value is None:
        # Skip None values - they indicate optional fields not present in this test group
        return
    elif isinstance(value, (str, int)):
        out.write(f"[{name} = {value}]\n")
    elif isinstance(value, dict):
        for key in sorted(value.keys()):
            out.write(f"[{name}.{key} = {value[key]}]\n")
    else:
        raise ValueError(f"Unsupported type for instruction: {type(value)}")


def write_attribute(out, name: str, value: Union[str, int]) -> None:
    """Write an attribute line: name = value"""
    if isinstance(value, (str, int)):
        out.write(f"{name} = {value}\n")
    else:
        raise ValueError(f"Unsupported type for attribute: {type(value)}")


def write_test_group(out, test_group: dict) -> None:
    """Write test group instructions"""
    # Skip metadata fields that don't affect test execution
    skip_meta_keys = {
        "tests",  # Array of test cases, processed separately
        "type",   # Test type identifier, not used in file_test.h format
        "source", # Source file reference, not needed in converted format
    }
    # Skip key formats we don't use (we use DER instead of PEM, and don't test with JWK)
    skip_key_formats = {
        "jwk",           # JSON Web Key format
        "keyJwk",        # Public key in JWK format
        "privateKeyJwk", # Private key in JWK format
        "keyPem",        # Public key in PEM format
        "privateKeyPem", # Private key in PEM format
    }
    
    skip_keys = skip_meta_keys | skip_key_formats
    
    for key in sorted(test_group.keys()):
        if key not in skip_keys:
            write_instruction(out, key, test_group[key])
    out.write("\n")


def write_test(out, test: dict) -> None:
    """Write a single test case"""
    out.write(f"# tcId = {test['tcId']}\n")
    
    if test.get("comment"):
        out.write(f"# {test['comment']}\n")
    
    skip_keys = {"tcId", "comment", "flags"}
    for key in sorted(test.keys()):
        if key not in skip_keys:
            write_attribute(out, key, test[key])
    
    if test.get("flags"):
        write_attribute(out, "flags", ",".join(test["flags"]))
    
    out.write("\n")


def convert_file(infile: pathlib.Path, outfile: pathlib.Path) -> None:
    """Convert a Wycheproof JSON file to file_test.h format."""
    assert infile.is_file()
    outfile.parent.mkdir(parents=True, exist_ok=True)

    with open(infile, "r") as json_in:
        data = json.load(json_in)

    with open(outfile, "w") as out:
        out.write(format_header(infile.name, data["algorithm"]))
        for group in data["testGroups"]:
            write_test_group(out, group)
            for test in group["tests"]:
                write_test(out, test)


if __name__ == "__main__":
    import unittest

    class TestConversion(unittest.TestCase):
        def test_convert_aes_gcm(self):
            """Test conversion of aes_gcm_test.json"""
            with tempfile.TemporaryDirectory() as tmpdir:
                tmpdir_path = pathlib.Path(tmpdir)
                input_file = pathlib.Path("upstream/wycheproof/testvectors_v1/aes_gcm_test.json")
                output_file = tmpdir_path / "aes_gcm_test.txt"

                if not input_file.exists():
                    self.skipTest(f"Input file not found: {input_file}")

                convert_file(input_file, output_file)
                self.assertTrue(output_file.exists())

                # Verify basic structure
                content = output_file.read_text()
                self.assertIn("# Algorithm: AES-GCM", content)
                self.assertIn("[ivSize = 96]", content)
                self.assertIn("# tcId = 1", content)
                self.assertIn("key = ", content)
                self.assertIn("result = ", content)

    unittest.main()
