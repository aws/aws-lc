import sys

assert sys.version_info.major == 3, "Only python 3 supported"

import cryptography
import cryptography.hazmat.backends.openssl.backend
from cryptography.fernet import Fernet

# exercise simple round trip, then assert that PyCA has linked OpenSSL
k = Fernet.generate_key()
f = Fernet(k)
pt = b"hello world"
assert pt == f.decrypt(f.encrypt(pt))

version = cryptography.hazmat.backends.openssl.backend.openssl_version_text()
assert "OpenSSL" in version, f"PyCA didn't link OpenSSL: {version}"
assert "AWS-LC" not in version, f"PyCA linked AWS-LC: {version}"
