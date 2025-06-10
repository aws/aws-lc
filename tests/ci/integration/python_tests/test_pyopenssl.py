import sys

assert sys.version_info.major == 3, "Only python 3 supported"

if sys.version_info.minor >= 14:
    print("PyOpenSSL import currently broken on mainline python >= 3.14")
    sys.exit()

import OpenSSL
from OpenSSL import SSL

# ensure libssl properly loaded
version = SSL.OpenSSL_version(SSL.OPENSSL_VERSION)
assert b"OpenSSL" in version, f"PyOpenSSL didn't link OpenSSL: {version}"
assert b"AWS-LC" not in version, f"PyOpenSSL linked AWS-LC: {version}"

# ensure libcrypto properly loaded
assert len(OpenSSL.crypto.get_elliptic_curves()) > 0
