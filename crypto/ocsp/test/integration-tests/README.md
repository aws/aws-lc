## Overview
These root certificate files were taken from [Amazon Trust Services](https://www.amazontrust.com/repository/). Amazon Root CA 1 - 3 refer to the respective root certificate's distinguished name.
Certificates will always expire and this also applies to these root certificates. The respective expiration date for each is listed below.
* AmazonRootCA1: Jan 17 00:00:00 2038 GMT
* AmazonRootCA2: May 26 00:00:00 2040 GMT
* AmazonRootCA3: May 26 00:00:00 2040 GMT

We've set up our tests to warn us to update these certificates within a year of expiring.

## How to Update
1. Navigate to the [Amazon Trust Services website](https://www.amazontrust.com/repository/) and find a root certificate. The root certificate should have two corresponding test links that test for "valid" and "revoked" certificates against it.
2. Replace the expiring cert with the new root certificate. Our tests expect the PEM format.
3. Replace the two "valid" and "revoked" certificate endpoints with the new corresponding test endpoints.
4. Check the expiration date of the other root certificates in this folder. If the other root certificates are expiring within 5 years, we should update these expiring root certificates as well. Repeat the process from Step 1 until all root certificates are updated.
