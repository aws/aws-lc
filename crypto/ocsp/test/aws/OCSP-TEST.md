## Overview
This original OCSP-TEST.md file and CA, OCSP, and server certs were taken from s2n and modified for our needs.
link: https://github.com/aws/s2n-tls/tree/main/tests/pems/ocsp
The files in this directory represent a cert hierarchy to test OCSP response stapling. This folder is for retaining the keys and certificates used to recreate OCSP der responses. Contents of der responses are hard coded in the ocsp_test.cc test file.

## CA
- ca_cert.pem
- ca_key.pem

Issuer for all of the other certs in the directory.
Since this is a test PKI, we do an intermediate for issuing leaf cert(s).

## OCSP
* ocsp_cert.pem
* ocsp_expired_cert.pem
* ocsp_key.pem

Cert/key for the test OCSP responder. OCSP responses will be signed by the key.
The CN for this cert matches the URI in the Server Cert's "Authority Information Access" x509 extension.

### Generating Expired OCSP Signing Cert
`ocsp_expired_cert.pem` is an expired test certificate used to sign OCSP responses.
```
openssl req -new -key ocsp_key.pem -out ocsp.csr
openssl x509 -req -in ocsp.csr -CA ca_cert.pem -CAkey ca_key.pem -days 0 -CAcreateserial -out expired_ocsp_cert.pem
```

## Server Cert
* server_cert.pem
* server_key.pem

The leaf cert/key. OCSP responses will be generated for this cert.

## OCSP response
* ocsp_response.der

DER formatted OCSP response for the Server Cert.

## Generating a OCSP request for the leaf cert
```
openssl ocsp -issuer ca_cert.pem -cert server_cert.pem -reqout ocsp_request.der
```
```
openssl ocsp -no_nonce -issuer ca_cert.pem -cert server_cert.pem -reqout ocsp_request_no_nonce.der
```
OCSP Request signing is optional, and these requests aren't usually signed in the wild.

## Generating a signed OCSP request for the leaf cert
```
openssl ocsp -issuer ca_cert.pem -cert server_cert.pem -signer ocsp_cert.pem -signkey ocsp_key.pem -reqout ocsp_request_signed.der
```
```
openssl ocsp -sha256 -issuer ca_cert.pem -cert server_cert.pem -signer ocsp_cert.pem -signkey ocsp_key.pem -reqout ocsp_request_signed_sha256.der
```
```
openssl ocsp -issuer ca_cert.pem -cert server_cert.pem -signer ocsp_cert.pem -signkey ocsp_key.pem -sign_other ca_cert.pem -reqout ocsp_request_attached_cert.der
```

## Generating a new OCSP response for the leaf cert
The current OCSP responses expire in 10 years. Our tests using these files only check if the timefield value has been 
parsed correctly, so an update shouldn't be necessary.

From the current directory:

### Run the server
```
# With nextUpdate
openssl ocsp -port 8889 -text -CA ca_cert.pem \
      -index certs.txt \
      -rkey ocsp_key.pem \
      -rsigner ocsp_cert.pem \
      -nrequest 1 \
      -ndays $(( 365 * 100 ))

# Without nextUpdate
openssl ocsp -port 8890 -text -CA ca_cert.pem \    
      -index certs.txt \
      -rkey ocsp_key.pem \
      -rsigner ocsp_cert.pem \
      -nrequest 1
```

### Run the client and save the result to file
```
# With nextUpdate
openssl ocsp -CAfile ca_cert.pem \
      -url http://127.0.0.1:8889 \
      -issuer ca_cert.pem \
      -verify_other ocsp_cert.pem \
      -sha1 -cert server_cert.pem -respout ocsp_response.der

# Without nextUpdate
openssl ocsp -CAfile ca_cert.pem \                                                                                                                                                                          
      -url http://127.0.0.1:8890 \
      -issuer ca_cert.pem \
      -verify_other ocsp_cert.pem \
      -sha1 -cert server_cert.pem -respout ocsp_response_no_next_update.der
```

## Recreate revoked OCSP responses

### Run the server
```
openssl ocsp -port 8889 -text -CA ca_cert.pem \                                                                                                                                                             
      -index certs_revoked.txt \
      -rkey ocsp_key.pem \
      -rsigner ocsp_cert.pem \
      -nrequest 1 \
      -ndays $(( 365 * 10 ))
```


### Run the client and save the result to file
```
openssl ocsp -CAfile ca_cert.pem \                                                                                                                                            
      -url http://127.0.0.1:8889 \
      -issuer ca_cert.pem \
      -verify_other ocsp_cert.pem \
      -sha1 -cert server_cert.pem -respout ocsp_revoked_response.der
```

## Recreate unknown cert status OCSP responses

### Run the server
```
openssl ocsp -port 8889 -text -CA ca_cert.pem \
      -index certs_unknown.txt \
      -rkey ocsp_key.pem \
      -rsigner ocsp_cert.pem \
      -nrequest 1 \
      -ndays $(( 365 * 10 ))
```


### Run the client and save the result to file
```
openssl ocsp -CAfile ca_cert.pem \
      -url http://127.0.0.1:8889 \
      -issuer ca_cert.pem \
      -verify_other ocsp_cert.pem \
      -sha1 -cert server_cert.pem -respout ocsp_unknown_response.der
```


## Recreate wrong signer OCSP responses

### Run the server
```
openssl ocsp -port 8889 -text -CA ca_cert.pem \                                                                                                                                                             
      -index certs_revoked.txt \
      -rkey server_ecdsa_key.pem \
      -rsigner server_ecdsa_cert.pem \
      -nrequest 1 \
      -ndays $(( 365 * 10 ))
```


### Run the client and save the result to file
```
openssl ocsp -CAfile ca_cert.pem \                                                                                                                                                                
      -url http://127.0.0.1:8889 \
      -issuer ca_cert.pem \
      -verify_other ocsp_cert.pem \
      -sha1 -cert server_cert.pem -respout ocsp_response_wrong_signer.der
```

## Recreate expired signer OCSP responses
### Run the server
```
openssl ocsp -port 8890 -text -CA ca_cert.pem \
      -index certs.txt \          
      -rkey ocsp_key.pem \ 
      -rsigner ocsp_expired_cert.pem \     
      -nrequest 1 
```


### Run the client and save the result to file
```
openssl ocsp -CAfile ca_cert.pem \
      -url http://127.0.0.1:8890 \
      -issuer ca_cert.pem \
      -verify_other ocsp_expired_cert.pem \
      -sha1 -cert server_cert.pem -respout ocsp_response_expired_signer.der
```

## For SHA-256 OCSP responses

### Run the server
```
openssl ocsp -port 8889 -text -CA ca_cert.pem \                                                                                                                                                        
      -index certs.txt \
      -rkey ocsp_key.pem \
      -rsigner ocsp_cert.pem \
      -nrequest 1 \
      -ndays $(( 365 * 10 ))
```


### Run the client and save the result to file
```
openssl ocsp -CAfile ca_cert.pem \                                                                                                                                                              
      -url http://127.0.0.1:8889 \
      -issuer ca_cert.pem \
      -verify_other ocsp_cert.pem \
      -sha256 -cert server_cert.pem -respout ocsp_response_sha256.der
```


