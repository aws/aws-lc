// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_OPENSSLV_H
#define OPENSSL_HEADER_OPENSSLV_H

// BORINGSSL_API_VERSION is replaced with AWSLC_API_VERSION to avoid users interpreting AWSLC as BoringSSL.
// Below are BoringSSL's comments on BORINGSSL_API_VERSION.
// BORINGSSL_API_VERSION is a positive integer that increments as BoringSSL
// changes over time. The value itself is not meaningful. It will be incremented
// whenever is convenient to coordinate an API change with consumers. This will
// not denote any special point in development.
//
// A consumer may use this symbol in the preprocessor to temporarily build
// against multiple revisions of BoringSSL at the same time. It is not
// recommended to do so for longer than is necessary.

#define AWSLC_API_VERSION 23

// This string tracks the most current production release version on Github
// https://github.com/aws/aws-lc/releases.
// When bumping the encoded version number, also update the test fixture:
// ServiceIndicatorTest.AWSLCVersionString
// Note: there are two versions of this test. Only one test is compiled
// depending on FIPS mode.
#define AWSLC_VERSION_NUMBER_STRING "1.18.0"


#define OPENSSL_VERSION_NUMBER 0x1010107f
#define SSLEAY_VERSION_NUMBER OPENSSL_VERSION_NUMBER
#define OPENSSL_VERSION_TEXT "OpenSSL 1.1.1 (compatible; AWS-LC " AWSLC_VERSION_NUMBER_STRING ")"

#endif
