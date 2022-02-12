# Android CI for AWS-LC
AWS-LC wants to ensure that our tests and build work correctly on Android. Insipred from the CRT Team's [`AWSCRTAndroidTestRunner`](https://github.com/awslabs/aws-c-common/tree/main/AWSCRTAndroidTestRunner), this mini Android test harness is intended to be used within our Android CI with AWS Device Farm. The tests will include `crypto_test`, `urandom_test`, `decrepit_test` and `ssl_test`, referenced from regular test dimensions. This app can be tested with the docker image at `tests/ci/docker_images/linux-x86/ubuntu-20.04_android`.

## Setup
1. `docker build -t ubuntu-20.04:android ../docker_images/linux-x86/ubuntu-20.04_android/`
2. `cd AWSLCAndroidTestRunner`
3. Run `./gradlew assembleDebug assembleAndroidTest` to build both the app and test apks with the AWS-LC non-FIPS debug build.
4. Run `./gradlew assembleDebug assembleAndroidTest -PRelease` to build both the app and test apks with the AWS-LC non-FIPS release build.
5. Run `./gradlew assembleDebug assembleAndroidTest -PFIPS` to build both the app and test apks with the AWS-LC FIPS build (only armv8 is supported).

## Local testing
Alternatively run `./gradlew cC` to build both apks, then run the tests locally on a connected Android device/emulator right after. Add the `-PRelease` or `-PFIPS` as needed.
