# Android CI for AWS-LC
AWS-LC wants to ensure that our tests and build work correctly on Android. Insipred from the CRT Team's [`AWSCRTAndroidTestRunner`](https://github.com/awslabs/aws-c-common/tree/main/AWSCRTAndroidTestRunner), this mini Android test harness is intended to be used within our Android CI with AWS Device Farm. The tests will include `crypto_test`, `urandom_test`, `decrepit_test` and `ssl_test`, referenced from regular test dimensions. This app can be tested with the docker image at `tests/ci/docker_images/linux-x86/ubuntu-20.04_android`.

## Setup
1. Assuming all the commands are being run from this folder: `cd tests/ci/android`
2. `docker build -t ubuntu-20.04:android ../docker_images/linux-x86/ubuntu-20.04_android/`
3. Run the docker image from root of aws-lc. The container needs access to aws-lc's source code to build.
   ```
   docker run -it -v `pwd`:`pwd` -w `pwd` ubuntu-20.04:android`
   ```
4. `cd AWSLCAndroidTestRunner`
5. Run `./gradlew assembleDebug assembleAndroidTest` to build both the app and test apks with the AWS-LC non-FIPS debug build.
6. Run `./gradlew assembleDebug assembleAndroidTest -PRelease` to build both the app and test apks with the AWS-LC non-FIPS release build.
7. Run `./gradlew assembleDebug assembleAndroidTest -PFIPS` to build both the app and test apks with the AWS-LC FIPS build (only armv8 is supported).

## Local testing
Alternatively run `./gradlew cC` to build both apks, then run the tests locally on a connected Android device/emulator right after. Add the `-PRelease` or `-PFIPS` as needed.

### Emulator
1. To set up an emulator on Mac OS X, go to https://developer.android.com/studio and download the latest version for Android Studio. Launch and install the dmg file, and the set up wizard should guide you through the setup. Once installed, you get the Welcome to Android Studio window, where you can configure and use SDK manager to install Android SDKs and dependencies.
2. Android emulators are managed through a UI called AVD Manager, which can be accessed from Android Studio. Start the Android Studio app, then create a blank project.
3. Go to the Tools menu -> Android -> AVD Manager. If no emulator has been created you should click the "Create Virtual Device" button.
4. Select "Pixel 2" (or any of the newer preferred options), then select "x86" images and download R (API Level:30, ABI:x86_64, Android 11.0 (Google APIs)). Click through the rest of the virtual device set up and then "Finish". The newly created device should be launchable from the AVD Manager window.
5. Run `./gradlew cC` on `AWSLCAndroidTestRunner`, and the emulator will be automatically detected. Outputted debug logs from the emulator device can be seen from the log interface in any blank project created in Android Studio. You can also use `awslc-test` tag to filter through specific logs outputted from running `AWSLCAndroidTestRunner`.
