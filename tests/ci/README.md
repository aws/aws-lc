# CI for AWS-LC
We use prebuilt docker images for all of our builds for speed and consistency.

## Setup
 To setup the images for local testing or testing in your own AWS account see
the platform specific `README` in docker_images/*.

Once you have the docker images uploaded to AWS Elastic Container Registry you
can setup the AWS CodeBuild projects that use the custom image with the
appropriate buildspec files in codebuild/*.

## Local testing
The best way to test AWS-LC locally is to use the same Docker containers AWS
CodeBuild uses.
1. Install Docker
2. Navigate to your AWS-LC project directory
3. Build the docker image you want to test
4. Run the docker image
   *   Use `-v` to pass a volume from the host to the container, `pwd`:`pwd`
       mounts the same path on the host to the container. This ensures the
       container will build and test your exact working state.
   *  Use `-w` to change to that directory inside the container after launching
      it
5. Run the build

For example testing x86-64 Ubuntu 19.10 clang 9x:
```
$ cd $AWS_LC_PROJECT_ROOT
$ docker build -t ubuntu-19.10:clang-9x tests/ci/docker_images/linux-x86/ubuntu-19.10_clang-9x/
$ docker run -v `pwd`:`pwd` -w `pwd` -it ubuntu-19.10:clang-9x
$ ./tests/ci/run_posix_tests.sh
```

## Test locations
### Unit tests
Runs all tests for:
* Debug
* Release
* Small
* No assembly
* Shared libs

CI Tool|Compiler|CPU platform|OS
------------ | -------------| -------------|-------------
CodeBuild|gcc 4.8.5|x86|Centos 7
CodeBuild|gcc 4.8.5|x86-64|Centos 7
CodeBuild|gcc 5.4.0|x86|Ubuntu 16.04
CodeBuild|gcc 7.3.1|x86-64|AL2
CodeBuild|gcc 7.3.1|aarch64|AL2
CodeBuild|gcc 7.4.4|x86-64|Ubuntu 18.04
CodeBuild|gcc 8.3.0|x86-64|Ubuntu 19.04
CodeBuild|clang 6.0.0|x86-64|Ubuntu 18.04
CodeBuild|clang 8.0.0|x86-64|Ubuntu 19.04
CodeBuild|clang 9.0.0|x86-64|Ubuntu 19.10
CodeBuild|clang 9.0.0|aarch64|ubuntu 19.10
CodeBuild|clang 9.0.1|x86-64|Fedora 31
CodeBuild|clang 10.0.0|aarch64|Ubuntu 20.04
CodeBuild|clang 10.0.0|x86-64|Ubuntu 20.04
CodeBuild|Visual Studio 2015|x86-64|Windows Server 10
Travis|Xcode 11*|x86-64|macOS 10.14

\* Apple Xcode 11 supplies what Apple calls clang 11 which is equivalent to llvm
clang 8.0.0

### Sanitizer tests
Runs all tests with:
* Address sanitizer
* Memory sanitizer
* Control flow integrity
* Thread sanitizer
* Undefined behavior sanitizer

CI Tool|Compiler|CPU platform|OS
------------ | -------------| -------------|-------------
CodeBuild|clang 9.0.0|x86-64|Ubuntu 19.10
CodeBuild|clang 9.0.0|aarch64|ubuntu 19.10

### Valgrind tests

The following Valgrind tests are run for a subset of targets in `utils/all_tests.json` using the debug build of AWS-LC:

CI Tool|Compiler|CPU platform|OS| memcheck 
------------ | -------------| -------------|-------------|-------------
CodeBuild|gcc 7.3.1|x86-64|AL2 | X
