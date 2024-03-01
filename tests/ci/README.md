# CI for AWS-LC
For speed and consistency, our CodeBuild CI build projects utilze prebuilt docker images.

## Setup
To setup the docker images for local testing or testing in your own AWS account see
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

For example testing x86-64 Ubuntu 20.04 clang 9x:
```
$ cd $AWS_LC_PROJECT_ROOT
$ docker build -t ubuntu-20.04:clang-9x tests/ci/docker_images/linux-x86/ubuntu-20.04_clang-9x/
$ docker run -v `pwd`:`pwd` -w `pwd` -it ubuntu-20.04:clang-9x
$ ./tests/ci/run_posix_tests.sh
```

Before building a "non-base" image you need to build the corresponding base one.
For example, to be able to build the `ubuntu-20.04_clang-9x` image from above,
you first need to build the base image `ubuntu-20.04_base`. In addition, the
base image has to be built with with the dependencies directory as the context
so it has access to the script that installs dependencies. So the full command
would look like this:
```
$ docker build -t ubuntu-18.04:base -f tests/ci/docker_images/linux-x86/ubuntu-18.04_base/Dockerfile tests/ci/docker_images/dependencies
```
For more examples, see `build_images.sh` script in directories corresponding
to different platforms (linux-x86, linux-aarch, windows).

### Issues with proxy.golang.org when running images locally

If you are having issues contacting `proxy.golang.org` try running the image
with the `GOPROXY=direct`. For example:
```bash
docker run -e GOPROXY=direct -v `pwd`:`pwd` -w `pwd` -it ubuntu-20.04:clang-9x
```

## Test locations

Our CI uses a combination of CodeBuild and GitHub Workflow build environments. Both for transparency and to assist 
contributors in diagnosing issues, most CI build logs are publicly available. If a CI failure occurs on your pull
request and you are unable to diagnose it (whether due to lack of log availability or otherwise), our team will gladly 
assist you in identifying the cause. For other CI-related concerns, you may submit an 
[issue](https://github.com/aws/aws-lc/issues) to our Github repository.

### Unit tests

General test suite with a varying set of build options (FIPS (shared-build), non-FIPS, debug,
shared, static, etc.) is executed on the following combinations:

| CI Tool           | Compiler                          | CPU     | OS                | Public Logs                      |
|-------------------|-----------------------------------|---------|-------------------|----------------------------------|
| CodeBuild         | gcc 4.1.3                         | x86     | Ubuntu 10.04      | _aws-lc-ci-linux-x86_            | 
| CodeBuild         | gcc 4.8.5                         | x86     | Centos 7          | _aws-lc-ci-linux-x86_            |
| CodeBuild         | gcc 4.8.5                         | x86-64  | Centos 7          | _aws-lc-ci-linux-x86_            |
| CodeBuild         | gcc 5.4.0                         | x86     | Ubuntu 16.04      | _aws-lc-ci-linux-x86_            |
| CodeBuild         | gcc 7.3.1                         | x86-64  | AL2               | _aws-lc-ci-linux-x86_            |
| CodeBuild         | gcc 7.3.1                         | aarch64 | AL2               | _aws-lc-ci-linux-arm_            |
| CodeBuild         | gcc 7.5.0                         | x86-64  | Ubuntu 18.04      | _aws-lc-ci-linux-x86_            |
| CodeBuild         | gcc 7.5.0                         | x86-64  | Ubuntu 20.04      | _aws-lc-ci-linux-x86_            |
| CodeBuild         | gcc 7.5.0                         | aarch64 | Ubuntu 20.04      | _aws-lc-ci-linux-arm_            |
| CodeBuild         | gcc 8.4.0                         | x86-64  | Ubuntu 20.04      | _aws-lc-ci-linux-x86_            |
| CodeBuild         | gcc 8.4.0                         | aarch64 | Ubuntu 20.04      | _aws-lc-ci-linux-arm_            |
| CodeBuild         | gcc 11                            | x86-64  | AL2023            | _aws-lc-ci-linux-x86_            |
| CodeBuild         | gcc 11                            | aarch64 | AL2023            | _aws-lc-ci-linux-arm_            |
| CodeBuild         | gcc 11                            | x86-64  | Ubuntu 22.04      | _aws-lc-ci-linux-x86_            |
| CodeBuild         | gcc 11                            | aarch64 | Ubuntu 22.04      | _aws-lc-ci-linux-arm_            |
| CodeBuild         | gcc 12                            | x86-64  | Ubuntu 22.04      | _aws-lc-ci-linux-x86_            |
| CodeBuild         | gcc 12                            | aarch64 | Ubuntu 22.04      | _aws-lc-ci-linux-arm_            |
| CodeBuild         | clang 7.0.1                       | x86-64  | AL2               | _aws-lc-ci-linux-x86_            |
| CodeBuild         | clang 7.0.1                       | aarch64 | AL2               | _aws-lc-ci-linux-arm_            |
| CodeBuild         | clang 6.0.0                       | x86-64  | Ubuntu 18.04      | _aws-lc-ci-linux-x86_            |
| CodeBuild         | clang 9.0.1                       | x86-64  | Fedora 31         | _aws-lc-ci-linux-x86_            |
| CodeBuild         | clang 7.0.1                       | x86-64  | Ubuntu 20.04      | _aws-lc-ci-linux-x86_            |
| CodeBuild         | clang 7.0.1                       | aarch64 | Ubuntu 20.04      | _aws-lc-ci-linux-arm_            |
| CodeBuild         | clang 8.0.1                       | x86-64  | Ubuntu 20.04      | _aws-lc-ci-linux-x86_            |
| CodeBuild         | clang 8.0.1                       | aarch64 | Ubuntu 20.04      | _aws-lc-ci-linux-arm_            |
| CodeBuild         | clang 9.0.1                       | x86-64  | Ubuntu 20.04      | _aws-lc-ci-linux-x86_            |
| CodeBuild         | clang 9.0.1                       | aarch64 | Ubuntu 20.04      | _aws-lc-ci-linux-arm_            |
| CodeBuild         | clang 10.0.0                      | x86-64  | Ubuntu 20.04      | _aws-lc-ci-linux-x86_            |
| CodeBuild         | clang 10.0.0                      | aarch64 | Ubuntu 20.04      | _aws-lc-ci-linux-arm_            |
| CodeBuild         | clang 15.0.6                      | x86-64  | AL2023            | _aws-lc-ci-linux-x86_            |
| CodeBuild         | clang 15.0.6                      | aarch64 | AL2023            | _aws-lc-ci-linux-arm_            |
| CodeBuild         | Visual Studio 2015                | x86-64  | Windows Server 19 | _aws-lc-ci-windows-x86_          |
| CodeBuild         | Visual Studio 2017                | x86-64  | Windows Server 19 | _aws-lc-ci-windows-x86_          |
| GitHub Workflow   | AppleClang 13.0.0                 | x86-64  | macOS 11          | _macOS-x86_ and _macOS-x86-FIPS_ |
| GitHub Workflow   | AppleClang 14.0.0                 | aarch64 | macOS 12          | _macOS-ARM_ and _macOS-ARM-FIPS_ |
| AWS Device Farm   | Android ndkVersion "21.0.6113669" | aarch64 | Android 10        | N/A                              |
| AWS Device Farm   | Android ndkVersion "21.0.6113669" | aarch64 | Android 11        | N/A                              |
| AWS Device Farm   | Android ndkVersion "21.0.6113669" | aarch64 | Android 12        | N/A                              |

### FIPS static build tests

Unfortunately, it's a known issue that the FIPS build has limited support when producing a static library. The static AWS-LC FIPS build is only supported on Linux based platforms for x86_64 and aarch64.

 CI Tool         | Compiler                          | CPU     | OS              | Public Logs           |
-----------------|-----------------------------------|---------|-----------------|-----------------------|
 CodeBuild       | gcc 4.8.5                         | x86-64  | Centos 7        | _aws-lc-ci-linux-x86_ |
 CodeBuild       | gcc 7.3.1                         | x86-64  | AL2             | _aws-lc-ci-linux-x86_ |
 CodeBuild       | gcc 7.3.1                         | aarch64 | AL2             | _aws-lc-ci-linux-arm_ |
 CodeBuild       | gcc 7.5.0                         | x86-64  | Ubuntu 18.04    | _aws-lc-ci-linux-x86_ |
 CodeBuild       | gcc 7.5.0                         | x86-64  | Ubuntu 20.04    | _aws-lc-ci-linux-x86_ |
 CodeBuild       | gcc 7.5.0                         | aarch64 | Ubuntu 20.04    | _aws-lc-ci-linux-arm_ |
 CodeBuild       | gcc 8.4.0                         | x86-64  | Ubuntu 20.04    | _aws-lc-ci-linux-x86_ |
 CodeBuild       | gcc 8.4.0                         | aarch64 | Ubuntu 20.04    | _aws-lc-ci-linux-arm_ |
 CodeBuild       | gcc 11                            | x86-64  | AL2023          | _aws-lc-ci-linux-x86_ |
 CodeBuild       | gcc 11                            | aarch64 | AL2023          | _aws-lc-ci-linux-arm_ |
 CodeBuild       | gcc 11                            | x86-64  | Ubuntu 22.04    | _aws-lc-ci-linux-x86_ |
 CodeBuild       | gcc 11                            | aarch64 | Ubuntu 22.04    | _aws-lc-ci-linux-arm_ |
 CodeBuild       | gcc 12                            | x86-64  | Ubuntu 22.04    | _aws-lc-ci-linux-x86_ |
 CodeBuild       | gcc 12                            | aarch64 | Ubuntu 22.04    | _aws-lc-ci-linux-arm_ |
 CodeBuild       | clang 7.0.1                       | x86-64  | AL2             | _aws-lc-ci-linux-x86_ |
 CodeBuild       | clang 7.0.1                       | aarch64 | AL2             | _aws-lc-ci-linux-arm_ |
 CodeBuild       | clang 6.0.0                       | x86-64  | Ubuntu 18.04    | _aws-lc-ci-linux-x86_ |
 CodeBuild       | clang 9.0.1                       | x86-64  | Fedora 31       | _aws-lc-ci-linux-x86_ |
 CodeBuild       | clang 7.0.1                       | x86-64  | Ubuntu 20.04    | _aws-lc-ci-linux-x86_ |
 CodeBuild       | clang 7.0.1                       | aarch64 | Ubuntu 20.04    | _aws-lc-ci-linux-arm_ |
 CodeBuild       | clang 8.0.1                       | x86-64  | Ubuntu 20.04    | _aws-lc-ci-linux-x86_ |
 CodeBuild       | clang 8.0.1                       | aarch64 | Ubuntu 20.04    | _aws-lc-ci-linux-arm_ |
 CodeBuild       | clang 9.0.1                       | x86-64  | Ubuntu 20.04    | _aws-lc-ci-linux-x86_ |
 CodeBuild       | clang 9.0.1                       | aarch64 | Ubuntu 20.04    | _aws-lc-ci-linux-arm_ |
 CodeBuild       | clang 10.0.0                      | x86-64  | Ubuntu 20.04    | _aws-lc-ci-linux-x86_ |
 CodeBuild       | clang 10.0.0                      | aarch64 | Ubuntu 20.04    | _aws-lc-ci-linux-arm_ |
 CodeBuild       | clang 15.0.6                      | x86-64  | AL2023          | _aws-lc-ci-linux-x86_ |
 CodeBuild       | clang 15.0.6                      | aarch64 | AL2023          | _aws-lc-ci-linux-arm_ |
 AWS Device Farm | Android ndkVersion "21.0.6113669" | aarch64 | Android 10      | N/A                   |
 AWS Device Farm | Android ndkVersion "21.0.6113669" | aarch64 | Android 11      | N/A                   |
 AWS Device Farm | Android ndkVersion "21.0.6113669" | aarch64 | Android 12      | N/A                   |

### Sanitizer tests

Runs all tests with:
* Address sanitizer
* Memory sanitizer
* Control flow integrity
* Thread sanitizer
* Undefined behavior sanitizer

 CI Tool   | Compiler     | CPU platform | OS     | Public Logs           |
-----------|--------------|--------------|--------|-----------------------|
 CodeBuild | clang 15.0.6 | x86-64       | AL2023 | _aws-lc-ci-linux-x86_ |
 CodeBuild | clang 15.0.6 | aarch64      | AL2023 | _aws-lc-ci-linux-arm_ |

### Valgrind tests

The following Valgrind tests are run for a subset of targets in `utils/all_tests.json` using the debug build of AWS-LC:

 CI Tool   | Compiler | CPU platform | OS     | memcheck | Public Logs           |
-----------|----------|--------------|--------|----------|-----------------------|
 CodeBuild | gcc 11   | x86-64       | AL2023 | X        | _aws-lc-ci-linux-x86_ |
 CodeBuild | gcc 11   | aarch64      | AL2023 | X        | _aws-lc-ci-linux-arm_ |

### Fuzz tests

All Fuzz tests under /fuzz are run in CodeBuild for an hour total. 


 CI Tool   | Compiler     | CPU platform | OS           | Flags  |
-----------|--------------|--------------|--------------|--------|
 CodeBuild | clang 10.0.0 | x86-64       | Ubuntu 20.04 | ASAN=1 | 
 CodeBuild | clang 10.0.0 | aarch64      | ubuntu 20.04 | ASAN=1 |

To add a new fuzz test create a new executable follow [libFuzzer's](https://llvm.org/docs/LibFuzzer.html) documentation
and existing tests. Generate a seed corpus and check it into a folder with the same name as the executable. The CI will
pull in any files from the seed folder and merge it into the growing corpus in EFS.


### Cryptofuzz

Each change is built and tested with [Cryptofuzz](https://github.com/guidovranken/cryptofuzz) for an hour. A seed corpus
is included in tests/docker_images/cryptofuzz_data.zip. As new inputs are found they are saved in a shared corpus across
runs in AWS EFS. Cryptofuzz is built with 3 modules:
* AWS-LC
* Botan
* Crypto++

 CI Tool   | Compiler     | CPU platform | OS           | Flags  |
-----------|--------------|--------------|--------------|--------|
 CodeBuild | clang 10.0.0 | x86-64       | Ubuntu 20.04 | ASAN=1 |
 CodeBuild | clang 10.0.0 | aarch64      | Ubuntu 20.04 | ASAN=1 |
