# `libcrypto` Verification
This repository contains specifications and correctness proofs for the functions in the [BoringSSL](https://boringssl.googlesource.com/boringssl/) implementation of `libcrypto`.

## Building and running
The easiest way to build the library and run the proofs is to use [Docker](https://docs.docker.com/get-docker/). To check the proofs, execute the following steps in the top-level directory of the repository.

1. Clone the submodules: `git submodule update --init`
2. Build a Docker image: `docker build -t awslc-saw .`
3. Run the proofs inside the Docker container: ``docker run -v `pwd`:`pwd` -w `pwd` awslc-saw``

Running ``docker run -it -v `pwd`:`pwd` -w `pwd` --entrypoint bash awslc-saw`` will enter an interactive shell within the container, which is often useful for debugging.
