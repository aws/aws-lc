# macOS Setup

```
$ docker buildx install
```

# Setup for AL2 or other Linux distributions
The following setup is required for Docker in order to be able to build cross-platform images.

By default, Docker Desktop is installed and configured with [Buildx](https://docs.docker.com/build/install-buildx/),
but this is not installed by default on most Linux distributions of docker. The following steps are required to install
on Amazon Linux 2.

## Steps for AL2
The following steps are required for Amazon Linux 2, note that symlink step is required due to a packaging bug in the
current Docker RPM for AL2.

```
$ sudo ln -s /usr/libexec/docker/cli-plugins/buildx /usr/libexec/docker/cli-plugins/docker-buildx
$ sudo systemctl restart docker
$ docker buildx install
$ sudo yum install -y qemu-system-aarch64 qemu-system-x86 qemu-user-binfmt
$ docker buildx create --name=container --driver=docker-container --use
$ docker run --privileged --rm tonistiigi/binfmt --install all
```

This may periodically need to be reset:
```
$ docker run --privileged --rm tonistiigi/binfmt --uninstall arm64,arm,riscv64,mips64le,s390x,ppc64le,mips64
$ docker run --privileged --rm tonistiigi/binfmt --install all
```