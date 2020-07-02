#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core

from cdk.github_codebuild_stack import GitHubCodeBuildStack
from cdk.linux_docker_images_build_stack import LinuxDockerImagesBuildStack
from cdk.windows_docker_image_build_stack import WindowsDockerImageBuildStack
from cdk.ecr_stack import EcrStack
from util.util import EnvUtil

# Initialize app.
app = core.App()

# Fetch environment variables.
aws_account = EnvUtil.get("CDK_DEPLOY_ACCOUNT", "620771051181")
aws_region = EnvUtil.get("CDK_DEPLOY_REGION", "us-west-2")
env = {"account": aws_account, "region": aws_region}

# Define AWS ECR stacks.
# ECR holds the docker images, which are pre-built to accelerate the code builds/tests of git pull requests.
linux_aarch_ecr_repo = EnvUtil.get("ECR_LINUX_AARCH_REPO_NAME", "aws-lc-test-docker-images-linux-aarch")
linux_x86_ecr_repo = EnvUtil.get("ECR_LINUX_X86_REPO_NAME", "aws-lc-test-docker-images-linux-x86")
windows_ecr_repo = EnvUtil.get("ECR_WINDOWS_REPO_NAME", "aws-lc-test-docker-images-windows")
EcrStack(app, linux_aarch_ecr_repo, env=env)
EcrStack(app, linux_x86_ecr_repo, env=env)
EcrStack(app, windows_ecr_repo, env=env)

# Define stacks used to build Docker images.
linux_docker_img_build_stacks = [
    {
        "id": "aws-lc-test-docker-images-build-linux-aarch",
        "repo_name": linux_aarch_ecr_repo,
        "env_type": "ARM",
        "build_spec": "linux-aarch-docker-img-build.yml"
    },
    {
        "id": "aws-lc-test-docker-images-build-linux-x86",
        "repo_name": linux_x86_ecr_repo,
        "env_type": "Linux",
        "build_spec": "linux-x86-docker-img-build.yml"
    }
]
code_build_dir = "./tests/ci/codebuild"
for stack in linux_docker_img_build_stacks:
    LinuxDockerImagesBuildStack(app, stack["id"], stack["repo_name"],
                                "./tests/ci/codebuild/{}".format(stack["build_spec"]), env_type=stack["env_type"],
                                env=env)
# DIND is not supported on Windows and, therefore, AWS CodeBuild is not used to build Windows Server container images.
# Windows Docker images are created by running commands in Windows EC2 instance.
WindowsDockerImageBuildStack(app, "aws-lc-test-docker-images-build-windows", windows_ecr_repo, env=env)

# Define CodeBuild stacks used to run test cases.
is_windows = True
# Define CodeBuild running on Linux aarch.
linux_aarch_test_stacks = [
    {
        "id": "aws-lc-test-ubuntu-19-10--gcc-9x",
        "img": "ubuntu-19.10_gcc-9x_latest",
        "spec": "ubuntu-19.10_gcc-9x_aarch64.yml",
    },
    {
        "id": "aws-lc-test-ubuntu-19-10--clang-9x",
        "img": "ubuntu-19.10_clang-9x_latest",
        "spec": "ubuntu-19.10_clang-9x_aarch64.yml",
    },
]
for stack in linux_aarch_test_stacks:
    GitHubCodeBuildStack(app, stack["id"], linux_aarch_ecr_repo, stack["img"],
                         "./tests/ci/codebuild/{}".format(stack["spec"]), env_type="ARM", privileged=True, env=env)
# Define CodeBuild running on Linux x86-64.
linux_x86_test_stacks = [
    {
        "id": "aws-lc-test-pre-push",
        "img": "ubuntu-18.04_gcc-7x_latest",
        "spec": "pre-push.yml",
    },
    {
        "id": "aws-lc-test-ubuntu-16-04--gcc-5x--x86",
        "img": "ubuntu-16.04_gcc-5x_latest",
        "spec": "ubuntu-16.04_gcc-5x_x86.yml",
    },
    {
        "id": "aws-lc-test-ubuntu-18-04--clang-6x--x86-64",
        "img": "ubuntu-18.04_clang-6x_latest",
        "spec": "ubuntu-18.04_clang-6x_x86-64.yml",
    },
    {
        "id": "aws-lc-test-ubuntu-18-04--gcc-7x--x86-64",
        "img": "ubuntu-18.04_gcc-7x_latest",
        "spec": "ubuntu-18.04_gcc-7x_x86-64.yml",
    },
    {
        "id": "aws-lc-test-ubuntu-19-10--gcc-9x--x86-64",
        "img": "ubuntu-19.10_gcc-9x_latest",
        "spec": "ubuntu-19.10_gcc-9x_x86-64.yml",
    },
    {
        "id": "aws-lc-test-ubuntu-19-10--clang-9x--x86-64",
        "img": "ubuntu-19.10_clang-9x_latest",
        "spec": "ubuntu-19.10_clang-9x_x86-64.yml",
    },
    {
        "id": "aws-lc-test-ubuntu-19-04--gcc-8x--x86-64",
        "img": "ubuntu-19.04_gcc-8x_latest",
        "spec": "ubuntu-19.04_gcc-8x_x86-64.yml",
    },
    {
        "id": "aws-lc-test-ubuntu-19-04--clang-8x--x86-64",
        "img": "ubuntu-19.04_clang-8x_latest",
        "spec": "ubuntu-19.04_clang-8x_x86-64.yml",
    },
    {
        "id": "aws-lc-test-centos-7--gcc-4x--x86",
        "img": "centos-7_gcc-4x_latest",
        "spec": "centos-7_gcc-4x-x86.yml",
    },
    {
        "id": "aws-lc-test-centos-7--gcc-4x--x86-64",
        "img": "centos-7_gcc-4x_latest",
        "spec": "centos-7_gcc-4x-x86-64.yml",
    },
    {
        "id": "aws-lc-test-amazonlinux-2--gcc-7x--x86-64",
        "img": "amazonlinux-2_gcc-7x_latest",
        "spec": "amazonlinux-2_gcc-7x-x86-64.yml",
    },
    {
        "id": "aws-lc-test-s2n--integration",
        "img": "s2n_integration_clang-9x_latest",
        "spec": "s2n_integration.yml",
    },
    {
        "id": "aws-lc-test-fedora-31--gcc-9x",
        "img": "fedora-31_gcc-9x_latest",
        "spec": "fedora-31_gcc-9x_x86-64.yml",
    },
    {
        "id": "aws-lc-test-fedora-31--clang-9x",
        "img": "fedora-31_clang-9x_latest",
        "spec": "fedora-31_clang-9x_x86-64.yml",
    },
]
for stack in linux_x86_test_stacks:
    GitHubCodeBuildStack(app, stack["id"], linux_x86_ecr_repo, stack["img"],
                         "./tests/ci/codebuild/{}".format(stack["spec"]), privileged=True, env=env)
# Define CodeBuild for sanitizer tests.
linux_sanitizer_test_stacks = [
    {
        "id": "aws-lc-test-ubuntu-19-10--clang-9x--sanitizer",
        "img": "ubuntu-19.10_clang-9x_sanitizer_latest",
        "spec": "ubuntu-19.10_clang-9x_aarch64_sanitizer.yml",
        "env_type": "ARM",
        "repo": linux_aarch_ecr_repo,
    },
    {
        "id": "aws-lc-test-ubuntu-19-10--clang-9x--x86-64--sanitizer",
        "img": "ubuntu-19.10_clang-9x_sanitizer_latest",
        "spec": "ubuntu-19.10_clang-9x_x86-64_sanitizer.yml",
        "env_type": "Linux",
        "repo": linux_x86_ecr_repo,
    },
]
for stack in linux_sanitizer_test_stacks:
    GitHubCodeBuildStack(app, stack["id"], stack["repo"], stack["img"],
                         "./tests/ci/codebuild/{}".format(stack["spec"]), env_type=stack["env_type"], privileged=True,
                         env=env)
# Define CodeBuild running on Windows.
GitHubCodeBuildStack(app, "aws-lc-test-windows-msvc2015-x64--vs2015", windows_ecr_repo, "vs2015_latest",
                     "./tests/ci/codebuild/windows-msvc2015-x64.yml", env_type="Windows", env=env)

app.synth()
