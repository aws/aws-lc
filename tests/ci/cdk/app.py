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
linux_aarch_ecr_repo = EnvUtil.get("ECR_LINUX_AARCH_REPO_NAME", "aws-lc-docker-img-linux-aarch")
linux_x86_ecr_repo = EnvUtil.get("ECR_LINUX_X86_REPO_NAME", "aws-lc-docker-img-linux-x86")
windows_ecr_repo = EnvUtil.get("ECR_WINDOWS_REPO_NAME", "aws-lc-docker-img-windows")
EcrStack(app, linux_aarch_ecr_repo, env=env)
EcrStack(app, linux_x86_ecr_repo, env=env)
EcrStack(app, windows_ecr_repo, env=env)

# Define stacks used to build Docker images.
code_build_dir = "./tests/ci/codebuild"
LinuxDockerImagesBuildStack(app, "aws-lc-test-docker-images-build-linux-aarch", linux_aarch_ecr_repo,
                            "{}/linux-aarch-docker-img-build.yml".format(code_build_dir), env=env)
LinuxDockerImagesBuildStack(app, "aws-lc-test-docker-images-build-linux-x86", linux_x86_ecr_repo,
                            "{}/linux-x86-docker-img-build.yml".format(code_build_dir), env=env)
# DIND is not supported on Windows and, therefore, AWS CodeBuild is not used to build Windows Server container images.
# Windows Docker images are created by running commands in Windows EC2 instance.
WindowsDockerImageBuildStack(app, "aws-lc-test-docker-images-build-windows", windows_ecr_repo, env=env)

# Define CodeBuild stacks used to run test cases.
is_windows = True
# Define CodeBuild running on Linux aarch.
GitHubCodeBuildStack(app, "aws-lc-test-ubuntu-19-10--gcc-9x", linux_aarch_ecr_repo, "ubuntu-19.10_gcc-9x_latest",
                     "{}/ubuntu-19.10_gcc-9x_aarch64.yml".format(code_build_dir), env=env)
GitHubCodeBuildStack(app, "aws-lc-test-ubuntu-19-10--clang-9x", linux_aarch_ecr_repo, "ubuntu-19.10_clang-9x_latest",
                     "{}/ubuntu-19.10_clang-9x_aarch64.yml".format(code_build_dir), env=env)
GitHubCodeBuildStack(app, "aws-lc-test-ubuntu-19-10--clang-9x--sanitizer", linux_aarch_ecr_repo,
                     "ubuntu-19.10_clang-9x_sanitizer_latest",
                     "{}/ubuntu-19.10_clang-9x_aarch64_sanitizer.yml".format(code_build_dir), privileged=True, env=env)
# Define CodeBuild running on Linux x86-64.
GitHubCodeBuildStack(app, "aws-lc-test-pre-push", linux_x86_ecr_repo, "ubuntu-18.04_gcc-7x_latest",
                     "{}/pre-push.yml".format(code_build_dir), env=env)
GitHubCodeBuildStack(app, "aws-lc-test-ubuntu-16-04--gcc-5x--x86", linux_x86_ecr_repo, "ubuntu-16.04_gcc-5x_latest",
                     "{}/ubuntu-16.04_gcc-5x_x86.yml".format(code_build_dir), env=env)
GitHubCodeBuildStack(app, "aws-lc-test-ubuntu-18-04--clang-6x--x86-64", linux_x86_ecr_repo,
                     "ubuntu-18.04_clang-6x_latest", "{}/ubuntu-18.04_clang-6x_x86-64.yml".format(code_build_dir),
                     env=env)
GitHubCodeBuildStack(app, "aws-lc-test-ubuntu-18-04--gcc-7x--x86-64", linux_x86_ecr_repo, "ubuntu-18.04_gcc-7x_latest",
                     "{}/ubuntu-18.04_gcc-7x_x86-64.yml".format(code_build_dir), env=env)
GitHubCodeBuildStack(app, "aws-lc-test-ubuntu-19-10--gcc-9x--x86-64", linux_x86_ecr_repo, "ubuntu-19.10_gcc-9x_latest",
                     "{}/ubuntu-19.10_gcc-9x_x86-64.yml".format(code_build_dir), env=env)
GitHubCodeBuildStack(app, "aws-lc-test-ubuntu-19-10--clang-9x--x86-64--sanitizer", linux_x86_ecr_repo,
                     "ubuntu-19.10_clang-9x_sanitizer_latest",
                     "{}/ubuntu-19.10_clang-9x_x86-64_sanitizer.yml".format(code_build_dir), privileged=True, env=env)
GitHubCodeBuildStack(app, "aws-lc-test-ubuntu-19-10--clang-9x--x86-64", linux_x86_ecr_repo,
                     "ubuntu-19.10_clang-9x_latest", "{}/ubuntu-19.10_clang-9x_x86-64.yml".format(code_build_dir),
                     env=env)
GitHubCodeBuildStack(app, "aws-lc-test-ubuntu-19-04--gcc-8x--x86-64", linux_x86_ecr_repo, "ubuntu-19.04_gcc-8x_latest",
                     "{}/ubuntu-19.04_gcc-8x_x86-64.yml".format(code_build_dir), env=env)
GitHubCodeBuildStack(app, "aws-lc-test-ubuntu-19-04--clang-8x--x86-64", linux_x86_ecr_repo,
                     "ubuntu-19.04_clang-8x_latest", "{}/ubuntu-19.04_clang-8x_x86-64.yml".format(code_build_dir),
                     env=env)
GitHubCodeBuildStack(app, "aws-lc-test-centos-7--gcc-4x--x86", linux_x86_ecr_repo, "centos-7_gcc-4x_latest",
                     "{}/centos-7_gcc-4x-x86.yml".format(code_build_dir), env=env)
GitHubCodeBuildStack(app, "aws-lc-test-centos-7--gcc-4x--x86-64", linux_x86_ecr_repo, "centos-7_gcc-4x_latest",
                     "{}/centos-7_gcc-4x-x86-64.yml".format(code_build_dir), env=env)
GitHubCodeBuildStack(app, "aws-lc-test-amazonlinux-2--gcc-7x--x86-64", linux_x86_ecr_repo,
                     "amazonlinux-2_gcc-7x_latest", "{}/amazonlinux-2_gcc-7x-x86-64.yml".format(code_build_dir),
                     env=env)
GitHubCodeBuildStack(app, "aws-lc-test-s2n--integration", linux_x86_ecr_repo, "s2n_integration_clang-9x_latest",
                     "{}/s2n_integration.yml".format(code_build_dir), env=env)
GitHubCodeBuildStack(app, "aws-lc-test-fedora-31--gcc-9x", linux_x86_ecr_repo, "fedora-31_gcc-9x_latest",
                     "{}/fedora-31_gcc-9x_x86-64.yml".format(code_build_dir), env=env)
GitHubCodeBuildStack(app, "aws-lc-test-fedora-31--clang-9x", linux_x86_ecr_repo, "fedora-31_clang-9x_latest",
                     "{}/fedora-31_clang-9x_x86-64.yml".format(code_build_dir), env=env)
# Define CodeBuild running on Windows.
GitHubCodeBuildStack(app, "aws-lc-test-windows-msvc2015-x64--vs2015", windows_ecr_repo, "vs2015_latest",
                     "{}/windows-msvc2015-x64.yml".format(code_build_dir), is_windows, env=env)

app.synth()
