# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM public.ecr.aws/ubuntu/ubuntu:24.04 AS base

SHELL ["/bin/bash", "-c"]

ENV DEBIAN_FRONTEND=noninteractive


ENV ANDROID_SDK_URL=commandlinetools-linux-13114758_latest
ENV ANDROID_HOME=/opt/sdk
ENV ANDROID_SDK_ROOT=/opt/sdk
ENV GRADLE_VERSION=gradle-7.6.4
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:/opt/sdk/cmdline-tools/latest/bin:$PATH"
# ------------------------------------------------------
# --- Android SDK

RUN <<EOF
set -ex
apt-get update -y
apt-get -y --no-install-recommends upgrade
apt-get -y --no-install-recommends install \
    git \
    libunwind-dev \
    openjdk-17-jdk \
    perl \
    python3.12 \
    python3.12-venv \
    python3-pip \
    unzip \
    wget
EOF

# Setup Android SDK
RUN <<EOF
# Set Java 17 as default
export JAVA17_ALT=$(update-alternatives --list java | grep java-17 | head -1)
update-alternatives --set java $JAVA17_ALT

# Set Java 17 for SDK manager compatibility
export JAVA_HOME=$(find /usr/lib/jvm -name "*java-17*" -type d | head -1)
export PATH=$JAVA_HOME/bin:$PATH

# install android-sdk from url source
mkdir /opt/sdk
mkdir /opt/sdk/cmdline-tools
mkdir /opt/cmdline-tools-tmp
cd /opt/cmdline-tools-tmp
wget -q https://dl.google.com/android/repository/${ANDROID_SDK_URL}.zip
unzip ${ANDROID_SDK_URL}.zip

# move to its final location and export path
mv ./cmdline-tools ${ANDROID_HOME}/cmdline-tools/latest
cd $ANDROID_HOME/cmdline-tools/latest/bin
./sdkmanager --update
yes | ./sdkmanager --licenses

# Preinstall AWSLCAndroidTestRunner android dependencies, so they don't need to be
# rebuilt for each new gradle build run.
./sdkmanager "ndk;28.2.13676358" \
    "build-tools;33.0.3" \
    "cmake;3.18.1" \
    "platforms;android-30"

cd /opt
wget -q https://services.gradle.org/distributions/${GRADLE_VERSION}-all.zip
rm -rf /opt/cmdline-tools-tmp
rm -rf /tmp/*
EOF

# Preinstall gradle dependencies, so they don't need to be redownloaded in the CI.
COPY . /tmp/triggerGradleDownloads/

RUN <<EOF
cd /tmp/triggerGradleDownloads
echo "JAVA_HOME=$JAVA_HOME"
java -version
echo "PATH=$PATH"
./gradlew --no-daemon --refresh-dependencies androidDependencies lint
EOF

# Install Go
ENV GOENV_ROOT="/.goenv"
ENV PATH="${GOENV_ROOT}/shims:${GOENV_ROOT}/bin:/go/bin:$PATH"

COPY --from=scripts setup-go-compiler.sh /tmp
RUN <<EOF
setup_script="/tmp/setup-go-compiler.sh"
${setup_script}
EOF

RUN rm -rf /tmp/*
