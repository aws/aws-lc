# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:20.04

SHELL ["/bin/bash", "-c"]

ENV DEBIAN_FRONTEND=noninteractive


ENV ANDROID_SDK_URL commandlinetools-linux-8092744_latest
ENV ANDROID_HOME /opt/sdk

# ------------------------------------------------------
# --- Android SDK

RUN set -ex && \
    apt-get update -y && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    python3.8 \
    python3-pip \
    openjdk-8-jdk \
    perl \
    libunwind-dev \
    wget \
    unzip && \
# install go dependencies
    cd /tmp && \
    wget https://dl.google.com/go/go1.13.12.linux-amd64.tar.gz && \
    tar -xvf go1.13.12.linux-amd64.tar.gz && \
    mv go /usr/local && \
# install android-sdk from url source
    mkdir /opt/sdk && \
    mkdir /opt/sdk/cmdline-tools && \
    mkdir /opt/cmdline-tools-tmp && \
    cd /opt/cmdline-tools-tmp && \
    wget -q https://dl.google.com/android/repository/${ANDROID_SDK_URL}.zip && \
    unzip  ${ANDROID_SDK_URL}.zip && \
# move to its final location and export path
    mv ./cmdline-tools ${ANDROID_HOME}/cmdline-tools/latest && \
    export PATH=$PATH:$ANDROID_HOME/cmdline-tools/latest/bin && \
    export PATH=$PATH:$ANDROID_HOME/platform-tools && \
    cd $ANDROID_HOME/cmdline-tools/latest/bin && \
    sdkmanager --update && \
    yes | sdkmanager --licenses && \
# Preinstall AWSLCAndroidTestRunner dependencies, so they don't need to be 
# rebuilt for each new gradle build run.
    sdkmanager "ndk;21.0.6113669" \
    "build-tools;29.0.3" \
    "cmake;3.10.2.4988404" \
    "platforms;android-29" && \
    rm -rf /opt/cmdline-tools-tmp && \
    rm -rf /tmp/* 

ENV GOROOT=/usr/local/go
ENV GO111MODULE=on
ENV PATH="$GOROOT/bin:$PATH"