# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:20.04

SHELL ["/bin/bash", "-c"]

ENV ANDROID_SDK_URL sdk-tools-linux-3859397
ENV ANDROID_HOME /opt/android-sdk

# ------------------------------------------------------
# --- Android SDK

RUN apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install openjdk-8-jdk wget unzip && \
# install go dependencies
    cd /tmp && \
    wget https://dl.google.com/go/go1.13.12.linux-amd64.tar.gz && \
    tar -xvf go1.13.12.linux-amd64.tar.gz && \
    mv go /usr/local && \
# install android-sdk from url source
    mkdir /opt/android-sdk && \                                                                                                     
    mkdir /opt/android-sdk-tmp && \
    cd /opt/android-sdk-tmp && \
    wget -q https://dl.google.com/android/repository/${ANDROID_SDK_URL}.zip && \
    unzip  ${ANDROID_SDK_URL}.zip && \
# move to its final location and export path
    mv ./tools ${ANDROID_HOME}/tools && \
    export PATH=$PATH:$ANDROID_HOME/tools/bin && \
    export PATH=$PATH:$ANDROID_HOME/platform-tools && \
    cd ${ANDROID_SDK_HOME} && \
    yes | sdkmanager --licenses && \
    rm -rf /opt/android-sdk-tmp && \
    rm -rf /tmp/* 

ENV GOROOT=/usr/local/go
ENV GO111MODULE=on
ENV PATH="$GOROOT/bin:$PATH"