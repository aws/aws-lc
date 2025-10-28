#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euo pipefail

NAME="awslcci"
VERSION="1.0"
SOURCE_NAMESPACE="${NAME}-${VERSION}"

install_dependencies() {
    dnf -y install rpm-build rpmdevtools
}

setup_rpm() {
    # Setup rpm folder tree. Just use standard folder structure.
    rpmdev-setuptree
}

create_source_archive() {
    if [ ! -d ~/rpmbuild/SOURCES ]; then
        echo "~/rpmbuild/SOURCES directory does not exist!"
        exit 1
    fi

    tar --transform="s,^.,${SOURCE_NAMESPACE}," \
        --exclude='.git' \
        --exclude='.github' \
        --exclude='.gitignore' \
        -czf ~/rpmbuild/SOURCES/${SOURCE_NAMESPACE}.tar.gz .
}

create_spec_file() {
cat > ~/rpmbuild/SPECS/${NAME}.spec <<EOF
Name:           ${NAME}
Version:        ${VERSION}
Release:        1%{?dist}
Summary:        Cryptographic library AWS-LC
Source0:        %{name}-%{version}.tar.gz

License:        Mock-do-not-use-1.0

BuildRequires:  gcc
BuildRequires:  cmake3
BuildRequires:  ninja-build
BuildRequires:  golang
BuildRequires:  perl

%description
RPM package used in AWS-LC CI to test rpmbuild.

# Teach cmake where to put artifacts under the RPM chroot.
# When we later copy artifacts undet the directive %files, the patch is relative
# to the root of the RPM tree.
%global awslc_namespace awslcci
%global cmake_flags -GNinja -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=ON -DCMAKE_INSTALL_PREFIX=%{buildroot}%{_libdir}/%{awslc_namespace}

%prep
%setup -q

# It appears cmake3 package doesn't have the required cmake scriptlets defined.
# So, need to use direct commands.
%build
cmake3 %{cmake_flags}
ninja-build
ninja-build run_tests

# Skip install step.
EOF
}

run_rpmbuild() {
    # Build and compile only i.e. bc.
    rpmbuild -bc ~/rpmbuild/SPECS/${NAME}.spec
}

install_dependencies
setup_rpm
create_source_archive
create_spec_file
run_rpmbuild
