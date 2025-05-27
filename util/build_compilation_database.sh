#!/usr/bin/env bash

set -ex

BASE_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}/" )/.." &> /dev/null && pwd )

TMP_DIR=`mktemp -d`
echo ${TMP_DIR}
AWS_LC_BUILD="${TMP_DIR}/AWS-LC-BUILD"

MY_CMAKE_FLAGS=("-DCMAKE_BUILD_TYPE=Debug" "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON" "-DDISABLE_GO=ON")

mkdir -p "${AWS_LC_BUILD}"

cmake "${BASE_DIR}" -B "${AWS_LC_BUILD}" "${MY_CMAKE_FLAGS[@]}" "${@}"

cmake --build "${AWS_LC_BUILD}" -j 4 --target all_tests

cp "${AWS_LC_BUILD}"/compile_commands.json "${BASE_DIR}"/
