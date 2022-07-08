#!/usr/bin/env bash
set -e -x

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
CRATE_DIR="${TMP_DIR}"/aws-lc-sys

if [[ ! "${OSTYPE}" == "darwin"* ]]; then
  # TODO: Update docker images so these preliminary steps aren't needed
  if [[ ! $(type -P "cargo") ]]; then
    wget -q -O- https://sh.rustup.rs | sh -s -- -y
  fi
  source "${HOME}"/.cargo/env

  if [[ $(lsb_release -a |grep -i ubuntu) ]]; then
    apt-get -y update
    apt-get -y install make
  else
    yum -y update
    yum -y install make
  fi

  rm -f /usr/bin/cc
  rm -f /usr/bin/c++

  C_COMPILER_LIST=( /usr/bin/gcc-* )
  CPP_COMPILER_LIST=( /usr/bin/g++-* )
  C_COMPILER="${C_COMPILER_LIST[0]}"
  CPP_COMPILER="${CPP_COMPILER_LIST[0]}"

  if [[ ! ${C_COMPILER} == "/usr/bin/gcc-*"  ]]; then
    update-alternatives --install /usr/bin/cc  gcc "${C_COMPILER}" 100
    update-alternatives --install /usr/bin/c++ g++ "${CPP_COMPILER}" 100
  fi

  C_COMPILER_LIST=( /usr/bin/clang-* )
  CPP_COMPILER_LIST=( /usr/bin/clang++-* )
  C_COMPILER="${C_COMPILER_LIST[0]}"
  CPP_COMPILER="${CPP_COMPILER_LIST[0]}"

  if [[ ! ${C_COMPILER} == "/usr/bin/clang-*"  ]]; then
    update-alternatives --install /usr/bin/cc  clang "${C_COMPILER}" 100
    update-alternatives --install /usr/bin/c++ clang++ "${CPP_COMPILER}" 100
  fi
fi

pushd "${CRATE_DIR}"

export GOPROXY=direct
cargo clean \
  && cargo build \
  && cargo test \
  && cargo test --release \
  && cargo publish --dry-run --allow-dirty \
  && cargo clean

popd
