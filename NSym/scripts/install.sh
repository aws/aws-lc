#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

SAW_URL='https://saw-builds.s3.us-west-2.amazonaws.com/saw-0.9.0.99-2023-06-08-ab46c76e0-Linux-x86_64.tar.gz'
C2A_URL='https://cryptol-air-interface.s3.us-west-2.amazonaws.com/cryptol-air-interface-2023-11-20-fd3447e-Linux-x86_64.tar.gz'
ELF_URL='https://ocaml-elf-loader.s3.us-west-2.amazonaws.com/elf_loader-2025-09-23-c95cf1c-Linux_x86_64.tar.gz'
OSI_URL='https://ocaml-smt-interface.s3.us-west-2.amazonaws.com/ocaml_smt_interface-2025-09-23-9654c87-Linux_x86_64.tar.gz'
NSYM_URL='https://native-code-symbolic-simulator.s3.us-west-2.amazonaws.com/nsym-2025-09-23-ae32e4c-Linux_x86_64.tar.gz'

mkdir -p /bin /deps

# fetch SAW
rm -rf /deps/saw
mkdir -p /deps/saw
wget $SAW_URL -O /deps/saw.tar.gz
tar -x -f /deps/saw.tar.gz --one-top-level=/deps/saw
cp /deps/saw/*/bin/saw /bin/saw
cp /deps/saw/*/bin/cryptol /bin/cryptol

# fetch Cryptol-Air-Interface
rm -rf /deps/cryptol-air-interface
mkdir -p /deps/cryptol-air-interface
wget $C2A_URL -O /deps/cryptol-air-interface.tar.gz
tar -x -f /deps/cryptol-air-interface.tar.gz --one-top-level=/deps/cryptol-air-interface
cp /deps/cryptol-air-interface/*/bin/cryptol-to-air /bin/cryptol-to-air

# fetch OCaml-SMT-Interface
rm -rf /deps/ocaml-smt-interface
mkdir -p /deps/ocaml-smt-interface
wget $OSI_URL -O /deps/ocaml-smt-interface.tar.gz
tar -x -f /deps/ocaml-smt-interface.tar.gz --one-top-level=/deps/ocaml-smt-interface
cp -r /deps/ocaml-smt-interface/*/lib/. /root/.opam/4.14.0/lib/

# fetch OCamlElfLoader
rm -rf /deps/ocaml-elf-loader
mkdir -p /deps/ocaml-elf-loader
wget $ELF_URL -O /deps/ocaml-elf-loader.tar.gz
tar -x -f /deps/ocaml-elf-loader.tar.gz --one-top-level=/deps/ocaml-elf-loader
cp -r /deps/ocaml-elf-loader/*/lib/. /root/.opam/4.14.0/lib/

# fetch NSym
rm -rf /deps/nsym
mkdir -p /deps/nsym
wget $NSYM_URL -O /deps/nsym.tar.gz
tar -x -f /deps/nsym.tar.gz --one-top-level=/deps/nsym
cp -r /deps/nsym/*/lib/. /root/.opam/4.14.0/lib/
