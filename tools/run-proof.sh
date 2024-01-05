#!/bin/bash
if [ "$#" -ne 3 ]; then
  echo "../tools/run-proof.sh <dir (arm/x86)> <asm filename without .S (e.g., bignum_copy)> <HOL Light command>"
  echo "This script runs HOL Light proof at '<dir>/proofs/<asm filename>.ml'".
  exit 1
fi

# Return the exit code if any statement fails
set -e

cd ..

s2n_bignum_arch=$1
asm_filename=$2
hol_light_cmd=$3

(echo 'Topdirs.dir_directory "+unix";;'; \
 echo 'Topdirs.dir_load Format.std_formatter "unix.cma";;'; \
 echo 'let start_time = Unix.time();;'; \
 echo "loadt \"${s2n_bignum_arch}/proofs/base.ml\";;"; \
 echo "loadt \"${s2n_bignum_arch}/proofs/${asm_filename}.ml\";;"; \
 echo 'let end_time = Unix.time();;'; \
 echo 'Printf.printf "Running time: %f sec, Start unixtime: %f, End unixtime: %f\n" (end_time -. start_time) start_time end_time;;') | eval "$hol_light_cmd" 2>&1
