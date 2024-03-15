#!/bin/bash
if [ "$#" -ne 4 ]; then
  echo "../tools/run-proof.sh <dir (arm/x86)>"
  echo "      <asm filename without .S (e.g., bignum_copy)>"
  echo "      <HOL Light command> <output log path>"
  echo "This script runs HOL Light proof at '<dir>/proofs/<asm filename>.ml', and".
  echo "inspects the log file to check whether all proofs are done successfully."
  exit 1
fi

# Return the exit code if any statement fails
set -e

cd ..

s2n_bignum_arch=$1
asm_filename=$2
hol_light_cmd=$3
output_path=${s2n_bignum_arch}/$4

(echo 'Topdirs.dir_directory "+unix";;'; \
 echo 'Topdirs.dir_load Format.std_formatter "unix.cma";;'; \
 echo 'let start_time = Unix.time();;'; \
 echo "loadt \"${s2n_bignum_arch}/proofs/base.ml\";;"; \
 echo "loadt \"${s2n_bignum_arch}/proofs/${asm_filename}.ml\";;"; \
 echo 'let end_time = Unix.time();;'; \
 echo 'Printf.printf "Running time: %f sec, Start unixtime: %f, End unixtime: %f\n" (end_time -. start_time) start_time end_time;;') | eval "$hol_light_cmd" 2>&1 > "$output_path"

# Revert the exit code option since 'grep' may return non-zero.
set +e

grep -r -i "error" --include "$output_path"
if [ $? -eq 0 ]; then
  echo "${s2n_bignum_arch}/proofs/${asm_filename}.ml had error(s)"
  exit 1
fi
