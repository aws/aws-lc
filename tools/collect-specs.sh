#!/bin/bash
if [ "$#" -ne 1 ]; then
  echo "collect-specs.sh <dir (e.g., arm)>"
  echo "This script collects the names of HOL Light theorems that are"
  echo "specifications of correctness of assembly functions."
  exit 1
fi

s2n_bignum_arch=$1
cd $s2n_bignum_arch

# An env. var for sorting
export LC_ALL=C
grep 'let [A-Z_0-9]*_SUBROUTINE_CORRECT' proofs/*.ml | cut -f2 -d' ' | sort
