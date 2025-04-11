#!/bin/bash
# This script must be run from the "x86/" directory

if [ "$#" -ne 1 ]; then
  echo "list-x86-insns.sh <output.ml>"
fi

tmp=`mktemp`
grep '^  0x' proofs/big*ml | grep '(\*' | grep -v '\[' | grep -v '\]' | \
    grep -vi push | grep -vi pop | grep -wv RET | grep -wiv rsp | \
    grep -v '\* J' | grep -v Memop | cut -f2 -d: | sort | uniq > $tmp

outfile=$1

echo "let iclasses = [" > "$outfile"

while read -r line; do
  echo "[${line}];" >> "$outfile"
done <$tmp

echo "];;" >> "$outfile"
