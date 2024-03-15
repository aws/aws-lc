#!/bin/bash
if [ "$#" -ne 1 ]; then
  echo "count-proofs.sh <dir (e.g., arm)>"
  exit 1
fi

s2n_bignum_arch=$1
cd $s2n_bignum_arch

num_correct_files=`find . -name "*.correct" | wc -l`
if [ $num_correct_files -eq 0 ]; then
  echo "No .correct file exists. Did you run 'make proofs'?"
  exit 1
fi

# Count the number of *_SUBROUTINE_CORRECT theorems that must be proven
num_correct_ans=`grep 'let [A-Z_0-9]*_SUBROUTINE_CORRECT' proofs/*.ml | wc -l`
# Print & count the *_SUBROUTINE_CORRECT theorems that are actually proven
num_correct_out=`grep 'SUBROUTINE_CORRECT : thm' */*.correct  | cut -f2 -d' ' | sort | uniq | wc -l`
echo "Proven *_SUBROUTINE_CORRECT theorems ($num_correct_out):"
grep 'SUBROUTINE_CORRECT : thm' */*.correct  | cut -f2 -d' ' | sort | uniq

# The two numbers must be equal
echo "Total # SUBROUTINE_CORRECT: ${num_correct_out}/${num_correct_ans}"
if [ $num_correct_ans -ne $num_correct_out ]; then
  exit 1
fi
