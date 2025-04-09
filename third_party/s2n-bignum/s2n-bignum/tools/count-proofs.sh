#!/bin/bash
if [ "$#" -ne 1 ]; then
  echo "count-proofs.sh <dir (e.g., arm)>"
  exit 1
fi

s2n_bignum_arch=$1
cd $s2n_bignum_arch > /dev/null

num_correct_files=`find . -name "*.correct" | wc -l`
if [ $num_correct_files -eq 0 ]; then
  echo "No .correct file exists. Did you run 'make proofs'?"
  exit 1
fi

# An environment variable setting for consistent sorting results.
export LC_ALL=C

# Count the number of *_SUBROUTINE_CORRECT theorems that must be proven
num_correct_ans=`cat proofs/specifications.txt | wc -l`
# Print & count the *_SUBROUTINE_CORRECT theorems that are actually proven
num_correct_out=`grep 'SUBROUTINE_CORRECT : thm' */*.correct  | cut -f2 -d' ' | sort | uniq | wc -l`

# Print the *_SUBROUTINE_CORRECT theorems that are actually proven
proven_thms_log=`mktemp`
echo "Proven *_SUBROUTINE_CORRECT theorems ($num_correct_out):"
grep 'SUBROUTINE_CORRECT : thm' */*.correct  | cut -f2 -d' ' | sort | uniq > $proven_thms_log
cat $proven_thms_log

echo "Total # SUBROUTINE_CORRECT: ${num_correct_out}/${num_correct_ans}"
diff $proven_thms_log proofs/specifications.txt
