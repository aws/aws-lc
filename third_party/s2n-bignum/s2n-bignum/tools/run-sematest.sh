#!/bin/bash
if [ "$#" -ne 2 ]; then
  echo "run-sematest.sh <dir (e.g., arm)> <N>"
  echo "This script runs the simulator ('<dir>/proofs/simulator.native') that tests the semantics "
  echo "of instructions. It launches N simulators in parallel, and uses the given "
  echo "HOL Light command to run them."
  echo "The current directory where this script is run must be <dir>."
  exit 1
fi

s2n_bignum_arch=$1
nproc=$2
simulator_path=${s2n_bignum_arch}/proofs/simulator.native

log_paths=()
children_pids=()
for (( i = 1; i <= $nproc; i++ )) ; do
  log_path=`mktemp`
  log_paths[$i]=$log_path
  (cd ..; "${simulator_path}" >$log_path 2>&1) &
  background_pid=$!
  children_pids[$i]=$background_pid
  echo "- Child $i (pid $background_pid) has started (log path: $log_path)"
done

for (( i = 1; i <= $nproc; i++ )) ; do
  wait ${children_pids[$i]}
  echo "- Last 100 lines of simulator $i's log (path: ${log_paths[$i]}):"
  tail -100 ${log_paths[$i]}

  # Revert the exit code option since 'grep' may return non-zero.
  set +e
  grep -i "error:\|exception:" ${log_paths[$i]}
  if [ $? -eq 0 ]; then
    echo "Simulator $i failed!"
    exit 1
  else
    echo "- Simulator $i finished successfully"
  fi
  set -e
done
