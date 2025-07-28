# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

function shard_gtest() {
    export GTEST_TOTAL_SHARDS=${NUM_CPU_THREADS}
    if [ -n "${2}" ]; then
        GTEST_TOTAL_SHARDS="${2}"
    fi
    if [ -z ${GTEST_TOTAL_SHARDS} -o ${GTEST_TOTAL_SHARDS} -lt 1 ]; then
        GTEST_TOTAL_SHARDS=4
    fi

    echo shard_gtest-Command: ${1}
    PIDS=()
    COUNTER=0
    while [ $COUNTER -lt $GTEST_TOTAL_SHARDS ]; do
        export GTEST_SHARD_INDEX=$COUNTER
        ${1} &
        PIDS[${COUNTER}]=$!
        COUNTER=$(( COUNTER+1 ))
    done

    RESULT=0
    for PID in ${PIDS[*]}; do
        # The exit status of wait is the exit status of $PID
        # `if` considers a zero exit status to be "true", but we need to branch on a non-zero exit status
        if ! wait -f $PID; then
          RESULT=1
        fi
    done
    unset GTEST_SHARD_INDEX
    unset GTEST_TOTAL_SHARDS

    if [ $RESULT -ne "0" ]; then
      #  Run w/o sharding to isolate the problem
      echo shard_gtest-Command: ${1} failed
      echo Running again w/o sharding
      ${1}
    fi

    return $RESULT
}
