# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

function shard_gtest() {
    export GTEST_TOTAL_SHARDS=$(nproc --all)
    if [ -n "${2}" ]; then
        GTEST_TOTAL_SHARDS="${2}"
    fi
    if [ -z ${GTEST_TOTAL_SHARDS} -o ${GTEST_TOTAL_SHARDS} -lt 1 ]; then
        GTEST_TOTAL_SHARDS=4
    fi

    PIDS=()
    COUNTER=0
    while [ $COUNTER -lt $GTEST_TOTAL_SHARDS ]; do
        export GTEST_SHARD_INDEX=$COUNTER
        echo shard_gtest-Command: ${1}
        ${1} &
        PIDS[${COUNTER}]=$!
        COUNTER=$(( COUNTER+1 ))
    done

    for PID in ${PIDS[*]}; do
        wait -f $PID
    done
}
