/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0
 */

package main

import (
	utility "aws-lc-verification/proof/common"
	"log"
	"math"
	"os"
	"sync"
)

// The AES GCM proofs use more than 8.2 gb of memory each, using 9 gb for headroom
const memory_used_per_test uint64 = 9e9

func main() {
	log.Printf("Started AES-GCM check.")
	// When 'AES_GCM_SELECTCHECK' is undefined, quickcheck is executed.
	env_var := os.Getenv("AES_GCM_SELECTCHECK")
	if len(env_var) == 0 {
		utility.RunSawScript("verify-AES-GCM-quickcheck.saw")
		return
	}
	// When 'AES_GCM_SELECTCHECK' is defined, formal verification is executed
	// with generated saw scripts based on the verification template and
	// different values of `mres` and `res_mres`. Each of these parameters can
	// be anything in the range [0, 15], but for now, we only check a subset of
	// all possible mres/res_mres values. In particular, we check the following
	// (mres, res_mres) pairs:
	//
	// (0, 0), (1, 0)
	mres_values := [2]int{0, 1}
	res_mres_value := 0
	var wg sync.WaitGroup
	process_count := 0

	total_memory := utility.SystemMemory()
	num_parallel_process := int(math.Floor((float64(total_memory) / float64(memory_used_per_test))))
	log.Printf("System has %d bytes of memory, running %d jobs in parallel", total_memory, num_parallel_process)
	for i := 0; i < 2; i++ {
		wg.Add(1)
		saw_template := "verify-AES-GCM-selectcheck-template.txt"
		mres_placeholder_name := "TARGET_MRES_PLACEHOLDER"
		res_mres_placeholder_name := "TARGET_RES_MRES_PLACEHOLDER"
		go utility.CreateAndRunSawScript(saw_template, []string{}, mres_placeholder_name, mres_values[i], res_mres_placeholder_name, res_mres_value, &wg)
		utility.Wait(&process_count, num_parallel_process, &wg)
	}

	wg.Wait()
	log.Printf("Completed AES-GCM check.")
}
