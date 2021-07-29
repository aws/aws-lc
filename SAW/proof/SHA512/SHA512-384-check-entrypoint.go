/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0
 */

package main

import (
	utility "aws-lc-verification/proof/common"
	"log"
	"os"
	"sync"
)

const sha_process_limit int = 15

func main() {
	log.Printf("Started SHA512-384 check.")
	// When 'SHA512_384_SELECTCHECK' is undefined, quickcheck is executed.
	env_var := os.Getenv("SHA512_384_SELECTCHECK")
	if len(env_var) == 0 {
		utility.RunSawScript("verify-SHA512-384-quickcheck.saw")
		return
	}

	// When 'SHA512_384_SELECTCHECK' is defined, formal verification is executed with all `len` given a 'num'.
	// Due to memory usage (each select_check takes 8GB memory) and limit of container size (largest one has 145GB memory),
	// not all nums are used to run formal verification. Only below nums are selected.
	target_nums := []int{0, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 127}

	// Generate saw scripts based on above verification template and target num ranges.
	var wg sync.WaitGroup
	process_count := 0
	for _, num := range target_nums {
		wg.Add(1)
		saw_template := "verify-SHA512-384-selectcheck-template.txt"
		placeholder_name := "TARGET_NUM_PLACEHOLDER"
		go utility.CreateAndRunSawScript(saw_template, placeholder_name, num, &wg)
		utility.Wait(&process_count, sha_process_limit, &wg)
	}

	wg.Wait()
	log.Printf("Completed SHA512-384 check.")
}
