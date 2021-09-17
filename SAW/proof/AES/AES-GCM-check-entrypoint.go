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

// Due to memory usage (each select_check takes 8GB memory) and limit of container size (largest one has 145GB memory).
// |aes_gcm_process_limit| is needed here to limit the number of saw processes.
const aes_gcm_process_limit int = 15

func main() {
	log.Printf("Started AES-GCM check.")
	// When 'AES_GCM_SELECTCHECK' is undefined, quickcheck is executed.
	env_var := os.Getenv("AES_GCM_SELECTCHECK")
	if len(env_var) == 0 {
		utility.RunSawScript("verify-AES-GCM-quickcheck.saw")
		return
	}
	selectcheck_range_start := utility.ParseSelectCheckRange("AES_GCM_SELECTCHECK_START", 1)
	selectcheck_range_end := utility.ParseSelectCheckRange("AES_GCM_SELECTCHECK_END", 384)
	// When 'AES_GCM_SELECTCHECK' is defined, formal verification is executed with different `evp_cipher_update_len`.
	// Generate saw scripts based on the verification template and evp_cipher_update_len range [1, 384].
	var wg sync.WaitGroup
	process_count := 0
	for i := selectcheck_range_start; i <= selectcheck_range_end; i++ {
		wg.Add(1)
		saw_template := "verify-AES-GCM-selectcheck-template.txt"
		placeholder_name := "TARGET_LEN_PLACEHOLDER"
		go utility.CreateAndRunSawScript(saw_template, placeholder_name, i, &wg)
		utility.Wait(&process_count, aes_gcm_process_limit, &wg)
	}

	wg.Wait()
	log.Printf("Completed AES-GCM check.")
}
