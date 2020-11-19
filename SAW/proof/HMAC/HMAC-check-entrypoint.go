/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0
 */

package main

import (
	utility "aws-lc-verification/proof/common"
	"log"
	"os"
)

func main() {
	log.Printf("Started HMAC check.")
	// When 'HMAC_SELECTCHECK' is undefined, quickcheck is executed.
	env_var := os.Getenv("HMAC_SELECTCHECK")
	if len(env_var) == 0 {
		utility.RunSawScript("verify-HMAC-SHA384-quickcheck.saw")
		return
	}

	// When 'HMAC_SELECTCHECK' is defined, selectcheck is executed.
	utility.RunSawScript("verify-HMAC-SHA384-selectcheck.saw")

	log.Printf("Completed HMAC check.")
}
