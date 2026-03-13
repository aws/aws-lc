// Copyright (c) 2021, Google Inc.
// SPDX-License-Identifier: ISC

//go:build ignore

// trimvectors takes an ACVP vector set file and discards all but a single test
// from each test group. This hope is that this achieves good coverage without
// having to check in megabytes worth of JSON files.
package main

import (
	"encoding/json"
	"os"
)

func main() {
	var vectorSets []interface{}
	decoder := json.NewDecoder(os.Stdin)
	if err := decoder.Decode(&vectorSets); err != nil {
		panic(err)
	}

	// The first element is the metadata which is left unmodified.
	for i := 1; i < len(vectorSets); i++ {
		vectorSet := vectorSets[i].(map[string]interface{})
		testGroups := vectorSet["testGroups"].([]interface{})
		for _, testGroupInterface := range testGroups {
			testGroup := testGroupInterface.(map[string]interface{})
			tests := testGroup["tests"].([]interface{})

			keepIndex := 10
			if keepIndex >= len(tests) {
				keepIndex = len(tests) - 1
			}

			testGroup["tests"] = []interface{}{tests[keepIndex]}
		}
	}

	encoder := json.NewEncoder(os.Stdout)
	encoder.SetIndent("", "  ")
	if err := encoder.Encode(vectorSets); err != nil {
		panic(err)
	}
}
