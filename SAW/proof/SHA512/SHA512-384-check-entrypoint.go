/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0
 */

package main

import (
	"fmt"
	"io/ioutil"
	"log"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync"
)

// A utility function to terminate this program when err exists.
func checkError(e error) {
	if e != nil {
		log.Fatal(e)
	}
}

// A function to create and run "verify-SHA512-384-check.saw" given a "target_num".
func createAndRunSawScript(target_num int, wg *sync.WaitGroup) {
	log.Printf("Start creating saw script for selected num %d", target_num)
	// Create a new saw script for the target_num.
	file_name := fmt.Sprint("verify-SHA512-384-check-num-", target_num, ".saw")
	file, err := os.Create(file_name)
	checkError(err)
	// Read file content of verification template.
	content, err := ioutil.ReadFile("verify-SHA512-384-selectcheck-template.txt")
	checkError(err)
	verification_template := string(content)
	// Replace some placeholders of the file content with target values.
	text := strings.Replace(verification_template, "TARGET_NUM_PLACEHOLDER", strconv.Itoa(target_num), 1)
	defer file.Close()
	file.WriteString(text)
	defer os.Remove(file_name)
	// Run saw script.
	defer wg.Done()
	runSawScript(file_name)
}

// A function to run saw script.
func runSawScript(path_to_saw_file string) {
	log.Printf("Running saw script %s", path_to_saw_file)
	cmd := exec.Command("saw", path_to_saw_file)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	err := cmd.Run()
	checkError(err)
}

func main() {
	log.Printf("Starting SHA512-384 check.")
	// When 'SHA512_384_SELECTCHECK' is undefined, quickcheck is executed.
	env_var := os.Getenv("SHA512_384_SELECTCHECK")
	if len(env_var) == 0 {
		runSawScript("verify-SHA512-384-quickcheck.saw")
		return
	}

	// When 'SHA512_384_SELECTCHECK' is defined, formal verification is executed with all `len` given a 'num'.
	// Due to memory usage (each select_check takes 8GB memory) and limit of container size (largest one has 145GB memory),
	// not all nums are used to run formal verification. Only below nums are selected.
	target_nums := []int{0, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 127}

	// Generate saw scripts based on above verification template and target num ranges.
	var wg sync.WaitGroup
	for _, num := range target_nums {
		wg.Add(1)
		go createAndRunSawScript(num, &wg)
	}

	wg.Wait()
	log.Printf("Completed SHA512-384 check.")
}
