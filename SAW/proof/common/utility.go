/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0
 */

package common

import (
	"fmt"
	"io/ioutil"
	"log"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync"
	"syscall"
)

// A utility function to terminate this program when err exists.
func CheckError(e error) {
	if e != nil {
		log.Fatal(e)
	}
}

// A function to parse select check parameter range.
// e.g. if the env var |AES_GCM_SELECTCHECK_RANGE_START| is set, this func will parse its value
func ParseSelectCheckRange(env_var_name string, default_val int) int {
	env_var_val := os.Getenv(env_var_name)
	if len(env_var_val) == 0 {
		return default_val
	}
	ret, err := strconv.Atoi(env_var_val)
	if err != nil {
		log.Fatal("Failed to convert the value(%s) of env var |%s| to integer.", env_var_val, env_var_name, err)
	}
	if ret < 0 {
		log.Fatal("The value(%s) of env var |%s| cannot be negative", env_var_val, env_var_name)
	}
	return ret
}

// A function to create a saw script, replace `placeholder_key` with value, and then execute the script.
func CreateAndRunSawScript(path_to_template string, placeholder_key string, value int, wg *sync.WaitGroup) {
	log.Printf("Start creating saw script for target value %s based on template %s.", value, path_to_template)
	// Create a new saw script.
	file_name := fmt.Sprint(value, ".saw")
	file, err := os.Create(file_name)
	CheckError(err)
	// Read file content of verification template.
	content, err := ioutil.ReadFile(path_to_template)
	CheckError(err)
	verification_template := string(content)
	// Replace some placeholders of the file content with target values.
	text := strings.Replace(verification_template, placeholder_key, strconv.Itoa(value), 1)
	defer file.Close()
	file.WriteString(text)
	defer os.Remove(file_name)
	// Run saw script.
	defer wg.Done()
	RunSelectCheckScript(file_name, path_to_template)
}

// A function to run saw script.
func RunSelectCheckScript(path_to_saw_file string, path_to_template string) {
	log.Printf("Running saw script %s. Related template: %s.", path_to_saw_file, path_to_template)
	cmd := exec.Command("saw", path_to_saw_file)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	err := cmd.Run()
	if err != nil {
		log.Fatal("Failed to run saw script %s. Related template: %s.", path_to_saw_file, path_to_template, err)
	} else {
		log.Printf("Finished executing saw script %s. Related template: %s.", path_to_saw_file, path_to_template)
	}
}

func RunSawScript(path_to_saw_file string) {
	log.Printf("Running saw script %s.", path_to_saw_file)
	cmd := exec.Command("saw", path_to_saw_file)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	err := cmd.Run()
	if err != nil {
		log.Fatal("Failed to run saw script %s.", path_to_saw_file, err)
	} else {
		log.Printf("Finished executing saw script %s.", path_to_saw_file)
	}
}

// A function to limit number of concurrent processes.
func Wait(process_count *int, limit int, wg *sync.WaitGroup) {
	if *process_count >= limit {
		log.Printf("Count [%d] reached process limit [%d].", *process_count, limit)
		wg.Wait()
		*process_count = 0
	} else {
		*process_count = (*process_count) + 1
	}
}

func SystemMemory() uint64 {
	info := &syscall.Sysinfo_t{}
	err := syscall.Sysinfo(info)
	if err != nil {
		return 0
	}
	return uint64(info.Totalram) * uint64(info.Unit)
}
