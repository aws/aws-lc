// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package ssl_transfer

import (
	"bufio"
	"errors"
	"fmt"
	"os"
	"sort"
	"strings"
)

// Bssl has 7k runner tests. These tests can be reused to test SSL
// transfer(encode and decode SSL) by performing some conversion(e.g.
// enable flag |-ssl-transfer| in the test case). However, not all tests
// are eligible for the conversion.
//
// TestHelper helps
// 1. identify which test case can be converted to test SSL transfer.
// 2. collect new test case that should be converted to test SSL transfer.
type TestHelper struct {
	// An absolute path to a test file, which includes
	// test case names that can be converted to test SSL transfer.
	abs_test_file string
	// A mapping from test case name to the counter.
	// The keys of |test_case_names| come from |abs_test_file|.
	test_case_names map[string]int
	// A mapping from test case name to the counter.
	// The keys of |new_test_case_names| are collected by |bssl_shim| during runtime.
	new_test_case_names map[string]int
}

func NewTestHelper(test_file string) *TestHelper {
	// Read test cases from |test_file|.
	file, err := os.Open(test_file)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Failed to create TestHelper. Err: %s.\n", err)
		os.Exit(1)
	}
	scanner := bufio.NewScanner(file)
	scanner.Split(bufio.ScanLines)
	var test_cases []string
	for scanner.Scan() {
		test_cases = append(test_cases, scanner.Text())
	}
	defer file.Close()
	// Construct |TestHelper|.
	var ret = new(TestHelper)
	ret.test_case_names = make(map[string]int)
	ret.new_test_case_names = make(map[string]int)
	for _, test_case := range test_cases {
		ret.test_case_names[test_case] = 0
	}
	ret.abs_test_file = test_file
	return ret
}

// CanBeTransfer tells if |test_case_name| can be converted to test SSL transfer.
func (helper *TestHelper) CanBeTransfer(test_case_name string) bool {
	val, ok := helper.test_case_names[test_case_name]
	if ok {
		helper.test_case_names[test_case_name] = val + 1
	}
	return ok
}

// AddNewCase collects new test case that should be converted to test SSL transfer.
func (helper *TestHelper) AddNewCase(test_case_name string) {
	val, ok := helper.new_test_case_names[test_case_name]
	if ok {
		helper.new_test_case_names[test_case_name] = val + 1
	} else {
		helper.new_test_case_names[test_case_name] = 1
	}
}

func (helper *TestHelper) CheckTestCases() {
	// Validate and collect new test cases.
	var err_msgs []string
	var test_cases []string
	for k, v := range helper.new_test_case_names {
		is_valid := true
		// Each new test case should be added only once.
		if v != 1 {
			err_msgs = append(err_msgs, fmt.Sprintf("New test case '%s' was added %d times.", k, v))
			is_valid = false
		}
		// Each new test case should not exist in |test_case_names|.
		if _, ok := helper.test_case_names[k]; ok {
			err_msgs = append(err_msgs, fmt.Sprintf("The new test case '%s' already exists.", k))
			is_valid = false
		}
		if is_valid {
			test_cases = append(test_cases, k)
		}
	}
	// Validate and collect existing test cases.
	var pre_test_cases []string
	for k, v := range helper.test_case_names {
		// Each test case should be used once.
		// If zero, that means the test case name may get removed or renamed.
		if v == 1 {
			test_cases = append(test_cases, k)
		}
		if v > 1 {
			err_msgs = append(err_msgs, fmt.Sprintf("Test case %s might be transferred %d times.", k, v))
		}
		pre_test_cases = append(pre_test_cases, k)
	}
	if len(err_msgs) != 0 {
		fmt.Fprintf(os.Stderr, "Failed to generate new ssl transfer test file.\n")
		fmt.Fprintf(os.Stderr, strings.Join(err_msgs[:], "\n"))
		os.Exit(1)
	}
	// Generate new |helper.abs_test_file|.
	sort.Strings(test_cases)
	sort.Strings(pre_test_cases)
	isTheSame := len(test_cases) == len(pre_test_cases)
	if isTheSame {
		for i := 0; i < len(test_cases); i++ {
			if test_cases[i] != pre_test_cases[i] {
				isTheSame = false
				break
			}
		}
	}
	if isTheSame {
		return
	}
	fmt.Fprintf(os.Stderr, "New vs old. D1 %d and D2 %d.\n", len(test_cases), len(pre_test_cases))
	// If the test cases get updated(deleted, added or modified), generate new helper.abs_test_file.
	if _, err := os.Stat(helper.abs_test_file); err == nil {
		tmp_err := os.Remove(helper.abs_test_file)
		if tmp_err != nil {
			fmt.Fprintf(os.Stderr, "Failed to remove %s. Err %s.\n", helper.abs_test_file, tmp_err)
			os.Exit(1)
		}
	} else if !errors.Is(err, os.ErrNotExist) {
		fmt.Fprintf(os.Stderr, "Unknown error happened. Err %s.\n", err)
		os.Exit(1)
	}
	file, err := os.Create(helper.abs_test_file)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Failed to generate new ssl transfer test file. Err: %s.\n", err)
		os.Exit(1)
	}
	defer file.Close()
	w := bufio.NewWriter(file)
	for _, test_case := range test_cases {
		fmt.Fprintln(w, test_case)
	}
	w.Flush()
	fmt.Fprintf(os.Stderr, "New ssl transfer configure file is generated. Please commit the change of file '%s'.\n", helper.abs_test_file)
	os.Exit(1)
}
