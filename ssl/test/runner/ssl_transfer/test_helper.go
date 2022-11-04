// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package ssl_transfer

import (
	"bufio"
	"errors"
	"fmt"
	"os"
	"sort"
)

var EMPTY struct{}

// libssl runner has thousands tests. These tests can be converted to test SSL
// transfer(encode and decode SSL) by enabling |bssl_shim| flag |-ssl-transfer|.
// However, not all tests are eligible for the conversion due to the support
// scope of SSL transfer.
// Besides, libssl runner needs to know all tests(including the converted)
// so it can process these tests concurrently. Otherwise, it has to execute the
// tests in two sequential sync.WaitGroup.
//
// TestHelper is created to
// 1. collect the name of the tests that can be converted to test SSL transfer.
type TestHelper struct {
	// An absolute path to a test file, which includes
	// test case names that can be converted to test SSL transfer.
	// The content of this file will be refreshed if there are new eligible test case
	// or some existing test cases are no longer needed.
	abs_test_file string
	// A mapping which has test case name as key.
	// The keys of |test_case_names| come from |abs_test_file|.
	// The value is EMPTY.
	// golang does not have set struct.
	test_case_names map[string]struct{}
	// A channel to collect test cases new test case that should be converted to
	// test SSL transfer.
	// A channel(instead of map) is used because the test cases are executed by 
	// multiple goroutines.
	new_test_case_chann chan string
}

func NewTestHelper(test_file_path string, num_of_tests int) *TestHelper {
	// Read test cases from |test_file_path|.
	file, err := os.Open(test_file_path)
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
	ret.test_case_names = make(map[string]struct{})
	ret.new_test_case_chann = make(chan string, num_of_tests)
	for _, test_case := range test_cases {
		ret.test_case_names[test_case] = EMPTY
	}
	ret.abs_test_file = test_file_path
	return ret
}

// CanBeTransfer tells if |test_case_name| can be converted to test SSL transfer.
func (helper *TestHelper) CanBeTransfer(test_case_name string) bool {
	_, ok := helper.test_case_names[test_case_name]
	return ok
}

// AddNewCase collects new test case that should be converted to test SSL transfer.
func (helper *TestHelper) AddNewCase(test_case_name string) {
	helper.new_test_case_chann <- test_case_name
}

// mapToSortedArray converts the keys of |input_map| to a sorted array.
func mapToSortedArray(input_map map[string]struct{}) []string {
	ret := make([]string, 0, len(input_map))
	for k := range input_map {
		ret = append(ret, k)
	}
	sort.Strings(ret)
	return ret
}

// Refresh the content of |abs_test_file| when
// 1. the new test case should be converted to test SSL transfer.
// 2. some test cases are deleted or renamed.
func (helper *TestHelper) RefreshTestFileContent() {
	close(helper.new_test_case_chann)
	tmp_map := make(map[string]struct{})
	for new_test_case_name := range helper.new_test_case_chann {
		tmp_map[new_test_case_name] = EMPTY
	}
	new_test_cases := mapToSortedArray(tmp_map)
	pre_test_cases := mapToSortedArray(helper.test_case_names)
	// Check if there are updates in the test cases(e.g. name change, deletion and so on).
	isTheSame := len(new_test_cases) == len(pre_test_cases)
	if isTheSame {
		for i := 0; i < len(new_test_cases); i++ {
			if new_test_cases[i] != pre_test_cases[i] {
				isTheSame = false
				break
			}
		}
	}
	if isTheSame {
		return
	}
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
	for _, test_case := range new_test_cases {
		fmt.Fprintln(w, test_case)
	}
	w.Flush()
	fmt.Fprintf(os.Stderr, "New ssl transfer configure file is generated. Please commit the change of file '%s'.\n", helper.abs_test_file)
	os.Exit(1)
}
