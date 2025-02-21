// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package main

import (
	"encoding/json"
	"fmt"
	"sort"
	"strings"
)

type Result string

func (r *Result) FromString(value string) error {
	if r == nil {
		return fmt.Errorf("unexpected nil: %T", r)
	}

	var result Result

	switch {
	case strings.EqualFold(string(skippedResult), value):
		result = skippedResult
	case strings.EqualFold(string(successResult), value):
		result = successResult
	case strings.EqualFold(string(failureResult), value):
		result = failureResult
	default:
		return fmt.Errorf("unknown result value: %v", value)
	}

	*r = result

	return nil
}

func (r *Result) UnmarshalJSON(bytes []byte) error {
	if r == nil {
		return fmt.Errorf("unexpected json unmarshal into nil: %T", r)
	}

	var str string

	if err := json.Unmarshal(bytes, &str); err != nil {
		return err
	}

	if err := r.FromString(str); err != nil {
		return err
	}

	return nil
}

const (
	skippedResult Result = "SKIPPED"
	successResult Result = "SUCCESS"
	failureResult Result = "FAILURE"
)

type Judgement string

func (j *Judgement) FromString(value string) error {
	if j == nil {
		return fmt.Errorf("unexpected nil: %T", j)
	}

	var judgement Judgement

	switch {
	case strings.EqualFold(string(skippedJudgement), value):
		judgement = (skippedJudgement)
	case strings.EqualFold(string(unexpectedFailureJudgement), value):
		judgement = (unexpectedFailureJudgement)
	case strings.EqualFold(string(unexpectedPassJudgement), value):
		judgement = (unexpectedPassJudgement)
	case strings.EqualFold(string(passJudgement), value):
		judgement = (passJudgement)
	default:
		return fmt.Errorf("unknown judgement value: %v", value)
	}

	*j = judgement

	return nil
}

func (j *Judgement) UnmarshalJSON(bytes []byte) error {
	if j == nil {
		return fmt.Errorf("unexpected json unmarshal into nil: %T", j)
	}

	var str string

	if err := json.Unmarshal(bytes, &str); err != nil {
		return err
	}

	if err := j.FromString(str); err != nil {
		return err
	}

	return nil
}

const (
	skippedJudgement           Judgement = "SKIPPED"
	unexpectedFailureJudgement Judgement = "UNEXPECTED_FAILURE"
	unexpectedPassJudgement    Judgement = "UNEXPECTED_PASS"
	passJudgement              Judgement = "PASS"
)

func Judgements() []Judgement {
	return []Judgement{passJudgement, skippedJudgement, unexpectedFailureJudgement, unexpectedPassJudgement}
}

type TestCaseMap map[string]TestCase

func (m *TestCaseMap) UnmarshalJSON(data []byte) error {
	var tc_slice []TestCase

	if err := json.Unmarshal(data, &tc_slice); err != nil {
		return err
	}

	if m == nil {
		return fmt.Errorf("unexpected nil: %T", m)
	}

	tc_map := make(TestCaseMap, len(tc_slice))

	for _, tc := range tc_slice {
		if _, ok := tc_map[tc.ID]; ok {
			return fmt.Errorf("duplicate test case id: %v", tc.ID)
		}
		tc_map[tc.ID] = tc
	}

	*m = tc_map

	return nil
}

type Limbo struct {
	Version   uint        `json:"version"`
	TestCases TestCaseMap `json:"testcases"`
}

type TestCase struct {
	ID             string `json:"id"`
	Description    string `json:"description"`
	ExpectedResult Result `json:"expected_result"`
}

type HarnessResults struct {
	Harness string            `json:"harness"`
	Results TestCaseResultMap `json:"results"`
}

// Annotate will use the provide Limbo test case descriptors to fill in the judgement fields on this harness result.
func (hr *HarnessResults) Annotate(limbo *Limbo) error {
	if limbo == nil {
		return fmt.Errorf("limbo data must not be nil")
	}

	for id := range hr.Results {
		tr := hr.Results[id]

		tc, ok := limbo.TestCases[id]
		if !ok {
			return fmt.Errorf("missing test case descriptor: %v", id)
		}

		judgement, err := getJudgement(tc.ExpectedResult, tr.ActualResult)
		if err != nil {
			return fmt.Errorf("unexpected result: (%v, %v)", tc.ExpectedResult, tr.ActualResult)
		}

		tr.Judgement = judgement
		tr.Description = tc.Description
		tr.ExpectedResult = tc.ExpectedResult

		hr.Results[id] = tr
	}

	return nil
}

type TestCaseResultMap map[string]AnnotatedTestCaseResult

func (m TestCaseResultMap) MarshalJSON() ([]byte, error) {
	if m == nil {
		return nil, fmt.Errorf("unexpected marshall of nil to json: %T", m)
	}

	var sortedIds []string

	for id, tc := range m {
		// This shouldn't happen if our unmarshal was correct, but sanity check
		if id != tc.ID {
			return nil, fmt.Errorf("unexpected id consistency during json marshal: %s != %s", id, tc.ID)
		}
		sortedIds = append(sortedIds, id)
	}
	sort.Strings(sortedIds)

	var slice []*AnnotatedTestCaseResult
	for _, id := range sortedIds {
		tc := m[id]
		slice = append(slice, &tc)
	}

	return json.Marshal(&slice)
}

func (m *TestCaseResultMap) UnmarshalJSON(data []byte) error {
	if m == nil {
		return fmt.Errorf("unexpected nil: %T", m)
	}

	var tc_slice []AnnotatedTestCaseResult

	if err := json.Unmarshal(data, &tc_slice); err != nil {
		return err
	}

	tc_map := make(TestCaseResultMap, len(tc_slice))

	for _, tc := range tc_slice {
		if _, ok := tc_map[tc.ID]; ok {
			return fmt.Errorf("duplicate test case id: %v", tc.ID)
		}
		tc_map[tc.ID] = tc
	}

	*m = tc_map

	return nil
}

type TestCaseResult struct {
	ID           string `json:"id"`
	ActualResult Result `json:"actual_result"`
	Context      string `json:"context"`
}

type AnnotatedTestCaseResult struct {
	TestCaseResult
	// These are additional fields we've annotated to the result.
	// This eliminates the need to later calculate or cross-reference from the limbo.json file.
	ExpectedResult Result    `json:"expected_result,omitempty"`
	Judgement      Judgement `json:"judgement,omitempty"`
	Description    string    `json:"description,omitempty"`
}

func getJudgement(expected, result Result) (judgement Judgement, err error) {
	if result == skippedResult {
		judgement = skippedJudgement
	} else if expected == result {
		judgement = passJudgement
	} else if expected == successResult && result == failureResult {
		judgement = unexpectedFailureJudgement
	} else if expected == failureResult && result == successResult {
		judgement = unexpectedPassJudgement
	} else {
		return "", fmt.Errorf("unexpected result: (%v, %v)", expected, result)
	}

	return judgement, nil
}
