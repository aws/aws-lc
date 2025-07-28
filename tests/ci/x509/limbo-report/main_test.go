// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"strings"
	"testing"

	"github.com/google/go-cmp/cmp"
)

func TestAnnotateHarnessResult(t *testing.T) {
	cases := []struct {
		Results     []byte
		Limbo       []byte
		Expected    HarnessResults
		ExpectedErr string
	}{
		{
			Results: []byte(`{
	"harness": "stub",
	"results": [
			{
				"actual_result": "SUCCESS",
				"id": "expected_pass"
			},
			{
				"actual_result": "FAILURE",
				"context": "the reason",
				"id": "expected_failure"
			},
			{
				"actual_result": "SKIPPED",
				"id": "skipped_expected_success"
			},
			{
				"actual_result": "SKIPPED",
				"id": "skipped_expected_failure"
			},
			{
				"actual_result": "SUCCESS",
				"id": "unexpected_pass"
			},
			{
				"actual_result": "FAILURE",
				"context": "the unexpected reason",
				"id": "unexpected_failure"
			}
	]
}`),
			Limbo: []byte(`{
	"version": 1,
	"testcases": [
		{
			"expected_result": "SUCCESS",
			"id": "expected_pass",
			"description": "this has a description"
		},
		{
			"expected_result": "FAILURE",
			"id": "expected_failure"
		},
		{
			"expected_result": "SUCCESS",
			"id": "skipped_expected_success"
		},
		{
			"expected_result": "FAILURE",
			"id": "skipped_expected_failure"
		},
		{
			"expected_result": "FAILURE",
			"id": "unexpected_pass"
		},
		{
			"expected_result": "SUCCESS",
			"id": "unexpected_failure"
		}
	]
}`),
			Expected: HarnessResults{
				Harness: "stub",
				Results: map[string]AnnotatedTestCaseResult{
					"expected_pass": {
						TestCaseResult: TestCaseResult{
							ActualResult: successResult,
							ID:           "expected_pass",
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
						Description:    "this has a description",
					},
					"expected_failure": {
						TestCaseResult: TestCaseResult{
							ActualResult: failureResult,
							Context:      "the reason",
							ID:           "expected_failure",
						},
						ExpectedResult: failureResult,
						Judgement:      passJudgement,
					},
					"skipped_expected_success": {
						TestCaseResult: TestCaseResult{
							ActualResult: skippedResult,
							ID:           "skipped_expected_success",
						},
						ExpectedResult: successResult,
						Judgement:      skippedJudgement,
					},
					"skipped_expected_failure": {
						TestCaseResult: TestCaseResult{
							ActualResult: skippedResult,
							ID:           "skipped_expected_failure",
						},
						ExpectedResult: failureResult,
						Judgement:      skippedJudgement,
					},
					"unexpected_pass": {
						TestCaseResult: TestCaseResult{
							ActualResult: successResult,
							ID:           "unexpected_pass",
						},
						ExpectedResult: failureResult,
						Judgement:      unexpectedPassJudgement,
					},
					"unexpected_failure": {
						TestCaseResult: TestCaseResult{
							ActualResult: failureResult,
							Context:      "the unexpected reason",
							ID:           "unexpected_failure",
						},
						ExpectedResult: successResult,
						Judgement:      unexpectedFailureJudgement,
					},
				},
			},
		},
		{
			Limbo: []byte(`{
	"version": 1,
	"testcases": [
		{
			"id": "bad_expected_result",
			"expected_result": "biz"
		}
	]
}`),
			Results:     []byte(`{}`),
			ExpectedErr: "unknown result value: biz",
		},
		{
			Limbo: []byte(`{
	"version": 1,
	"testcases": [
		{
			"id": "bad_expected_result",
			"expected_result": "SUCCESS"
		}
	]
}`),
			Results: []byte(`{
	"harness": "stub",
	"results": [
		{
			"id": "bad_actual_result",
			"actual_result": "biz"
		}
	]
}`),
			ExpectedErr: "unknown result value: biz",
		},
		{
			Limbo: []byte(`{
	"version": 1,
	"testcases": [
		{
			"id": "mot_missing_id",
			"expected_result": "FAILURE"
		}
	]
}`),
			Results: []byte(`{
	"harness": "stub",
	"results": [
		{
			"id": "missing_id",
			"actual_result": "SUCCESS"
		}
	]
}`),
			ExpectedErr: "missing test case descriptor: missing_id",
		},
	}

	for i, tc := range cases {
		t.Run(fmt.Sprint(i), func(t *testing.T) {
			var limbo Limbo
			if err := json.Unmarshal(tc.Limbo, &limbo); err != nil {
				if len(tc.ExpectedErr) == 0 {
					t.Fatalf("unexpected err: %v", err)
				} else if !strings.Contains(err.Error(), tc.ExpectedErr) {
					t.Fatalf("err didn't contain expected string, wanted %v, got %v", tc.ExpectedErr, err)
				} else {
					return
				}
			}

			var harness HarnessResults
			if err := json.Unmarshal(tc.Results, &harness); err != nil {
				if len(tc.ExpectedErr) == 0 {
					t.Fatalf("unexpected err: %v", err)
				} else if !strings.Contains(err.Error(), tc.ExpectedErr) {
					t.Fatalf("err didn't contain expected string, wanted %v, got %v", tc.ExpectedErr, err)
				} else {
					return
				}
			}

			if err := harness.Annotate(&limbo); err != nil {
				if len(tc.ExpectedErr) == 0 {
					t.Fatalf("unexpected err: %v", err)
				} else if !strings.Contains(err.Error(), tc.ExpectedErr) {
					t.Fatalf("err didn't contain expected string, wanted %v, got %v", tc.ExpectedErr, err)
				} else {
					return
				}
			}

			if diff := cmp.Diff(&harness, &tc.Expected); len(diff) > 0 {
				t.Fatal(diff)
			}
		})
	}
}

func TestDiff(t *testing.T) {
	cases := []struct {
		ResultsBefore          HarnessResults
		ResultsAfter           HarnessResults
		Expected               Diff
		ExpectedTotal          int
		ExpectedTotalRemoved   int
		ExpectedTotalAdded     int
		ExpectedTotalChanged   int
		ExpectedTotalUnchanged int
	}{
		{
			ResultsBefore: HarnessResults{
				Results: TestCaseResultMap{
					"left_pass": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "left_pass",
							ActualResult: successResult,
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
					},
					"left_skipped": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "left_skipped",
							ActualResult: skippedResult,
						},
						ExpectedResult: failureResult,
						Judgement:      skippedJudgement,
					},
					"left_expect_fail": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "left_expect_fail",
							ActualResult: successResult,
						},
						ExpectedResult: failureResult,
						Judgement:      unexpectedPassJudgement,
					},
					"left_expect_pass": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "left_expect_pass",
							ActualResult: failureResult,
						},
						ExpectedResult: successResult,
						Judgement:      unexpectedFailureJudgement,
					},
				},
			},
			ResultsAfter: HarnessResults{},
			Expected: Diff{
				Removed: map[Judgement][]string{
					passJudgement:              {"left_pass"},
					skippedJudgement:           {"left_skipped"},
					unexpectedFailureJudgement: {"left_expect_pass"},
					unexpectedPassJudgement:    {"left_expect_fail"},
				},
				Added:     map[Judgement][]string{},
				Changed:   map[Judgement][]ChangedResult{},
				Unchanged: map[Judgement][]string{},
			},
			ExpectedTotalRemoved: 4,
		},
		{
			ResultsBefore: HarnessResults{},
			ResultsAfter: HarnessResults{
				Results: TestCaseResultMap{
					"right_pass": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "right_pass",
							ActualResult: successResult,
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
					},
					"right_skipped": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "right_skipped",
							ActualResult: skippedResult,
						},
						ExpectedResult: failureResult,
						Judgement:      skippedJudgement,
					},
					"right_expect_fail": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "right_expect_fail",
							ActualResult: successResult,
						},
						ExpectedResult: failureResult,
						Judgement:      unexpectedPassJudgement,
					},
					"right_expect_pass": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "right_expect_pass",
							ActualResult: failureResult,
						},
						ExpectedResult: successResult,
						Judgement:      unexpectedFailureJudgement,
					},
				},
			},
			Expected: Diff{
				Removed: map[Judgement][]string{},
				Added: map[Judgement][]string{
					passJudgement:              {"right_pass"},
					skippedJudgement:           {"right_skipped"},
					unexpectedFailureJudgement: {"right_expect_pass"},
					unexpectedPassJudgement:    {"right_expect_fail"},
				},
				Changed:   map[Judgement][]ChangedResult{},
				Unchanged: map[Judgement][]string{},
			},
			ExpectedTotal:      4,
			ExpectedTotalAdded: 4,
		},
		{
			ResultsBefore: HarnessResults{
				Results: TestCaseResultMap{
					"both_pass": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "both_pass",
							ActualResult: successResult,
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
					},
					"both_skipped": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "both_skipped",
							ActualResult: skippedResult,
						},
						ExpectedResult: failureResult,
						Judgement:      skippedJudgement,
					},
					"both_expect_fail": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "both_expect_fail",
							ActualResult: successResult,
						},
						ExpectedResult: failureResult,
						Judgement:      unexpectedPassJudgement,
					},
					"both_expect_pass": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "both_expect_pass",
							ActualResult: failureResult,
						},
						ExpectedResult: successResult,
						Judgement:      unexpectedFailureJudgement,
					},
				},
			},
			ResultsAfter: HarnessResults{
				Results: TestCaseResultMap{
					"both_pass": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "both_pass",
							ActualResult: successResult,
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
					},
					"both_skipped": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "both_skipped",
							ActualResult: skippedResult,
						},
						ExpectedResult: failureResult,
						Judgement:      skippedJudgement,
					},
					"both_expect_fail": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "both_expect_fail",
							ActualResult: successResult,
						},
						ExpectedResult: failureResult,
						Judgement:      unexpectedPassJudgement,
					},
					"both_expect_pass": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "both_expect_pass",
							ActualResult: failureResult,
						},
						ExpectedResult: successResult,
						Judgement:      unexpectedFailureJudgement,
					},
				},
			},
			Expected: Diff{
				Removed: map[Judgement][]string{},
				Added:   map[Judgement][]string{},
				Changed: map[Judgement][]ChangedResult{},
				Unchanged: map[Judgement][]string{
					passJudgement:              {"both_pass"},
					skippedJudgement:           {"both_skipped"},
					unexpectedFailureJudgement: {"both_expect_pass"},
					unexpectedPassJudgement:    {"both_expect_fail"},
				},
			},
			ExpectedTotal:          4,
			ExpectedTotalUnchanged: 4,
		},
		{
			ResultsBefore: HarnessResults{
				Results: TestCaseResultMap{
					"changed1": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed1",
							ActualResult: successResult,
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
					},
					"changed2": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed2",
							ActualResult: skippedResult,
						},
						ExpectedResult: failureResult,
						Judgement:      skippedJudgement,
					},
					"changed3": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed3",
							ActualResult: successResult,
						},
						ExpectedResult: failureResult,
						Judgement:      unexpectedPassJudgement,
					},
					"changed4": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed4",
							ActualResult: failureResult,
						},
						ExpectedResult: successResult,
						Judgement:      unexpectedFailureJudgement,
					},
				},
			},
			ResultsAfter: HarnessResults{
				Results: TestCaseResultMap{
					"changed1": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed1",
							ActualResult: failureResult,
						},
						ExpectedResult: successResult,
						Judgement:      unexpectedFailureJudgement,
					},
					"changed2": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed2",
							ActualResult: successResult,
						},
						ExpectedResult: failureResult,
						Judgement:      unexpectedPassJudgement,
					},
					"changed3": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed3",
							ActualResult: failureResult,
						},
						ExpectedResult: failureResult,
						Judgement:      passJudgement,
					},
					"changed4": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed4",
							ActualResult: skippedResult,
						},
						ExpectedResult: successResult,
						Judgement:      skippedJudgement,
					},
				},
			},
			Expected: Diff{
				Removed: map[Judgement][]string{},
				Added:   map[Judgement][]string{},
				Changed: map[Judgement][]ChangedResult{
					passJudgement:              {{ID: "changed3", Was: "UNEXPECTED_PASS"}},
					skippedJudgement:           {{ID: "changed4", Was: "UNEXPECTED_FAILURE"}},
					unexpectedFailureJudgement: {{ID: "changed1", Was: "PASS"}},
					unexpectedPassJudgement:    {{ID: "changed2", Was: "SKIPPED"}},
				},
				Unchanged: map[Judgement][]string{},
			},
			ExpectedTotal:        4,
			ExpectedTotalChanged: 4,
		},
		{
			ResultsBefore: HarnessResults{
				Results: TestCaseResultMap{
					"before1": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "before1",
							ActualResult: successResult,
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
					},
					"before2": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "before2",
							ActualResult: failureResult,
						},
						ExpectedResult: failureResult,
						Judgement:      passJudgement,
					},
					"same1": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "same1",
							ActualResult: successResult,
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
					},
					"same2": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "same2",
							ActualResult: failureResult,
						},
						ExpectedResult: failureResult,
						Judgement:      passJudgement,
					},
					"changed1": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed1",
							ActualResult: successResult,
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
					},
					"changed2": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed2",
							ActualResult: failureResult,
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
					},
				},
			},
			ResultsAfter: HarnessResults{
				Results: TestCaseResultMap{
					"same1": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "same1",
							ActualResult: successResult,
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
					},
					"same2": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "same2",
							ActualResult: failureResult,
						},
						ExpectedResult: failureResult,
						Judgement:      passJudgement,
					},
					"changed1": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed1",
							ActualResult: failureResult,
						},
						ExpectedResult: successResult,
						Judgement:      unexpectedFailureJudgement,
					},
					"changed2": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "changed2",
							ActualResult: successResult,
						},
						ExpectedResult: successResult,
						Judgement:      unexpectedFailureJudgement,
					},
					"new1": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "new1",
							ActualResult: successResult,
						},
						ExpectedResult: successResult,
						Judgement:      passJudgement,
					},
					"new2": AnnotatedTestCaseResult{
						TestCaseResult: TestCaseResult{
							ID:           "new2",
							ActualResult: failureResult,
						},
						ExpectedResult: failureResult,
						Judgement:      passJudgement,
					},
				},
			},
			Expected: Diff{
				Removed: map[Judgement][]string{
					passJudgement: {"before1", "before2"},
				},
				Added: map[Judgement][]string{
					passJudgement: {"new1", "new2"},
				},
				Changed: map[Judgement][]ChangedResult{
					unexpectedFailureJudgement: {{ID: "changed1", Was: "PASS"}, {ID: "changed2", Was: "PASS"}},
				},
				Unchanged: map[Judgement][]string{
					passJudgement: {"same1", "same2"},
				},
			},
			ExpectedTotal:          6,
			ExpectedTotalRemoved:   2,
			ExpectedTotalAdded:     2,
			ExpectedTotalChanged:   2,
			ExpectedTotalUnchanged: 2,
		},
	}

	for i, tc := range cases {
		t.Run(fmt.Sprintf("%d", i), func(t *testing.T) {
			diff, err := diffReports(&tc.ResultsBefore, &tc.ResultsAfter)
			if err != nil {
				t.Fatal(err)
			}
			if diff := cmp.Diff(tc.Expected, diff); len(diff) > 0 {
				t.Error(diff)
			}
			if diff := cmp.Diff(diff.Total(), tc.ExpectedTotal); len(diff) > 0 {
				t.Error(diff)
			}
			if diff := cmp.Diff(diff.TotalRemoved(), tc.ExpectedTotalRemoved); len(diff) > 0 {
				t.Error(diff)
			}
			if diff := cmp.Diff(diff.TotalAdded(), tc.ExpectedTotalAdded); len(diff) > 0 {
				t.Error(diff)
			}
			if diff := cmp.Diff(diff.TotalChanged(), tc.ExpectedTotalChanged); len(diff) > 0 {
				t.Error(diff)
			}
			if diff := cmp.Diff(diff.TotalUnchanged(), tc.ExpectedTotalUnchanged); len(diff) > 0 {
				t.Error(diff)
			}
		})
	}
}

func TestIntersection(t *testing.T) {
	cases := []struct {
		Left        []string
		Right       []string
		ExpectLeft  []string
		ExpectBoth  []string
		ExpectRight []string
	}{
		{
			Left:       []string{"left"},
			ExpectLeft: []string{"left"},
		},
		{
			Right:       []string{"right"},
			ExpectRight: []string{"right"},
		},
		{
			Left:        []string{"left"},
			Right:       []string{"right"},
			ExpectLeft:  []string{"left"},
			ExpectRight: []string{"right"},
		},
		{
			Left:       []string{"both"},
			Right:      []string{"both"},
			ExpectBoth: []string{"both"},
		},
		{
			Left:        []string{"both", "left"},
			Right:       []string{"both", "right"},
			ExpectLeft:  []string{"left"},
			ExpectBoth:  []string{"both"},
			ExpectRight: []string{"right"},
		},
	}

	for i, tc := range cases {
		t.Run(fmt.Sprintf("%d", i), func(t *testing.T) {
			left, inter, right := intersection(tc.Left, tc.Right)
			if diff := cmp.Diff(tc.ExpectLeft, left); len(diff) > 0 {
				t.Error(diff)
			}
			if diff := cmp.Diff(tc.ExpectBoth, inter); len(diff) > 0 {
				t.Error(diff)
			}
			if diff := cmp.Diff(tc.ExpectRight, right); len(diff) > 0 {
				t.Error(diff)
			}
		})
	}
}

func TestDiffNeedsAttention(t *testing.T) {
	cases := []struct {
		Diff   Diff
		Expect bool
	}{
		{
			Diff: Diff{
				Removed: map[Judgement][]string{
					skippedJudgement: {"skipped"},
				},
				Added: map[Judgement][]string{
					passJudgement:    {"added_pass"},
					skippedJudgement: {"added_skipped"},
				},
				Changed: map[Judgement][]ChangedResult{
					skippedJudgement: {
						{
							ID:  "changed_skipped",
							Was: passJudgement,
						},
					},
					passJudgement: {
						{
							ID:  "changed_passed",
							Was: unexpectedFailureJudgement,
						},
					},
				},
				Unchanged: map[Judgement][]string{
					skippedJudgement:           {"unchanged_skipped"},
					passJudgement:              {"unchanged_pass"},
					unexpectedFailureJudgement: {"unchanged_failure1"},
					unexpectedPassJudgement:    {"unchanged_failure2"},
				},
			},
			Expect: false,
		},
		{
			Diff: Diff{
				Removed: map[Judgement][]string{},
				Added: map[Judgement][]string{
					unexpectedFailureJudgement: {"failure"},
				},
				Changed:   map[Judgement][]ChangedResult{},
				Unchanged: map[Judgement][]string{},
			},
			Expect: true,
		},
		{
			Diff: Diff{
				Removed: map[Judgement][]string{},
				Added: map[Judgement][]string{
					unexpectedPassJudgement: {"failure"},
				},
				Changed:   map[Judgement][]ChangedResult{},
				Unchanged: map[Judgement][]string{},
			},
			Expect: true,
		},
		{
			Diff: Diff{
				Removed: map[Judgement][]string{},
				Added:   map[Judgement][]string{},
				Changed: map[Judgement][]ChangedResult{
					unexpectedFailureJudgement: {{
						ID:  "failure",
						Was: passJudgement,
					}},
				},
				Unchanged: map[Judgement][]string{},
			},
			Expect: true,
		},
		{
			Diff: Diff{
				Removed: map[Judgement][]string{},
				Added:   map[Judgement][]string{},
				Changed: map[Judgement][]ChangedResult{
					unexpectedPassJudgement: {{
						ID:  "failure",
						Was: passJudgement,
					}},
				},
				Unchanged: map[Judgement][]string{},
			},
			Expect: true,
		},
	}

	for i, tc := range cases {
		t.Run(fmt.Sprint(i), func(t *testing.T) {
			if got := tc.Diff.NeedsAttention(); tc.Expect != got {
				t.Fatalf("expected %v, got %v", tc.Expect, got)
			}
		})
	}
}

func TestRenderDiff(t *testing.T) {
	cases := []struct {
		Diff   Diff
		Expect string
	}{
		{
			Diff: Diff{
				Removed: map[Judgement][]string{
					skippedJudgement: {"skipped"},
				},
				Added: map[Judgement][]string{
					passJudgement:    {"added_pass"},
					skippedJudgement: {"added_skipped"},
				},
				Changed: map[Judgement][]ChangedResult{
					skippedJudgement: {
						{
							ID:  "changed_skipped",
							Was: passJudgement,
						},
					},
					passJudgement: {
						{
							ID:  "changed_passed",
							Was: unexpectedFailureJudgement,
						},
					},
				},
				Unchanged: map[Judgement][]string{
					skippedJudgement:           {"unchanged_skipped"},
					passJudgement:              {"unchanged_pass"},
					unexpectedFailureJudgement: {"unchanged_failure1"},
					unexpectedPassJudgement:    {"unchanged_failure2"},
				},
			},
			Expect: `PASS: 3, SKIPPED: 3, UNEXPECTED_FAILURE: 1, UNEXPECTED_PASS: 1

Report Breakdown:
	2 added
	1 removed
	2 changed
	4 unchanged

Added PASS:
	added_pass

Added SKIPPED:
	added_skipped


Removed SKIPPED:
	skipped


Changed to PASS:
	changed_passed (previously UNEXPECTED_FAILURE)

Changed to SKIPPED:
	changed_skipped (previously PASS)


`,
		},
		{
			Diff: Diff{
				Removed: map[Judgement][]string{},
				Added:   map[Judgement][]string{},
				Changed: map[Judgement][]ChangedResult{},
				Unchanged: map[Judgement][]string{
					skippedJudgement:           {"unchanged_skipped"},
					passJudgement:              {"unchanged_pass"},
					unexpectedFailureJudgement: {"unchanged_failure1"},
					unexpectedPassJudgement:    {"unchanged_failure2"},
				},
			},
			Expect: `PASS: 1, SKIPPED: 1, UNEXPECTED_FAILURE: 1, UNEXPECTED_PASS: 1

Report Breakdown:
	0 added
	0 removed
	0 changed
	4 unchanged

`,
		},
	}

	for i, tc := range cases {
		t.Run(fmt.Sprint(i), func(t *testing.T) {
			buffer := bytes.NewBuffer(nil)
			if err := tc.Diff.Render(buffer); err != nil {
				t.Fatal(err)
			}
			if diff := cmp.Diff(tc.Expect, buffer.String()); len(diff) > 0 {
				t.Fatal(diff)
			}
		})
	}
}
