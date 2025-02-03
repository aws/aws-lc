// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"
	"sort"
	"strings"
)

var diffHelp string = `report diff <annotatedFile1> <annotatedFile2>

Provides a difference report between <annotatedFile1> and <annotatedFile2>. These files are expected to be in the
default json file format produced by invoking "report annotate".
`

var diffFlagSet = func() *flag.FlagSet {
	fs := flag.NewFlagSet("diff", flag.ExitOnError)
	fs.Usage = func() {
		fmt.Fprint(fs.Output(), diffHelp)
	}
	return fs
}()

func runDiffCommand(args []string) error {
	if err := diffFlagSet.Parse(args); err != nil {
		return err
	}

	if diffFlagSet.NArg() != 2 {
		return fmt.Errorf("expected two positional arguments containing paths to files to diff")
	}

	leftReportFilePath := diffFlagSet.Arg(0)
	rightReportFilePath := diffFlagSet.Arg(1)

	leftReport, err := os.Open(leftReportFilePath)
	if err != nil {
		return fmt.Errorf("failed to read %s: %w", leftReportFilePath, err)
	}
	defer leftReport.Close()

	rightReport, err := os.Open(rightReportFilePath)
	if err != nil {
		return fmt.Errorf("failed to read %s: %w", rightReportFilePath, err)
	}
	defer rightReport.Close()

	var leftResults, rightResults HarnessResults

	leftDecoder := json.NewDecoder(leftReport)
	rightDecoder := json.NewDecoder(rightReport)

	if err := leftDecoder.Decode(&leftResults); err != nil {
		return fmt.Errorf("failed to decode left report: %w", err)
	}

	if err := rightDecoder.Decode(&rightResults); err != nil {
		return fmt.Errorf("failed to decode right report: %w", err)
	}

	diff, err := diffReports(&leftResults, &rightResults)
	if err != nil {
		return err
	}

	if err := diff.Render(os.Stdout); err != nil {
		return err
	}

	if diff.NeedsAttention() {
		os.Exit(1)
	}

	return nil
}

func diffReports(left, right *HarnessResults) (diff Diff, err error) {
	var sortedLeftIds []string
	var sortedRightIds []string

	for id := range left.Results {
		sortedLeftIds = append(sortedLeftIds, id)
	}
	sort.Strings(sortedLeftIds)

	for id := range right.Results {
		sortedRightIds = append(sortedRightIds, id)
	}
	sort.Strings(sortedRightIds)

	exclusiveLeftIds, commonIds, exclusiveRightIds := intersection(sortedLeftIds, sortedRightIds)

	removed := make(map[Judgement][]string)
	added := make(map[Judgement][]string)

	for _, id := range exclusiveLeftIds {
		tc := left.Results[id]
		slice := removed[tc.Judgement]
		slice = append(slice, id)
		removed[tc.Judgement] = slice
	}

	for _, id := range exclusiveRightIds {
		tc := right.Results[id]
		slice := added[tc.Judgement]
		slice = append(slice, id)
		added[tc.Judgement] = slice
	}

	changed := make(map[Judgement][]ChangedResult)
	unchanged := make(map[Judgement][]string)

	for _, id := range commonIds {
		leftTc := left.Results[id]
		rightTc := right.Results[id]

		if leftTc.Judgement == rightTc.Judgement {
			slice := unchanged[rightTc.Judgement]
			slice = append(slice, id)
			unchanged[rightTc.Judgement] = slice
		} else {
			slice := changed[rightTc.Judgement]
			slice = append(slice, ChangedResult{
				ID:  id,
				Was: leftTc.Judgement,
			})
			changed[rightTc.Judgement] = slice
		}
	}

	return Diff{
		Removed:   removed,
		Added:     added,
		Changed:   changed,
		Unchanged: unchanged,
	}, nil
}

type ChangedResult struct {
	ID  string
	Was Judgement
}

type Diff struct {
	Removed map[Judgement][]string

	Added map[Judgement][]string

	Changed map[Judgement][]ChangedResult

	Unchanged map[Judgement][]string
}

func (diff *Diff) TotalAdded() (count int) {
	for i := range diff.Added {
		count += len(diff.Added[i])
	}
	return count
}

func (diff *Diff) TotalRemoved() (count int) {
	for i := range diff.Removed {
		count += len(diff.Removed[i])
	}
	return count
}

func (diff *Diff) TotalChanged() (count int) {
	for i := range diff.Changed {
		count += len(diff.Changed[i])
	}
	return count
}

func (diff *Diff) TotalUnchanged() (count int) {
	for i := range diff.Unchanged {
		count += len(diff.Unchanged[i])
	}
	return count
}

func (diff *Diff) Total() int {
	return diff.TotalAdded() + diff.TotalChanged() + diff.TotalUnchanged()
}

func (diff *Diff) NeedsAttention() bool {
	return len(diff.Added[unexpectedFailureJudgement]) > 0 || len(diff.Added[unexpectedPassJudgement]) > 0 ||
		len(diff.Changed[unexpectedFailureJudgement]) > 0 || len(diff.Changed[unexpectedPassJudgement]) > 0
}

func (diff *Diff) Render(out io.Writer) (err error) {
	writer := bufio.NewWriter(out)
	defer func() {
		closeErr := writer.Flush()
		if err == nil {
			err = closeErr
		} else if closeErr != nil {
			err = fmt.Errorf("close err: %v, original error: %w", closeErr, err)
		}
	}()

	totalAdded := diff.TotalAdded()
	totalRemoved := diff.TotalRemoved()
	totalChanged := diff.TotalChanged()

	judgements := Judgements()

	var unchangedSummary strings.Builder
	for i, judge := range judgements {
		unchangedSummary.WriteString(fmt.Sprintf("%s: %d", judge, len(diff.Added[judge])+len(diff.Unchanged[judge])+len(diff.Changed[judge])))
		if i != len(judgements)-1 {
			unchangedSummary.WriteString(", ")
		}
	}

	writer.WriteString(fmt.Sprintf(`%s

Report Breakdown:
	%d added
	%d removed
	%d changed
	%d unchanged

`, unchangedSummary.String(), totalAdded, totalRemoved, totalChanged, diff.TotalUnchanged()))

	if totalAdded > 0 {
		for _, judge := range judgements {
			if _, ok := diff.Added[judge]; !ok {
				continue
			}
			writer.WriteString(fmt.Sprintf("Added %s:\n", judge))
			for _, id := range diff.Added[judge] {
				writer.WriteString(fmt.Sprintf("\t%s\n", id))
			}
			writer.WriteByte('\n')
		}
		writer.WriteByte('\n')
	}

	if totalRemoved > 0 {
		for _, judge := range judgements {
			if _, ok := diff.Removed[judge]; !ok {
				continue
			}
			writer.WriteString(fmt.Sprintf("Removed %s:\n", judge))
			for _, id := range diff.Removed[judge] {
				writer.WriteString(fmt.Sprintf("\t%s\n", id))
			}
			writer.WriteByte('\n')
		}
		writer.WriteByte('\n')
	}

	if totalChanged > 0 {
		for _, judge := range judgements {
			if _, ok := diff.Changed[judge]; !ok {
				continue
			}
			writer.WriteString(fmt.Sprintf("Changed to %s:\n", judge))
			for _, result := range diff.Changed[judge] {
				writer.WriteString(fmt.Sprintf("\t%s (previously %s)\n", result.ID, result.Was))
			}
			writer.WriteByte('\n')
		}
		writer.WriteByte('\n')
	}

	return nil
}

// intersection computes the set intersection of two string slice left and right.
// This expect left and right to have already been sorted, and will return `aAndB` sorted.
func intersection(left, right []string) (a, aAndB, b []string) {
	aAndBDedupe := make(map[string]struct{})

	for _, v := range left {
		if isInSlice(right, v) {
			aAndBDedupe[v] = struct{}{}
		} else {
			a = append(a, v)
		}
	}

	for _, v := range right {
		if isInSlice(left, v) {
			aAndBDedupe[v] = struct{}{}
		} else {
			b = append(b, v)
		}
	}

	for v := range aAndBDedupe {
		aAndB = append(aAndB, v)
	}
	sort.Strings(aAndB)

	return a, aAndB, b
}

func isInSlice(slice []string, value string) bool {
	i := sort.SearchStrings(slice, value)
	return i < len(slice) && value == slice[i]
}
