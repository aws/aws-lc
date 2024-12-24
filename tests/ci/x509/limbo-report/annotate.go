// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package main

import (
	"encoding/csv"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"os"
	"sort"
)

var annotateHelpDoc string = `report annotate [-csv] <limboFile> <resultFile>

Annotates a standard x509-limbo results file with information from the provided <limboFile> test descriptors.
By default this will write the result back to the process standard output.

Options:
-csv Write the results to standard output in csv format rather then the default json format
`

var annotateCommand struct {
	formatAsCsv bool
}

var annotateFlagSet = func() *flag.FlagSet {
	fs := flag.NewFlagSet("annotate", flag.ExitOnError)
	fs.BoolVar(&annotateCommand.formatAsCsv, "csv", false, "format output as csv rather then the default")
	fs.Usage = func() {
		fmt.Fprint(fs.Output(), annotateHelpDoc)
	}

	return fs
}()

func runAnnotateCommand(args []string) error {
	if err := annotateFlagSet.Parse(args); err != nil {
		return err
	}

	if len(annotateFlagSet.Args()) != 2 {
		return fmt.Errorf("expect two positional arguments")
	}

	limbo, err := parseLimboFile(annotateFlagSet.Arg(0))
	if err != nil {
		return err
	}

	harnessFilePath := annotateFlagSet.Arg(1)
	harnessBytes, err := os.ReadFile(harnessFilePath)
	if err != nil {
		log.Fatalf("failed to read harnessFile(%v): %v", harnessFilePath, err)
	}

	var hr HarnessResults
	if err := json.Unmarshal(harnessBytes, &hr); err != nil {
		log.Fatalf("failed to parse json: %v", err)
	}
	if err := hr.Annotate(limbo); err != nil {
		return err
	}

	if annotateCommand.formatAsCsv {
		return writeCsvJudgementReport(&hr, os.Stdout)
	}

	return writeJsonJudgementReport(&hr, os.Stdout)
}

func parseLimboFile(filePath string) (limbo *Limbo, err error) {
	testCasesBytes, err := os.ReadFile(filePath)
	if err != nil {
		return limbo, fmt.Errorf("failed to read limbo test cases: %w", err)
	}

	var unmarshaled Limbo

	if err := json.Unmarshal(testCasesBytes, &unmarshaled); err != nil {
		return limbo, fmt.Errorf("failed to parse json: %w", err)
	}

	limbo = &unmarshaled

	return limbo, nil
}

func writeJsonJudgementReport(hr *HarnessResults, out io.Writer) error {
	jsonWriter := json.NewEncoder(out)
	jsonWriter.SetIndent("", " ")

	if err := jsonWriter.Encode(hr); err != nil {
		return fmt.Errorf("failed to encode harness judgement: %w", err)
	}

	return nil
}

func writeCsvJudgementReport(hr *HarnessResults, out io.Writer) error {
	csvWriter := csv.NewWriter(out)
	defer csvWriter.Flush()

	csvWriter.Write([]string{"id", "expected", "result", "judgement", "context"})

	// Normalize The Report for Diffing
	var sortedIds []string
	for id := range hr.Results {
		sortedIds = append(sortedIds, id)
	}
	sort.Strings(sortedIds)

	for _, id := range sortedIds {
		tr := hr.Results[id]
		csvWriter.Write([]string{id, string(tr.ExpectedResult), string(tr.ActualResult), string(tr.Judgement), tr.Context})
	}

	return nil
}
