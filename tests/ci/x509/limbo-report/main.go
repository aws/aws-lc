// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"strings"
)

func init() {
	flag.Usage = printHelp
}

func printHelp() {
	var builder strings.Builder
	builder.WriteString("Usage:\n\n")
	builder.WriteString(annotateHelpDoc)
	builder.WriteRune('\n')
	builder.WriteString(diffHelp)
	builder.WriteRune('\n')
	fmt.Fprint(os.Stderr, builder.String())
	os.Exit(0)
}

func main() {
	flag.Parse()

	var err error
	arg := flag.Arg(0)
	switch {
	case strings.EqualFold("annotate", arg):
		err = runAnnotateCommand(flag.Args()[1:])
	case strings.EqualFold("diff", arg):
		err = runDiffCommand(flag.Args()[1:])
	case strings.EqualFold("help", arg):
		fallthrough
	default:
		printHelp()
		return
	}

	if err != nil {
		log.Fatal(err)
	}
}
