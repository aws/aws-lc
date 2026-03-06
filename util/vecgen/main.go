package main

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
)

const (
	outputDir     = "gen"
	sourceName    = "github/aws/aws-lc"
	sourceVersion = "1.x"
)

// generateReproducibleSeed generates a reproducible seed of the specified length
func generateReproducibleSeed(length int) []byte {
	seed := make([]byte, length)
	// all-zeros
	return seed
}

func main() {
	fmt.Println("Generating test vectors...")

	// Create output directory
	err := os.MkdirAll(outputDir, 0755)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error creating output directory: %v\n", err)
		os.Exit(1)
	}

	// Generate ML-KEM vectors
	mlkemTestData := generateMLKEMDecapsVectors()

	// Create test files and write them
	for filename, testData := range mlkemTestData {
		// Create test file structure
		testFile := TestFile[MLKEMDecapsTestVector]{
			Algorithm:     "ML-KEM",
			Schema:        "mlkem_decaps_test_schema.json",
			NumberOfTests: len(testData.Tests),
			Notes:         testData.Notes,
			TestGroups: []TestGroup[MLKEMDecapsTestVector]{
				{
					Type: testData.Type,
					Source: Source{
						Name:    sourceName,
						Version: sourceVersion,
					},
					ParameterSet: testData.ParameterSet,
					Tests:        testData.Tests,
				},
			},
		}

		// Marshal to JSON with indentation
		jsonData, err := json.MarshalIndent(testFile, "", "  ")
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error marshaling JSON for %s: %v\n", filename, err)
			os.Exit(1)
		}
		jsonData = append(jsonData, '\n')

		// Write to file
		outputPath := filepath.Join(outputDir, filename)
		err = os.WriteFile(outputPath, jsonData, 0644)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error writing file %s: %v\n", outputPath, err)
			os.Exit(1)
		}

		fmt.Printf("Generated test vectors -> %s\n", outputPath)
	}

	fmt.Println("Done!")
}
