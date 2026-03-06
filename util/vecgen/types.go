package main

// TestGroup represents a group of related test vectors
type TestGroup[T any] struct {
	Type         string `json:"type"`
	Source       Source `json:"source"`
	ParameterSet string `json:"parameterSet"`
	Tests        []T    `json:"tests"`
}

// TestFile represents the complete test vector file structure
type TestFile[T any] struct {
	Algorithm     string         `json:"algorithm"`
	Schema        string         `json:"schema"`
	NumberOfTests int            `json:"numberOfTests"`
	Notes         map[string]any `json:"notes"`
	TestGroups    []TestGroup[T] `json:"testGroups"`
}

// Source identifies the origin of test vectors
type Source struct {
	Name    string `json:"name"`
	Version string `json:"version"`
}

// TestData represents the raw test data for any cryptographic primitive
type TestData[T any] struct {
	ParameterSet string
	Type         string
	Notes        map[string]any
	Tests        []T
}
