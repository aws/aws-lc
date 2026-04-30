// Copyright (c) 2020, Google Inc.
// SPDX-License-Identifier: ISC

package testconfig

import (
	"encoding/json"
	"os"
)

type Test struct {
	Cmd            []string `json:"cmd"`
	Env            []string `json:"env"`
	SkipSDE        bool     `json:"skip_sde"`
	SkipValgrind   bool     `json:"skip_valgrind"`
	ValgrindSupp   []string `json:"valgrind_supp"`
	ValgrindFilter string   `json:"valgrind_filter"`
	TargetArch     string   `json:"target_arch"`
	Shard          bool     `json:"shard"`
}

func ParseTestConfig(filename string) ([]Test, error) {
	in, err := os.Open(filename)
	if err != nil {
		return nil, err
	}
	defer in.Close()

	decoder := json.NewDecoder(in)
	var result []Test
	if err := decoder.Decode(&result); err != nil {
		return nil, err
	}
	return result, nil
}
