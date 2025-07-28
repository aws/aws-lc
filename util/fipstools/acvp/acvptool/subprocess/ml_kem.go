// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package subprocess

import (
	"encoding/json"
	"fmt"
	"strings"
)

type mlKem struct{}

func (*mlKem) Process(vectorSet []byte, m Transactable) (interface{}, error) {
	var vs struct {
		Mode       string          `json:"mode"`
		TestGroups json.RawMessage `json:"testGroups"`
	}

	if err := json.Unmarshal(vectorSet, &vs); err != nil {
		return nil, err
	}

	switch {
	case strings.EqualFold(vs.Mode, "keyGen"):
		return processMlKemKeyGen(vs.TestGroups, m)
	case strings.EqualFold(vs.Mode, "encapDecap"):
		return processMlKemEncapDecap(vs.TestGroups, m)
	}

	return nil, fmt.Errorf("unknown ML-KEM mode: %v", vs.Mode)
}

type mlKemKeyGenTestGroup struct {
	ID           uint64 `json:"tgId"`
	Type         string `json:"testType"`
	ParameterSet string `json:"parameterSet"`
	Tests        []struct {
		ID uint64               `json:"tcId"`
		D  hexEncodedByteString `json:"d"`
		Z  hexEncodedByteString `json:"z"`
	}
}

type mlKemKeyGenTestGroupResponse struct {
	ID    uint64                        `json:"tgId"`
	Tests []mlKemKeyGenTestCaseResponse `json:"tests"`
}

type mlKemKeyGenTestCaseResponse struct {
	ID uint64               `json:"tcId"`
	EK hexEncodedByteString `json:"ek"`
	DK hexEncodedByteString `json:"dk"`
}

func processMlKemKeyGen(vectors json.RawMessage, m Transactable) (interface{}, error) {
	var groups []mlKemKeyGenTestGroup

	if err := json.Unmarshal(vectors, &groups); err != nil {
		return nil, err
	}

	var responses []mlKemKeyGenTestGroupResponse

	for _, group := range groups {
		if !strings.EqualFold(group.Type, "AFT") {
			return nil, fmt.Errorf("unsupported keyGen test type: %v", group.Type)
		}

		response := mlKemKeyGenTestGroupResponse{
			ID: group.ID,
		}

		for _, test := range group.Tests {
			results, err := m.Transact("ML-KEM/"+group.ParameterSet+"/keyGen", 2, test.D, test.Z)
			if err != nil {
				return nil, err
			}

			ek := results[0]
			dk := results[1]

			response.Tests = append(response.Tests, mlKemKeyGenTestCaseResponse{
				ID: test.ID,
				EK: ek,
				DK: dk,
			})
		}

		responses = append(responses, response)
	}

	return responses, nil
}

type mlKemEncapDecapTestGroup struct {
	ID           uint64               `json:"tgId"`
	Type         string               `json:"testType"`
	ParameterSet string               `json:"parameterSet"`
	Function     string               `json:"function"`
	DK           hexEncodedByteString `json:"dk"`
	Tests        []struct {
		ID uint64               `json:"tcId"`
		EK hexEncodedByteString `json:"ek"`
		M  hexEncodedByteString `json:"m"`
		C  hexEncodedByteString `json:"c"`
	}
}

type mlKemEncDecapTestGroupResponse struct {
	ID    uint64                          `json:"tgId"`
	Tests []mlKemEncDecapTestCaseResponse `json:"tests"`
}

type mlKemEncDecapTestCaseResponse struct {
	ID uint64               `json:"tcId"`
	C  hexEncodedByteString `json:"c,omitempty"`
	K  hexEncodedByteString `json:"k,omitempty"`
}

func processMlKemEncapDecap(vectors json.RawMessage, m Transactable) (interface{}, error) {
	var groups []mlKemEncapDecapTestGroup

	if err := json.Unmarshal(vectors, &groups); err != nil {
		return nil, err
	}

	var responses []mlKemEncDecapTestGroupResponse

	for _, group := range groups {
		if (strings.EqualFold(group.Function, "encapsulation") && !strings.EqualFold(group.Type, "AFT")) ||
			(strings.EqualFold(group.Function, "decapsulation") && !strings.EqualFold(group.Type, "VAL")) {
			return nil, fmt.Errorf("unsupported encapDecap function and test group type pair: (%v, %v)", group.Function, group.Type)
		}

		response := mlKemEncDecapTestGroupResponse{
			ID: group.ID,
		}

		for _, test := range group.Tests {
			var (
				err          error
				testResponse mlKemEncDecapTestCaseResponse
			)

			switch {
			case strings.EqualFold(group.Function, "encapsulation"):
				testResponse, err = processMlKemEncapTestCase(test.ID, group.ParameterSet, test.EK, test.M, m)
			case strings.EqualFold(group.Function, "decapsulation"):
				testResponse, err = processMlKemDecapTestCase(test.ID, group.ParameterSet, group.DK, test.C, m)
			default:
				return nil, fmt.Errorf("unknown encDecap function: %v", group.Function)
			}
			if err != nil {
				return nil, err
			}

			response.Tests = append(response.Tests, testResponse)
		}

		responses = append(responses, response)
	}
	return responses, nil
}

func processMlKemEncapTestCase(id uint64, algorithm string, ek []byte, m []byte, t Transactable) (mlKemEncDecapTestCaseResponse, error) {
	results, err := t.Transact("ML-KEM/"+algorithm+"/encap", 2, ek, m)
	if err != nil {
		return mlKemEncDecapTestCaseResponse{}, err
	}

	c := results[0]
	k := results[1]

	return mlKemEncDecapTestCaseResponse{
		ID: id,
		C:  c,
		K:  k,
	}, nil
}

func processMlKemDecapTestCase(id uint64, algorithm string, dk []byte, c []byte, t Transactable) (mlKemEncDecapTestCaseResponse, error) {
	results, err := t.Transact("ML-KEM/"+algorithm+"/decap", 1, dk, c)
	if err != nil {
		return mlKemEncDecapTestCaseResponse{}, err
	}

	k := results[0]

	return mlKemEncDecapTestCaseResponse{
		ID: id,
		K:  k,
	}, nil
}
