// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package subprocess

import (
	"encoding/json"
	"fmt"
	"strings"
)

type mlDsa struct{}

func (*mlDsa) Process(vectorSet []byte, m Transactable) (interface{}, error) {
	var vs struct {
		Mode       string          `json:"mode"`
		TestGroups json.RawMessage `json:"testGroups"`
	}

	if err := json.Unmarshal(vectorSet, &vs); err != nil {
		return nil, err
	}

	switch {
	case strings.EqualFold(vs.Mode, "keyGen"):
		return processMlDsaKeyGen(vs.TestGroups, m)
	case strings.EqualFold(vs.Mode, "sigGen"):
		return processMlDsaSigGen(vs.TestGroups, m)
	case strings.EqualFold(vs.Mode, "sigVer"):
		return processMlDsaSigVer(vs.TestGroups, m)
	}

	return nil, fmt.Errorf("unknown ML-DSA mode: %v", vs.Mode)
}

type mlDsaKeyGenTestGroup struct {
	ID           uint64 `json:"tgId"`
	Type         string `json:"testType"`
	ParameterSet string `json:"parameterSet"`
	Tests        []struct {
		ID   uint64               `json:"tcId"`
		SEED hexEncodedByteString `json:"seed"`
	}
}

type mlDsaKeyGenTestGroupResponse struct {
	ID    uint64                        `json:"tgId"`
	Tests []mlDsaKeyGenTestCaseResponse `json:"tests"`
}

type mlDsaKeyGenTestCaseResponse struct {
	ID uint64               `json:"tcId"`
	PK hexEncodedByteString `json:"pk"`
	SK hexEncodedByteString `json:"sk"`
}

func processMlDsaKeyGen(vectors json.RawMessage, m Transactable) (interface{}, error) {
	var groups []mlDsaKeyGenTestGroup

	if err := json.Unmarshal(vectors, &groups); err != nil {
		return nil, err
	}

	var responses []mlDsaKeyGenTestGroupResponse

	for _, group := range groups {
		if !strings.EqualFold(group.Type, "AFT") {
			return nil, fmt.Errorf("unsupported keyGen test type: %v", group.Type)
		}

		response := mlDsaKeyGenTestGroupResponse{
			ID: group.ID,
		}

		for _, test := range group.Tests {
			results, err := m.Transact("ML-DSA/"+group.ParameterSet+"/keyGen", 2, test.SEED)
			if err != nil {
				return nil, err
			}

			pk := results[0]
			sk := results[1]

			response.Tests = append(response.Tests, mlDsaKeyGenTestCaseResponse{
				ID: test.ID,
				PK: pk,
				SK: sk,
			})
		}

		responses = append(responses, response)
	}

	return responses, nil
}

type mlDsaSigGenTestGroup struct {
	ID                 uint64 `json:"tgId"`
	Type               string `json:"testType"`
	ParameterSet       string `json:"parameterSet"`
	Deterministic      bool   `json:"deterministic"`
	SignatureInterface string `json:"signatureInterface"`
	ExternalMu         bool   `json:"externalMu`
	Tests              []struct {
		ID      uint64               `json:"tcId"`
		Message hexEncodedByteString `json:"message"`
		MU      hexEncodedByteString `json:"mu"`
		SK      hexEncodedByteString `json:"sk"`
		RND     hexEncodedByteString `json:"rnd"`
		Context hexEncodedByteString `json:"context"`
		HashAlg string               `json:"hashAlg"`
	}
}

type mlDsaSigGenTestGroupResponse struct {
	ID    uint64                        `json:"tgId"`
	Tests []mlDsaSigGenTestCaseResponse `json:"tests"`
}

type mlDsaSigGenTestCaseResponse struct {
	ID        uint64               `json:"tcId"`
	Signature hexEncodedByteString `json:"signature"`
}

// Convert boolean to byte slice (using 1 for true, 0 for false)
func boolToBytes(b bool) []byte {
	if b {
		return []byte{1}
	}
	return []byte{0}
}

func processMlDsaSigGen(vectors json.RawMessage, m Transactable) (interface{}, error) {
	var groups []mlDsaSigGenTestGroup

	if err := json.Unmarshal(vectors, &groups); err != nil {
		return nil, err
	}

	var responses []mlDsaSigGenTestGroupResponse

	for _, group := range groups {
		if !strings.EqualFold(group.Type, "AFT") {
			return nil, fmt.Errorf("unsupported sigGen test type: %v", group.Type)
		}

		response := mlDsaSigGenTestGroupResponse{
			ID: group.ID,
		}

		for _, test := range group.Tests {
			results, err := m.Transact("ML-DSA/"+group.ParameterSet+"/sigGen",
				1, test.SK, test.Message, test.MU, test.RND, boolToBytes(group.ExternalMu))
			if err != nil {
				return nil, err
			}

			signature := results[0]

			response.Tests = append(response.Tests, mlDsaSigGenTestCaseResponse{
				ID:        test.ID,
				Signature: signature,
			})
		}

		responses = append(responses, response)
	}
	return responses, nil
}

type mlDsaSigVerTestGroup struct {
	ID                 uint64 `json:"tgId"`
	Type               string `json:"testType"`
	ParameterSet       string `json:"parameterSet"`
	Deterministic      bool   `json:"deterministic"`
	SignatureInterface string `json:"signatureInterface"`
	ExternalMu         bool   `json:"externalMu`
	Tests              []struct {
		ID        uint64               `json:"tcId"`
		PK        hexEncodedByteString `json:"pk"`
		Message   hexEncodedByteString `json:"message"`
		MU        hexEncodedByteString `json:"mu"`
		Signature hexEncodedByteString `json:"signature"`
		Context   hexEncodedByteString `json:"context"`
		HashAlg   string               `json:"hashAlg"`
	}
}

type mlDsaSigVerTestGroupResponse struct {
	ID    uint64                        `json:"tgId"`
	Tests []mlDsaSigVerTestCaseResponse `json:"tests"`
}

type mlDsaSigVerTestCaseResponse struct {
	ID         uint64 `json:"tcId"`
	TestPassed *bool  `json:"testPassed"`
}

func processMlDsaSigVer(vectors json.RawMessage, m Transactable) (interface{}, error) {
	var groups []mlDsaSigVerTestGroup

	if err := json.Unmarshal(vectors, &groups); err != nil {
		return nil, err
	}

	var responses []mlDsaSigVerTestGroupResponse

	for _, group := range groups {
		if !strings.EqualFold(group.Type, "AFT") {
			return nil, fmt.Errorf("unsupported sigVer test type: %v", group.Type)
		}

		response := mlDsaSigVerTestGroupResponse{
			ID: group.ID,
		}

		for _, test := range group.Tests {
			results, err := m.Transact("ML-DSA/"+group.ParameterSet+"/sigVer", 1,
				test.Signature, test.PK, test.Message, test.MU, boolToBytes(group.ExternalMu))
			if err != nil {
				return nil, err
			}

			var passed *bool
			if len(results[0]) == 1 {
				val := results[0][0] == 1
				passed = &val
			}

			response.Tests = append(response.Tests, mlDsaSigVerTestCaseResponse{
				ID:         test.ID,
				TestPassed: passed,
			})
		}

		responses = append(responses, response)
	}
	return responses, nil
}
