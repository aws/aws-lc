// Copyright (c) 2020, Google Inc.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

package subprocess

import (
	"crypto/rand"
	"encoding/json"
	"fmt"
	"strings"
)

type CounterLocation string

func (c *CounterLocation) UnmarshalJSON(v []byte) error {
	var parsed string
	if err := json.Unmarshal(v, &parsed); err != nil {
		return err
	}

	var val CounterLocation

	// Normalize to constants for easy comparisons later
	switch {
	case strings.EqualFold(parsed, string(NoneCounterLocation)):
		val = NoneCounterLocation
	case strings.EqualFold(parsed, string(AfterFixedDataCounterLocation)):
		val = AfterFixedDataCounterLocation
	case strings.EqualFold(parsed, string(BeforeFixedDataCounterLocation)):
		val = BeforeFixedDataCounterLocation
	case strings.EqualFold(parsed, string(MiddleFixedDataCounterLocation)):
		val = MiddleFixedDataCounterLocation
	case strings.EqualFold(parsed, string(BeforeIterator)):
		val = BeforeIterator
	default:
		return fmt.Errorf("unknown KDF counter location: %v", parsed)
	}

	*c = val

	return nil
}

const (
	NoneCounterLocation            CounterLocation = "none"
	AfterFixedDataCounterLocation  CounterLocation = "after fixed data"
	MiddleFixedDataCounterLocation CounterLocation = "middle fixed data"
	BeforeFixedDataCounterLocation CounterLocation = "before fixed data"
	BeforeIterator                 CounterLocation = "before iterator"
)

// The following structures reflect the JSON of ACVP KDF-1.0 tests. See
// https://pages.nist.gov/ACVP/draft-celi-acvp-kbkdf.html#name-test-groups-json-schema

type kdfTestVectorSet struct {
	Groups []kdfTestGroup `json:"testGroups"`
}

type kdfTestGroup struct {
	ID uint64 `json:"tgId"`
	// KDFMode can take the values "counter", "feedback", or
	// "double pipeline iteration".
	KDFMode         string          `json:"kdfMode"`
	MACMode         string          `json:"macMode"`
	CounterLocation CounterLocation `json:"counterLocation"`
	OutputBits      uint32          `json:"keyOutLength"`
	CounterBits     uint32          `json:"counterLength"`
	ZeroIV          bool            `json:"zeroLengthIv"`

	Tests []struct {
		ID  uint64               `json:"tcId"`
		Key hexEncodedByteString `json:"keyIn"`
		Iv  hexEncodedByteString `json:"iv"`
	}
}

type kdfTestGroupResponse struct {
	ID    uint64            `json:"tgId"`
	Tests []kdfTestResponse `json:"tests"`
}

type kdfTestResponse struct {
	ID        uint64               `json:"tcId"`
	FixedData hexEncodedByteString `json:"fixedData"`
	KeyOut    hexEncodedByteString `json:"keyOut"`
}

type kdfPrimitive struct{}

func (k *kdfPrimitive) Process(vectorSet []byte, m Transactable) (interface{}, error) {
	var parsed kdfTestVectorSet
	if err := json.Unmarshal(vectorSet, &parsed); err != nil {
		return nil, err
	}

	var respGroups []kdfTestGroupResponse
	for _, group := range parsed.Groups {
		var groupProcessor func(kdfTestGroup, Transactable) (kdfTestGroupResponse, error)

		// We only support KBKDF in feedback or counter modes
		switch {
		case strings.EqualFold(group.KDFMode, "feedback"):
			groupProcessor = processFeedbackMode
		case strings.EqualFold(group.KDFMode, "counter"):
			groupProcessor = processCounterMode
		default:
			return nil, fmt.Errorf("KDF mode %q not supported", group.KDFMode)
		}

		groupResp, err := groupProcessor(group, m)
		if err != nil {
			return nil, err
		}
		respGroups = append(respGroups, groupResp)
	}

	return respGroups, nil
}

func processFeedbackMode(group kdfTestGroup, m Transactable) (kdfTestGroupResponse, error) {
	groupResp := kdfTestGroupResponse{ID: group.ID}

	if group.OutputBits%8 != 0 {
		return kdfTestGroupResponse{}, fmt.Errorf("%d bit key in test group %d: fractional bytes not supported", group.OutputBits, group.ID)
	}

	if group.CounterLocation != AfterFixedDataCounterLocation {
		// We only support the counter location being after fixed data
		return kdfTestGroupResponse{}, fmt.Errorf("counter location %q not supported", group.CounterLocation)
	}

	if group.CounterBits != 8 {
		// We only support counter lengths of 8
		return kdfTestGroupResponse{}, fmt.Errorf("counter length %v not supported", group.CounterBits)
	}

	outputBytes := uint32le(group.OutputBits / 8)

	// Fixed data variable is determined by the IUT according to the NIST specifications
	// We send it as part of the response so that NIST can verify whether it is correct
	fixedData := make([]byte, 4)
	rand.Read(fixedData)

	for _, test := range group.Tests {
		test := test
		testResp := kdfTestResponse{ID: test.ID}

		// Make the call to the crypto module.
		resp, err := m.Transact("KDF/Feedback/"+group.MACMode, 1, outputBytes, test.Key, fixedData)
		if err != nil {
			return kdfTestGroupResponse{}, fmt.Errorf("wrapper KDF operation failed: %s", err)
		}

		// Parse results.
		testResp.ID = test.ID
		testResp.KeyOut = resp[0]
		testResp.FixedData = fixedData

		groupResp.Tests = append(groupResp.Tests, testResp)
	}

	return groupResp, nil
}

func processCounterMode(group kdfTestGroup, m Transactable) (kdfTestGroupResponse, error) {
	groupResp := kdfTestGroupResponse{ID: group.ID}

	if group.OutputBits%8 != 0 {
		return kdfTestGroupResponse{}, fmt.Errorf("%d bit key in test group %d: fractional bytes not supported", group.OutputBits, group.ID)
	}

	if group.CounterLocation != BeforeFixedDataCounterLocation {
		// We only support the counter location being after fixed data
		return kdfTestGroupResponse{}, fmt.Errorf("counter location %q not supported", group.CounterLocation)
	}

	if group.CounterBits != 32 {
		// We only support counter lengths of 32
		return kdfTestGroupResponse{}, fmt.Errorf("counter length %v not supported", group.CounterBits)
	}

	outputBytes := uint32le(group.OutputBits / 8)

	// Fixed data variable is determined by the IUT according to the NIST specifications
	// We send it as part of the response so that NIST can verify whether it is correct
	fixedData := make([]byte, 4)
	rand.Read(fixedData)

	for _, test := range group.Tests {
		test := test
		testResp := kdfTestResponse{ID: test.ID}

		// Make the call to the crypto module.
		resp, err := m.Transact("KDF/Counter/"+group.MACMode, 1, outputBytes, test.Key, fixedData)
		if err != nil {
			return kdfTestGroupResponse{}, fmt.Errorf("wrapper KDF operation failed: %s", err)
		}

		// Parse results.
		testResp.ID = test.ID
		testResp.KeyOut = resp[0]
		testResp.FixedData = fixedData

		groupResp.Tests = append(groupResp.Tests, testResp)
	}

	return groupResp, nil
}
