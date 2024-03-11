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
	"encoding/hex"
	"encoding/json"
	"fmt"
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
	KDFMode         string `json:"kdfMode"`
	MACMode         string `json:"macMode"`
	CounterLocation string `json:"counterLocation"`
	OutputBits      uint32 `json:"keyOutLength"`
	CounterBits     uint32 `json:"counterLength"`
	ZeroIV          bool   `json:"zeroLengthIv"`

	Tests []struct {
		ID     uint64 `json:"tcId"`
		KeyHex string `json:"keyIn"`
		IvHex  string `json:"iv"`
	}
}

type kdfTestGroupResponse struct {
	ID    uint64            `json:"tgId"`
	Tests []kdfTestResponse `json:"tests"`
}

type kdfTestResponse struct {
	ID        uint64 `json:"tcId"`
	FixedData string `json:"fixedData"`
	KeyOut    string `json:"keyOut"`
}

type kdfPrimitive struct{}

func (k *kdfPrimitive) Process(vectorSet []byte, m Transactable) (any, error) {
	var parsed kdfTestVectorSet
	if err := json.Unmarshal(vectorSet, &parsed); err != nil {
		return nil, err
	}

	var respGroups []kdfTestGroupResponse
	for _, group := range parsed.Groups {
		group := group
		groupResp := kdfTestGroupResponse{ID: group.ID}

		if group.OutputBits%8 != 0 {
			return nil, fmt.Errorf("%d bit key in test group %d: fractional bytes not supported", group.OutputBits, group.ID)
		}

		if group.KDFMode != "feedback" {
			// We only support KBKDF in feedback mode
			return nil, fmt.Errorf("KDF mode %q not supported", group.KDFMode)
		}

		if group.CounterLocation != "after fixed data" {
			// We only support the counter location being after fixed data
			return nil, fmt.Errorf("label location %q not supported", group.CounterLocation)
		}

		if group.CounterBits != 8 {
			// We only support counter lengths of 8
			return nil, fmt.Errorf("counter length %q not supported", group.CounterBits)
		}

		outputBytes := uint32le(group.OutputBits / 8)

		// Fixed data variable is determined by the IUT according to the NIST specifications
		// We send it as part of the response so that NIST can verify whether it is correct
		fixedData := make([]byte, 4)
		rand.Read(fixedData)

		for _, test := range group.Tests {
			test := test
			testResp := kdfTestResponse{ID: test.ID}

			key, err := hex.DecodeString(test.KeyHex)
			if err != nil {
				return nil, fmt.Errorf("failed to decode Key in test case %d/%d: %v", group.ID, test.ID, err)
			}

			// Make the call to the crypto module.
			resp, err := m.Transact("KDF/Feedback/"+group.MACMode, 1, outputBytes, key, fixedData)
			if err != nil {
				return nil, fmt.Errorf("wrapper KDF operation failed: %s", err)
			}

			// Parse results.
			testResp.ID = test.ID
			testResp.KeyOut = hex.EncodeToString(resp[0])
			testResp.FixedData = hex.EncodeToString(fixedData)

			groupResp.Tests = append(groupResp.Tests, testResp)
		}
		respGroups = append(respGroups, groupResp)
	}

	return respGroups, nil
}
