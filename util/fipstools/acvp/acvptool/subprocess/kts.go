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
	"encoding/json"
	"fmt"
)

type ktsVectorSet struct {
	Groups []ktsTestGroup `json:"testGroups"`
}

type ktsTestGroup struct {
	ID               uint64           `json:"tgId"`
	Type             string           `json:"testType"`
	Role             string           `json:"kasRole"`
	Scheme           string           `json:"scheme"`
	KtsConfiguration ktsConfiguration `json:"ktsConfiguration"`
	Tests            []ktsTest        `json:"tests"`
	L                uint32           `json:"l"`
}

type ktsConfiguration struct {
	HashAlg string `json:"hashAlg"`
}

type ktsTest struct {
	ID      uint64               `json:"tcId"`
	ServerN hexEncodedByteString `json:"serverN"`
	ServerE hexEncodedByteString `json:"serverE"`
	IutN    hexEncodedByteString `json:"iutN"`
	IutE    hexEncodedByteString `json:"iutE"`
	IutP    hexEncodedByteString `json:"iutP"`
	IutQ    hexEncodedByteString `json:"iutQ"`
	IutD    hexEncodedByteString `json:"iutD"`
	Ct      hexEncodedByteString `json:"serverC"`
}

type ktsTestGroupResponse struct {
	ID    uint64            `json:"tgId"`
	Tests []ktsTestResponse `json:"tests"`
}

type ktsTestResponse struct {
	ID   uint64               `json:"tcId"`
	IutC hexEncodedByteString `json:"iutC,omitempty"`
	Dkm  hexEncodedByteString `json:"dkm"`
}

type kts struct{}

func (k *kts) Process(vectorSet []byte, m Transactable) (interface{}, error) {
	var parsed ktsVectorSet
	if err := json.Unmarshal(vectorSet, &parsed); err != nil {
		return nil, err
	}

	// See https://pages.nist.gov/ACVP/draft-hammett-acvp-kas-ifc.html
	var ret []ktsTestGroupResponse
	for _, group := range parsed.Groups {
		group := group
		response := ktsTestGroupResponse{
			ID: group.ID,
		}

		if group.Type != "AFT" {
			return nil, fmt.Errorf("unknown test type %q", group.Scheme)
		}

		switch group.Role {
		case "initiator", "responder":
			break
		default:
			return nil, fmt.Errorf("unknown role %q", group.Role)
		}

		if group.Scheme != "KTS-OAEP-basic" {
			return nil, fmt.Errorf("unknown scheme %q", group.Scheme)
		}

		if len(group.KtsConfiguration.HashAlg) == 0 {
			return nil, fmt.Errorf("missing hash algorithm")
		}

		hashAlg := group.KtsConfiguration.HashAlg

		var outLenBytes [4]byte
		NativeEndian.PutUint32(outLenBytes[:], group.L/8) // Convert bits to bytes

		for _, test := range group.Tests {
			test := test
			if group.Role == "initiator" {
				result, err := m.Transact("KTS/OAEP/"+hashAlg+"/transport", 2, outLenBytes[:], test.ServerN, test.ServerE)
				if err != nil {
					return nil, err
				}
				response.Tests = append(response.Tests, ktsTestResponse{
					ID:   test.ID,
					IutC: result[0],
					Dkm:  result[1],
				})
			} else {
				result, err := m.Transact("KTS/OAEP/"+hashAlg+"/receive", 1, test.Ct, test.IutN, test.IutE, test.IutQ, test.IutP, test.IutD)
				if err != nil {
					return nil, err
				}

				response.Tests = append(response.Tests, ktsTestResponse{
					ID:  test.ID,
					Dkm: result[0],
				})
			}
		}

		ret = append(ret, response)
	}

	return ret, nil
}
