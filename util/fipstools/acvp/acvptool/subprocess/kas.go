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
	"bytes"
	"encoding/json"
	"fmt"
)

type kasVectorSet struct {
	Groups []kasTestGroup `json:"testGroups"`
}

type kasTestGroup struct {
	ID     uint64    `json:"tgId"`
	Type   string    `json:"testType"`
	Curve  string    `json:"domainParameterGenerationMode"`
	Role   string    `json:"kasRole"`
	Scheme string    `json:"scheme"`
	Tests  []kasTest `json:"tests"`
}

type kasTest struct {
	ID uint64 `json:"tcId"`

	EphemeralXHex          hexEncodedByteString `json:"ephemeralPublicServerX"`
	EphemeralYHex          hexEncodedByteString `json:"ephemeralPublicServerY"`
	EphemeralPrivateKeyHex hexEncodedByteString `json:"ephemeralPrivateIut"`

	StaticXHex          hexEncodedByteString `json:"staticPublicServerX"`
	StaticYHex          hexEncodedByteString `json:"staticPublicServerY"`
	StaticPrivateKeyHex hexEncodedByteString `json:"staticPrivateIut"`

	Result hexEncodedByteString `json:"z"`
}

type kasTestGroupResponse struct {
	ID    uint64            `json:"tgId"`
	Tests []kasTestResponse `json:"tests"`
}

type kasTestResponse struct {
	ID uint64 `json:"tcId"`

	EphemeralXHex hexEncodedByteString `json:"ephemeralPublicIutX,omitempty"`
	EphemeralYHex hexEncodedByteString `json:"ephemeralPublicIutY,omitempty"`

	StaticXHex hexEncodedByteString `json:"staticPublicIutX,omitempty"`
	StaticYHex hexEncodedByteString `json:"staticPublicIutY,omitempty"`

	Result hexEncodedByteString `json:"z,omitempty"`
	Passed *bool                `json:"testPassed,omitempty"`
}

type kas struct{}

func (k *kas) Process(vectorSet []byte, m Transactable) (interface{}, error) {
	var parsed kasVectorSet
	if err := json.Unmarshal(vectorSet, &parsed); err != nil {
		return nil, err
	}

	// See https://pages.nist.gov/ACVP/draft-fussell-acvp-kas-ecc.html#name-test-vectors
	var ret []kasTestGroupResponse
	for _, group := range parsed.Groups {
		group := group
		response := kasTestGroupResponse{
			ID: group.ID,
		}

		var privateKeyGiven bool
		switch group.Type {
		case "AFT":
			privateKeyGiven = false
		case "VAL":
			privateKeyGiven = true
		default:
			return nil, fmt.Errorf("unknown test type %q", group.Type)
		}

		switch group.Curve {
		case "P-224", "P-256", "P-384", "P-521":
		default:
			return nil, fmt.Errorf("unknown curve %q", group.Curve)
		}

		switch group.Role {
		case "initiator", "responder":
		default:
			return nil, fmt.Errorf("unknown role %q", group.Role)
		}

		var useEphemeralPeerKeys bool
		var useEphemeralPrivateKey bool
		switch group.Scheme {
		case "ephemeralUnified":
			useEphemeralPeerKeys = true
			useEphemeralPrivateKey = true
		case "staticUnified":
			useEphemeralPeerKeys = false
			useEphemeralPrivateKey = false
		case "onePassDh":
			if group.Role == "initiator" {
				useEphemeralPeerKeys = false
				useEphemeralPrivateKey = true
			} else {
				useEphemeralPeerKeys = true
				useEphemeralPrivateKey = false
			}
		default:
			return nil, fmt.Errorf("unknown scheme %q", group.Scheme)
		}

		generateEphemeralKeys := useEphemeralPrivateKey && group.Role != "staticUnified"

		method := "ECDH/" + group.Curve

		for _, test := range group.Tests {
			test := test

			var peerX, peerY, privateKey hexEncodedByteString
			if useEphemeralPeerKeys {
				peerX, peerY = test.EphemeralXHex, test.EphemeralYHex
			} else {
				peerX, peerY = test.StaticXHex, test.StaticYHex
			}

			if useEphemeralPrivateKey {
				privateKey = test.EphemeralPrivateKeyHex
			} else {
				privateKey = test.StaticPrivateKeyHex
			}

			if len(peerX) == 0 || len(peerY) == 0 {
				return nil, fmt.Errorf("%d/%d is missing peer's point", group.ID, test.ID)
			}

			if (len(privateKey) != 0) != privateKeyGiven {
				return nil, fmt.Errorf("%d/%d incorrect private key presence", group.ID, test.ID)
			}

			if privateKeyGiven {
				result, err := m.Transact(method, 3, peerX, peerY, privateKey)
				if err != nil {
					return nil, err
				}

				ok := bytes.Equal(result[2], test.Result)
				response.Tests = append(response.Tests, kasTestResponse{
					ID:     test.ID,
					Passed: &ok,
				})
			} else {
				result, err := m.Transact(method, 3, peerX, peerY, nil)
				if err != nil {
					return nil, err
				}

				testResponse := kasTestResponse{
					ID:     test.ID,
					Result: result[2],
				}

				if generateEphemeralKeys {
					testResponse.EphemeralXHex = result[0]
					testResponse.EphemeralYHex = result[1]
				} else {
					testResponse.StaticXHex = result[0]
					testResponse.StaticYHex = result[1]
				}

				response.Tests = append(response.Tests, testResponse)
			}
		}

		ret = append(ret, response)
	}

	return ret, nil
}
