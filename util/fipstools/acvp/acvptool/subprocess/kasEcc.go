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
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
)

type kasEccVectorSet struct {
	Groups []kasEccTestGroup `json:"testGroups"`
}

type kdfConfiguration struct {
	KdfType     string `json:"kdfType"`
	AuxFunction string `json:"auxFunction"`
}

type kdfParameter struct {
	KdfType     string `json:"kdfType"`
	AlgorithmId string `json:"algorithmId"`
}

type kasEccTestGroup struct {
	ID               uint64           `json:"tgId"`
	Type             string           `json:"testType"`
	Curve            string           `json:"domainParameterGenerationMode"`
	Role             string           `json:"kasRole"`
	Scheme           string           `json:"scheme"`
	KdfConfiguration kdfConfiguration `json:"kdfConfiguration"`
	L                uint32           `json:"l"`
	IutId            string           `json:"iutId"`
	ServerId         string           `json:"serverId"`
	Tests            []kasEccTest     `json:"tests"`
}

type kasEccTest struct {
	ID uint64 `json:"tcId"`

	EphemeralXHex          string       `json:"ephemeralPublicServerX"`
	EphemeralYHex          string       `json:"ephemeralPublicServerY"`
	EphemeralPrivateKeyHex string       `json:"ephemeralPrivateIut"`
	EphemeralPublicIutXHex string       `json:"ephemeralPublicIutX"`
	EphemeralPublicIutYHex string       `json:"ephemeralPublicIutY"`
	KdfParameter           kdfParameter `json:"kdfParameter"`
	Dkm                    string       `json:"dkm"`

	StaticXHex          string `json:"staticPublicServerX"`
	StaticYHex          string `json:"staticPublicServerY"`
	StaticPrivateKeyHex string `json:"staticPrivateIut"`
}

type kasEccTestGroupResponse struct {
	ID    uint64               `json:"tgId"`
	Tests []kasEccTestResponse `json:"tests"`
}

type kasEccResponse struct {
	VsId       uint64                    `json:"vsId,omitempty"`
	Algorithm  string                    `json:"algorithm,omitempty"`
	Revision   string                    `json:"revision,omitempty"`
	IsSample   bool                      `json:"isSample,omitempty"`
	TestGroups []kasEccTestGroupResponse `json:"testGroups"`
}

type kasEccTestResponse struct {
	ID uint64 `json:"tcId"`

	EphemeralXHex string `json:"ephemeralPublicIutX,omitempty"`
	EphemeralYHex string `json:"ephemeralPublicIutY,omitempty"`

	Dkm    string `json:"dkm,omitempty"`
	Passed *bool  `json:"testPassed,omitempty"`
}

type kasEcc struct{}

func (k *kasEcc) Process(vectorSet []byte, m Transactable) (interface{}, error) {
	var parsed kasEccVectorSet
	if err := json.Unmarshal(vectorSet, &parsed); err != nil {
		return nil, err
	}

	// See https://pages.nist.gov/ACVP/draft-fussell-acvp-kas-ecc.html#name-test-vectors
	var ret []kasEccTestGroupResponse
	for _, group := range parsed.Groups {
		group := group
		response := kasEccTestGroupResponse{
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
			break
		default:
			return nil, fmt.Errorf("unknown curve %q", group.Curve)
		}

		switch group.Role {
		case "initiator", "responder":
			break
		default:
			return nil, fmt.Errorf("unknown role %q", group.Role)
		}

		var useOnePassNameFields bool
		switch group.Scheme {
		case "ephemeralUnified":
			break
		case "onePassDh":
			useOnePassNameFields = true
			break
		default:
			return nil, fmt.Errorf("unknown scheme %q", group.Scheme)
		}

		switch group.KdfConfiguration.KdfType {
			case "oneStep":
				break
			default:
				return nil, fmt.Errorf("unknown KDF type %q", group.KdfConfiguration.KdfType)
		}

		method := "KAS-ECC/OneStep/" + group.Curve + "/" + group.KdfConfiguration.AuxFunction

		for _, test := range group.Tests {
			test := test

			var xHex, yHex, privateKeyHex string
			if useOnePassNameFields {
				if group.Role == "initiator" {
					xHex, yHex, privateKeyHex = test.StaticXHex, test.StaticYHex, test.StaticPrivateKeyHex
				} else {
					xHex, yHex, privateKeyHex = test.EphemeralXHex, test.EphemeralYHex, test.StaticPrivateKeyHex
				}
			} else {
				xHex, yHex, privateKeyHex = test.EphemeralXHex, test.EphemeralYHex, test.EphemeralPrivateKeyHex
			}

			if len(xHex) == 0 || len(yHex) == 0 {
				return nil, fmt.Errorf("%d/%d is missing peer's point", group.ID, test.ID)
			}

			peerX, err := hex.DecodeString(xHex)
			if err != nil {
				return nil, err
			}

			peerY, err := hex.DecodeString(yHex)
			if err != nil {
				return nil, err
			}

			if (len(privateKeyHex) != 0) != privateKeyGiven {
				return nil, fmt.Errorf("%d/%d incorrect private key presence", group.ID, test.ID)
			}

			var outLenBytes [4]byte
			NativeEndian.PutUint32(outLenBytes[:], group.L/8) // Convert bits to bytes

			// Build fixedInfo: algorithmId || l || uPartyInfo || vPartyInfo
			// uPartyInfo = uPartyId || ephemeralKey (when available)
			// vPartyInfo = vPartyId || ephemeralKey (when available)
			algorithmId, err := hex.DecodeString(test.KdfParameter.AlgorithmId)
			if err != nil {
				return nil, err
			}

			var lBytes [4]byte
			binary.BigEndian.PutUint32(lBytes[:], group.L)

			iutId, err := hex.DecodeString(group.IutId)
			if err != nil {
				return nil, err
			}

			serverId, err := hex.DecodeString(group.ServerId)
			if err != nil {
				return nil, err
			}

			fixedInfo := append([]byte{}, algorithmId...)
			fixedInfo = append(fixedInfo, lBytes[:]...)

			if group.Role == "initiator" {
				// IUT is party U (initiator), Server is party V (responder)
				fixedInfo = append(fixedInfo, iutId...)
				if !useOnePassNameFields {
					// ephemeralUnified: IUT has ephemeral key
					if privateKeyGiven {
						// VAL mode: use provided public key
						iutPubX, err := hex.DecodeString(test.EphemeralPublicIutXHex)
						if err != nil {
							return nil, err
						}
						iutPubY, err := hex.DecodeString(test.EphemeralPublicIutYHex)
						if err != nil {
							return nil, err
						}
						fixedInfo = append(fixedInfo, iutPubX...)
						fixedInfo = append(fixedInfo, iutPubY...)
					}
				}
				fixedInfo = append(fixedInfo, serverId...)
				fixedInfo = append(fixedInfo, peerX...)
				fixedInfo = append(fixedInfo, peerY...)
			} else {
				// Server is U party (initiator), IUT is V party (responder)
				fixedInfo = append(fixedInfo, serverId...)
				fixedInfo = append(fixedInfo, peerX...)
				fixedInfo = append(fixedInfo, peerY...)
				fixedInfo = append(fixedInfo, iutId...)
				if !useOnePassNameFields {
					// ephemeralUnified: IUT has ephemeral key
					if privateKeyGiven {
						// VAL mode: use provided public key
						iutPubX, err := hex.DecodeString(test.EphemeralPublicIutXHex)
						if err != nil {
							return nil, err
						}
						iutPubY, err := hex.DecodeString(test.EphemeralPublicIutYHex)
						if err != nil {
							return nil, err
						}
						fixedInfo = append(fixedInfo, iutPubX...)
						fixedInfo = append(fixedInfo, iutPubY...)
					}
				}
			}

			if privateKeyGiven {
				privateKey, err := hex.DecodeString(privateKeyHex)
				if err != nil {
					return nil, err
				}

				expectedOutput, err := hex.DecodeString(test.Dkm)
				if err != nil {
					return nil, err
				}

				result, err := m.Transact(method, 3, peerX, peerY, privateKey, fixedInfo, outLenBytes[:], nil)
				if err != nil {
					return nil, err
				}

				ok := bytes.Equal(result[2], expectedOutput)
				response.Tests = append(response.Tests, kasEccTestResponse{
					ID:     test.ID,
					Passed: &ok,
				})
			} else {
				result, err := m.Transact(method, 3, peerX, peerY, nil, fixedInfo, outLenBytes[:], nil)
				if err != nil {
					return nil, err
				}

				testResponse := kasEccTestResponse{
					ID:            test.ID,
					EphemeralXHex: hex.EncodeToString(result[0]),
					EphemeralYHex: hex.EncodeToString(result[1]),
					Dkm:           hex.EncodeToString(result[2]),
				}

				response.Tests = append(response.Tests, testResponse)
			}
		}

		ret = append(ret, response)
	}

	return ret, nil
}
