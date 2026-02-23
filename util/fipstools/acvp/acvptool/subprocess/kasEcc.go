// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

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

	EphemeralXHex          hexEncodedByteString `json:"ephemeralPublicServerX"`
	EphemeralYHex          hexEncodedByteString `json:"ephemeralPublicServerY"`
	EphemeralPrivateKeyHex hexEncodedByteString `json:"ephemeralPrivateIut"`
	EphemeralPublicIutXHex hexEncodedByteString `json:"ephemeralPublicIutX"`
	EphemeralPublicIutYHex hexEncodedByteString `json:"ephemeralPublicIutY"`
	KdfParameter           kdfParameter         `json:"kdfParameter"`
	ExpectedOutput         hexEncodedByteString `json:"dkm"`

	StaticXHex          hexEncodedByteString `json:"staticPublicServerX"`
	StaticYHex          hexEncodedByteString `json:"staticPublicServerY"`
	StaticPrivateKeyHex hexEncodedByteString `json:"staticPrivateIut"`
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
		default:
			return nil, fmt.Errorf("unknown curve %q", group.Curve)
		}

		switch group.Role {
		case "initiator", "responder":
		default:
			return nil, fmt.Errorf("unknown role %q", group.Role)
		}

		var useOnePassNameFields bool
		switch group.Scheme {
		case "ephemeralUnified":
		case "onePassDh":
			useOnePassNameFields = true
		default:
			return nil, fmt.Errorf("unknown scheme %q", group.Scheme)
		}

		switch group.KdfConfiguration.KdfType {
		case "oneStep":
		default:
			return nil, fmt.Errorf("unknown KDF type %q", group.KdfConfiguration.KdfType)
		}

		method := "KAS-ECC/OneStep/" + group.Curve + "/" + group.KdfConfiguration.AuxFunction

		for _, test := range group.Tests {
			var peerX, peerY, privateKey hexEncodedByteString
			if useOnePassNameFields {
				if group.Role == "initiator" {
					peerX, peerY, privateKey = test.StaticXHex, test.StaticYHex, test.StaticPrivateKeyHex
				} else {
					peerX, peerY, privateKey = test.EphemeralXHex, test.EphemeralYHex, test.StaticPrivateKeyHex
				}
			} else {
				peerX, peerY, privateKey = test.EphemeralXHex, test.EphemeralYHex, test.EphemeralPrivateKeyHex
			}

			if len(peerX) == 0 || len(peerY) == 0 {
				return nil, fmt.Errorf("%d/%d is missing peer's point", group.ID, test.ID)
			}

			if (len(privateKey) != 0) != privateKeyGiven {
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
						// VAL mode: use provided public keyreturn nil, err
						fixedInfo = append(fixedInfo, test.EphemeralPublicIutXHex...)
						fixedInfo = append(fixedInfo, test.EphemeralPublicIutYHex...)
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
						fixedInfo = append(fixedInfo, test.EphemeralPublicIutXHex...)
						fixedInfo = append(fixedInfo, test.EphemeralPublicIutYHex...)
					}
				}
			}

			if privateKeyGiven {
				result, err := m.Transact(method, 3, peerX, peerY, privateKey, fixedInfo, outLenBytes[:], nil)
				if err != nil {
					return nil, err
				}

				ok := bytes.Equal(result[2], test.ExpectedOutput)
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
