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
	KdfType           string `json:"kdfType"`
	FixedInfoPattern  string `json:"fixedInfoPattern"`
	FixedInfoEncoding string `json:"fixedInfoEncoding"`
	AuxFunction       string `json:"auxFunction"`
}

type kdfParameter struct {
	KdfType     string `json:"kdfType"`
	AlgorithmId string `json:"algorithmId"`
}

type kasEccTestGroup struct {
	ID               uint64               `json:"tgId"`
	Type             string               `json:"testType"`
	Curve            string               `json:"domainParameterGenerationMode"`
	Role             string               `json:"kasRole"`
	Scheme           string               `json:"scheme"`
	KdfConfiguration kdfConfiguration     `json:"kdfConfiguration"`
	L                uint32               `json:"l"`
	IutId            hexEncodedByteString `json:"iutId"`
	ServerId         hexEncodedByteString `json:"serverId"`
	Tests            []kasEccTest         `json:"tests"`
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

type kasEccTestResponse struct {
	ID            uint64               `json:"tcId"`
	EphemeralXHex hexEncodedByteString `json:"ephemeralPublicIutX,omitempty"`
	EphemeralYHex hexEncodedByteString `json:"ephemeralPublicIutY,omitempty"`
	StaticXHex    hexEncodedByteString `json:"staticPublicIutX,omitempty"`
	StaticYHex    hexEncodedByteString `json:"staticPublicIutY,omitempty"`
	Dkm           hexEncodedByteString `json:"dkm,omitempty"`
	Passed        *bool                `json:"testPassed,omitempty"`
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

		var useEphemeralPeerKeys bool
		var useEphemeralPrivateKey bool
		switch group.Scheme {
		case "ephemeralUnified":
			useEphemeralPeerKeys = true
			useEphemeralPrivateKey = true
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

		switch group.KdfConfiguration.KdfType {
		case "oneStep":
		default:
			return nil, fmt.Errorf("unknown KDF type %q", group.KdfConfiguration.KdfType)
		}

		switch group.KdfConfiguration.FixedInfoPattern {
		case "algorithmId||l||uPartyInfo||vPartyInfo":
		default:
			return nil, fmt.Errorf("unsupported fixed info pattern %q", group.KdfConfiguration.FixedInfoPattern)
		}

		switch group.KdfConfiguration.FixedInfoEncoding {
		case "concatenation":
		default:
			return nil, fmt.Errorf("unsupported fixed info encoding %q", group.KdfConfiguration.FixedInfoEncoding)
		}

		method := "KAS-ECC/OneStep/" + group.Curve + "/" + group.KdfConfiguration.AuxFunction

		for _, test := range group.Tests {
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
				jsonBytes, _ := json.MarshalIndent(group, "", " ")
				return nil, fmt.Errorf("%d/%d incorrect private key presence\n%s", group.ID, test.ID, jsonBytes)
			}

			var outLenBytes [4]byte
			NativeEndian.PutUint32(outLenBytes[:], group.L/8) // Convert bits to bytes

			algorithmId, err := hex.DecodeString(test.KdfParameter.AlgorithmId)
			if err != nil {
				return nil, err
			}

			var lBytes [4]byte
			binary.BigEndian.PutUint32(lBytes[:], group.L)

			// Concatenate algorithmId || l
			fixedInfoPrefix := append([]byte{}, algorithmId...)
			fixedInfoPrefix = append(fixedInfoPrefix, lBytes[:]...)

			// Build partyUInfo and partyVInfo
			var iutInfo, serverInfo []byte
			var partyUInfo, partyVInfo []byte

			if privateKeyGiven {
				iutInfo = append(iutInfo, group.IutId...)
				iutInfo = append(iutInfo, test.EphemeralPublicIutXHex...)
				iutInfo = append(iutInfo, test.EphemeralPublicIutYHex...)
			} else {
				// AFT mode: only iutId, modulewrapper will add generated public key
				iutInfo = append(iutInfo, group.IutId...)
			}

			serverInfo = append(serverInfo, group.ServerId...)
			if useEphemeralPeerKeys {
				serverInfo = append(serverInfo, peerX...)
				serverInfo = append(serverInfo, peerY...)
			}

			if group.Role == "initiator" {
				partyUInfo = iutInfo
				partyVInfo = serverInfo
			} else {
				partyUInfo = serverInfo
				partyVInfo = iutInfo
			}

			addPubKeys := []byte{0}
			if useEphemeralPrivateKey && !privateKeyGiven {
				addPubKeys[0] = 1
			}

			if privateKeyGiven {
				result, err := m.Transact(method, 3, peerX, peerY, privateKey, fixedInfoPrefix, partyUInfo, partyVInfo, outLenBytes[:], addPubKeys)
				if err != nil {
					return nil, err
				}

				ok := bytes.Equal(result[2], test.ExpectedOutput)
				response.Tests = append(response.Tests, kasEccTestResponse{
					ID:     test.ID,
					Passed: &ok,
				})
			} else {
				result, err := m.Transact(method, 3, peerX, peerY, nil, fixedInfoPrefix, partyUInfo, partyVInfo, outLenBytes[:], addPubKeys)
				if err != nil {
					return nil, err
				}

				var testResponse kasEccTestResponse

				if useEphemeralPrivateKey {
					testResponse = kasEccTestResponse{
						ID:            test.ID,
						EphemeralXHex: result[0],
						EphemeralYHex: result[1],
						Dkm:           result[2],
					}
				} else {
					testResponse = kasEccTestResponse{
						ID:         test.ID,
						StaticXHex: result[0],
						StaticYHex: result[1],
						Dkm:        result[2],
					}
				}

				response.Tests = append(response.Tests, testResponse)
			}
		}

		ret = append(ret, response)
	}

	return ret, nil
}
