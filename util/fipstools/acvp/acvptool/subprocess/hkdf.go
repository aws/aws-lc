// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package subprocess

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"strings"
)

// The following structures reflect the JSON of ACVP KDA HKDF tests. See
// https://pages.nist.gov/ACVP/draft-hammett-acvp-kas-kdf-hkdf.html

type hkdfTestVectorSet struct {
	Groups []hkdfTestGroup `json:"testGroups"`
	Mode   string          `json:"mode"`
}

type hkdfTestGroup struct {
	ID     uint64            `json:"tgId"`
	Type   string            `json:"testType"` // AFT or VAL
	Config hkdfConfiguration `json:"kdfConfiguration"`
	Tests  []hkdfTest        `json:"tests"`
}

type hkdfTest struct {
	ID          uint64         `json:"tcId"`
	Params      hkdfParameters `json:"kdfParameter"`
	PartyU      hkdfPartyInfo  `json:"fixedInfoPartyU"`
	PartyV      hkdfPartyInfo  `json:"fixedInfoPartyV"`
	ExpectedHex string         `json:"dkm"`
}

type hkdfConfiguration struct {
	Type               string `json:"kdfType"`
	SaltMethod         string `json:"saltMethod"`
	SaltLength         uint64 `json:"saltLen"`
	FixedInfoPattern   string `json:"fixedInfoPattern"`
	FixedInputEncoding string `json:"fixedInfoEncoding"`
	HmacAlg            string `json:"hmacAlg"`
	OutputBits         uint32 `json:"l"`
}

func (c *hkdfConfiguration) extract() (outBytes uint32, hashName string, err error) {
	if c.Type != "hkdf" ||
		(c.SaltMethod != "default" && c.SaltMethod != "random") ||
		!strings.Contains(c.FixedInfoPattern, "uPartyInfo||vPartyInfo") ||
		c.FixedInputEncoding != "concatenation" ||
		c.OutputBits%8 != 0 {
		return 0, "", fmt.Errorf("Test group not configured for KDA HKDF")
	}

	return c.OutputBits / 8, c.HmacAlg, nil
}

type hkdfParameters struct {
	KdfType         string `json:"kdfType"`
	SaltHex         string `json:"salt"`
	AlgorithmId     string `json:"algorithmID"`
	Context         string `json:"context"`
	Label           string `json:"label"`
	OutputBits      uint32 `json:"l"`
	KeyHex          string `json:"z"`
	SecondaryKeyHex string `json:"t"`
}

func (p *hkdfParameters) extract() (key, salt []byte, err error) {
	salt, err = hex.DecodeString(p.SaltHex)
	if err != nil {
		return nil, nil, err
	}

	key, err = hex.DecodeString(p.KeyHex)
	if err != nil {
		return nil, nil, err
	}

	return key, salt, nil
}

func (p *hkdfParameters) data() []byte {
	ret := make([]byte, 4)
	binary.BigEndian.PutUint32(ret, p.OutputBits)

	return ret
}

type hkdfPartyInfo struct {
	IDHex    string `json:"partyId"`
	ExtraHex string `json:"ephemeralData"`
}

func (p *hkdfPartyInfo) data() ([]byte, error) {
	ret, err := hex.DecodeString(p.IDHex)
	if err != nil {
		return nil, err
	}

	if len(p.ExtraHex) > 0 {
		extra, err := hex.DecodeString(p.ExtraHex)
		if err != nil {
			return nil, err
		}
		ret = append(ret, extra...)
	}

	return ret, nil
}

type hkdfTestGroupResponse struct {
	ID    uint64             `json:"tgId"`
	Tests []hkdfTestResponse `json:"tests"`
}

type hkdfTestResponse struct {
	ID     uint64 `json:"tcId"`
	KeyOut string `json:"dkm,omitempty"`
	Passed *bool  `json:"testPassed,omitempty"`
}

type hkdf struct{}

func (k *hkdf) Process(vectorSet []byte, m Transactable) (any, error) {
	var parsed hkdfTestVectorSet
	if err := json.Unmarshal(vectorSet, &parsed); err != nil {
		return nil, err
	}

	var respGroups []hkdfTestGroupResponse
	for _, group := range parsed.Groups {
		group := group
		groupResp := hkdfTestGroupResponse{ID: group.ID}

		// determine the test type
		var isValidationTest bool
		switch group.Type {
		case "VAL":
			isValidationTest = true
		case "AFT":
			isValidationTest = false
		default:
			return nil, fmt.Errorf("unknown test type %q", group.Type)
		}

		// get the number of bytes to output and the hmac alg we're using
		outBytes, hashName, err := group.Config.extract()
		if err != nil {
			return nil, err
		}

		for _, test := range group.Tests {
			test := test
			testResp := hkdfTestResponse{ID: test.ID}

			key, salt, err := test.Params.extract()
			if err != nil {
				return nil, err
			}
			uData, err := test.PartyU.data()
			if err != nil {
				return nil, err
			}
			vData, err := test.PartyV.data()
			if err != nil {
				return nil, err
			}
			lenData := test.Params.data()

			var expected []byte
			if isValidationTest {
				expected, err = hex.DecodeString(test.ExpectedHex)
				if err != nil {
					return nil, err
				}
			}

			info := make([]byte, 0, len(uData)+len(vData)+len(lenData))
			info = append(info, uData...)
			info = append(info, vData...)
			info = append(info, lenData...)

			resp, err := m.Transact("KDA/HKDF/"+hashName, 1, key, salt, info, uint32le(outBytes))
			if err != nil {
				return nil, fmt.Errorf("KDA_HKDF operation failed: %s", err)
			}

			if isValidationTest {
				passed := bytes.Equal(expected, resp[0])
				testResp.Passed = &passed
			} else {
				testResp.KeyOut = hex.EncodeToString(resp[0])
			}

			groupResp.Tests = append(groupResp.Tests, testResp)
		}
		respGroups = append(respGroups, groupResp)
	}

	return respGroups, nil
}
