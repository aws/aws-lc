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
	ID             uint64                          `json:"tgId"`
	Type           string                          `json:"testType"` // AFT or VAL
	Config         hkdfConfiguration               `json:"kdfConfiguration"`
	MultiExpansion bool                            `json:"multiExpansion"`
	MultiConfig    hkdfMultiExpansionConfiguration `json:"kdfMultiExpansionConfiguration"`
	Tests          []hkdfTest                      `json:"tests"`
}

type hkdfTest struct {
	ID              uint64                       `json:"tcId"`
	Params          hkdfParameters               `json:"kdfParameter"`
	MultiParams     hkdfMultiExpansionParameters `json:"kdfMultiExpansionParameter"`
	PartyU          hkdfPartyInfo                `json:"fixedInfoPartyU"`
	PartyV          hkdfPartyInfo                `json:"fixedInfoPartyV"`
	ExpectedHex     string                       `json:"dkm"`
	ExpectedDkmsHex []string                     `json:"dkms"`
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

type hkdfMultiExpansionConfiguration struct {
	Type       string `json:"kdfType"`
	SaltMethod string `json:"saltMethod"`
	SaltLength uint64 `json:"saltLen"`
	HmacAlg    string `json:"hmacAlg"`
	OutputBits uint32 `json:"l"`
}

func (c *hkdfMultiExpansionConfiguration) extract() (hashName string, err error) {
	if c.Type != "hkdf" ||
		(c.SaltMethod != "default" && c.SaltMethod != "random") {
		return "", fmt.Errorf("Test group not configured for KDA HKDF multi-expansion")
	}
	return c.HmacAlg, nil
}

type hkdfMultiExpansionParameters struct {
	KdfType             string                          `json:"kdfType"`
	KeyHex              string                          `json:"z"`
	HmacAlg             string                          `json:"hmacAlg"`
	SaltHex             string                          `json:"salt"`
	IterationParameters []hkdfMultiExpansionIteration   `json:"iterationParameters"`
}

type hkdfMultiExpansionIteration struct {
	OutputBits   uint32 `json:"l"`
	FixedInfoHex string `json:"fixedInfo"`
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
	ID     uint64   `json:"tcId"`
	KeyOut string   `json:"dkm,omitempty"`
	KeyOuts []string `json:"dkms,omitempty"`
	Passed *bool    `json:"testPassed,omitempty"`
}

type kdaHkdfMode struct{}

func (k *kdaHkdfMode) ProcessKDA(vectorSet []byte, m Transactable) (interface{}, error) {
	var parsed hkdfTestVectorSet
	if err := json.Unmarshal(vectorSet, &parsed); err != nil {
		return nil, err
	}

	var respGroups []hkdfTestGroupResponse
	for _, group := range parsed.Groups {
		group := group
		groupResp := hkdfTestGroupResponse{ID: group.ID}

		if group.MultiExpansion {
			if err := processMultiExpansionGroup(&group, &groupResp, m); err != nil {
				return nil, err
			}
		} else {
			if err := processSingleExpansionGroup(&group, &groupResp, m); err != nil {
				return nil, err
			}
		}

		respGroups = append(respGroups, groupResp)
	}

	return respGroups, nil
}

func processSingleExpansionGroup(group *hkdfTestGroup, groupResp *hkdfTestGroupResponse, m Transactable) error {
	// determine the test type
	var isValidationTest bool
	switch group.Type {
	case "VAL":
		isValidationTest = true
	case "AFT":
		isValidationTest = false
	default:
		return fmt.Errorf("unknown test type %q", group.Type)
	}

	// get the number of bytes to output and the hmac alg we're using
	outBytes, hashName, err := group.Config.extract()
	if err != nil {
		return err
	}

	for _, test := range group.Tests {
		test := test
		testResp := hkdfTestResponse{ID: test.ID}

		key, salt, err := test.Params.extract()
		if err != nil {
			return err
		}
		uData, err := test.PartyU.data()
		if err != nil {
			return err
		}
		vData, err := test.PartyV.data()
		if err != nil {
			return err
		}
		lenData := test.Params.data()

		var expected []byte
		if isValidationTest {
			expected, err = hex.DecodeString(test.ExpectedHex)
			if err != nil {
				return err
			}
		}

		info := make([]byte, 0, len(uData)+len(vData)+len(lenData))
		info = append(info, uData...)
		info = append(info, vData...)
		info = append(info, lenData...)

		resp, err := m.Transact("KDA/HKDF/"+hashName, 1, key, salt, info, uint32le(outBytes))
		if err != nil {
			return fmt.Errorf("KDA_HKDF operation failed: %s", err)
		}

		if isValidationTest {
			passed := bytes.Equal(expected, resp[0])
			testResp.Passed = &passed
		} else {
			testResp.KeyOut = hex.EncodeToString(resp[0])
		}

		groupResp.Tests = append(groupResp.Tests, testResp)
	}

	return nil
}

func processMultiExpansionGroup(group *hkdfTestGroup, groupResp *hkdfTestGroupResponse, m Transactable) error {
	// Multi-expansion supports both AFT and VAL
	var isValidationTest bool
	switch group.Type {
	case "VAL":
		isValidationTest = true
	case "AFT":
		isValidationTest = false
	default:
		return fmt.Errorf("unsupported test type %q for multi-expansion", group.Type)
	}

	hashName, err := group.MultiConfig.extract()
	if err != nil {
		return err
	}

	for _, test := range group.Tests {
		test := test
		testResp := hkdfTestResponse{ID: test.ID}

		// Decode z (shared secret) and salt
		z, err := hex.DecodeString(test.MultiParams.KeyHex)
		if err != nil {
			return fmt.Errorf("tcId %d: failed to decode z: %s", test.ID, err)
		}
		salt, err := hex.DecodeString(test.MultiParams.SaltHex)
		if err != nil {
			return fmt.Errorf("tcId %d: failed to decode salt: %s", test.ID, err)
		}

		// Step 1: Extract — PRK = HKDF-Extract(salt, z)
		extractResp, err := m.Transact("HKDF/"+hashName+"/extract", 1, z, salt)
		if err != nil {
			return fmt.Errorf("tcId %d: HKDF extract failed: %s", test.ID, err)
		}
		prk := extractResp[0]

		// Step 2: Expand — for each iteration, derive a key
		dkms := make([]string, 0, len(test.MultiParams.IterationParameters))
		for i, iter := range test.MultiParams.IterationParameters {
			if iter.OutputBits%8 != 0 {
				return fmt.Errorf("tcId %d, iteration %d: output bits %d not a multiple of 8", test.ID, i, iter.OutputBits)
			}
			outBytes := iter.OutputBits / 8

			fixedInfo, err := hex.DecodeString(iter.FixedInfoHex)
			if err != nil {
				return fmt.Errorf("tcId %d, iteration %d: failed to decode fixedInfo: %s", test.ID, i, err)
			}

			expandResp, err := m.Transact("HKDF/"+hashName+"/expand", 1, uint32le(outBytes), prk, fixedInfo)
			if err != nil {
				return fmt.Errorf("tcId %d, iteration %d: HKDF expand failed: %s", test.ID, i, err)
			}

			dkms = append(dkms, strings.ToUpper(hex.EncodeToString(expandResp[0])))
		}

		if isValidationTest {
			// Compare computed dkms against expected
			passed := len(dkms) == len(test.ExpectedDkmsHex)
			if passed {
				for i := range dkms {
					if !strings.EqualFold(dkms[i], test.ExpectedDkmsHex[i]) {
						passed = false
						break
					}
				}
			}
			testResp.Passed = &passed
		} else {
			testResp.KeyOuts = dkms
		}

		groupResp.Tests = append(groupResp.Tests, testResp)
	}

	return nil
}
