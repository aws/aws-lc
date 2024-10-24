// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package subprocess

import (
	"bytes"
	"encoding/json"
	"fmt"
	"strings"
)

// Processes Vectors defined by https://pages.nist.gov/ACVP/draft-hammett-acvp-kas-kdf-onestep.html
type kdaOneStepMode struct{}

func (k *kdaOneStepMode) ProcessKDA(vectorSet []byte, m Transactable) (interface{}, error) {
	var parsed kdaOneStepTestVectorSet

	if err := json.Unmarshal(vectorSet, &parsed); err != nil {
		return nil, err
	}

	var respGroups []kdaOneStepTestGroupResponse
	for _, group := range parsed.Groups {
		group := group
		groupResp := kdaOneStepTestGroupResponse{ID: group.ID}

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

		// get the number of bytes to output and the auxillary function we're using
		outBytes, auxFunctionName, auxFuncType, err := group.Configuration.extract()
		if err != nil {
			return nil, err
		}

		for _, test := range group.Tests {
			test := test
			testResp := kdaOneStepTestCaseResponse{ID: test.ID}

			info := test.fixedInfoBytes()

			var args [][]byte

			args = append(args, test.KDFParameter.Z)
			if auxFuncType == hmacAuxFunction {
				args = append(args, test.KDFParameter.Salt)
			}
			args = append(args, info)
			args = append(args, uint32le(outBytes))

			resp, err := m.Transact("KDA/OneStep/"+auxFunctionName, 1, args...)
			if err != nil {
				return nil, fmt.Errorf("KDA_OneStep operation failed: %s", err)
			}

			if isValidationTest {
				passed := bytes.Equal(test.DerivedKeyMaterial, resp[0])
				testResp.Passed = &passed
			} else {
				testResp.DerivedKeyMaterial = resp[0]
			}

			groupResp.Tests = append(groupResp.Tests, testResp)
		}
		respGroups = append(respGroups, groupResp)

	}

	return respGroups, nil
}

type kdaOneStepTestVectorSet struct {
	Groups []kdaOneStepTestGroup `json:"testGroups"`
}

type kdaOneStepTestGroup struct {
	ID            uint64                  `json:"tgId"`
	Type          string                  `json:"testType"`
	Configuration kdaOneStepConfiguration `json:"kdfConfiguration"`
	Tests         []kdaOneStepTest        `json:"tests"`
}

type kdaOneStepConfiguration struct {
	Type              string `json:"kdfType"`
	SaltMethod        string `json:"saltMethod"`
	FixedInfoPattern  string `json:"fixedInfoPattern"`
	FixedInfoEncoding string `json:"fixedInfoEncoding"`
	AuxFunction       string `json:"auxFunction"`
	L                 uint32 `json:"l"`
}

func (k *kdaOneStepConfiguration) extract() (outLen uint32, auxFunction string, auxFuncType auxFunctionType, err error) {
	if k.Type != "oneStep" {
		return 0, "", unknownAuxFunction, fmt.Errorf("unexpected kdfType: %v", k.Type)
	}

	auxFuncType.setFromString(k.AuxFunction)

	if auxFuncType == unknownAuxFunction {
		return 0, "", unknownAuxFunction, fmt.Errorf("unknown auxillary function: %v", k.AuxFunction)
	}

	if k.FixedInfoPattern != "uPartyInfo||vPartyInfo" || k.FixedInfoEncoding != "concatenation" {
		return 0, "", unknownAuxFunction, fmt.Errorf("unsupported FixedInfo construction, pattern(%v) with encoding(%v)", k.FixedInfoPattern, k.FixedInfoEncoding)
	}

	return k.L / 8, k.AuxFunction, auxFuncType, nil
}

type kdaOneStepTest struct {
	ID           uint64 `json:"tcId"`
	KDFParameter struct {
		Type string               `json:"kdfType"`
		Salt hexEncodedByteString `json:"salt,omitempty"`
		Z    hexEncodedByteString `json:"z"`
	} `json:"kdfParameter"`
	FixedInfoPartyU    kdaOneStepFixedInfoParty `json:"fixedInfoPartyU"`
	FixedInfoPartyV    kdaOneStepFixedInfoParty `json:"fixedInfoPartyV"`
	DerivedKeyMaterial hexEncodedByteString     `json:"dkm,omitempty"`
}

func (k *kdaOneStepTest) fixedInfoBytes() []byte {
	uBytes := k.FixedInfoPartyU.concatenatedBytes()
	vBytes := k.FixedInfoPartyV.concatenatedBytes()
	v := make([]byte, 0, len(uBytes)+len(vBytes))
	v = append(v, uBytes...)
	v = append(v, vBytes...)
	return v
}

type kdaOneStepFixedInfoParty struct {
	PartyID       hexEncodedByteString `json:"partyId"`
	EphemeralData hexEncodedByteString `json:"ephemeralData"`
}

func (k *kdaOneStepFixedInfoParty) concatenatedBytes() []byte {
	v := make([]byte, 0, len(k.PartyID)+len(k.EphemeralData))
	v = append(v, k.PartyID...)
	v = append(v, k.EphemeralData...)
	return v
}

type kdaOneStepTestGroupResponse struct {
	ID    uint64                       `json:"tgId"`
	Tests []kdaOneStepTestCaseResponse `json:"tests"`
}

type kdaOneStepTestCaseResponse struct {
	ID                 uint64               `json:"tcId"`
	Passed             *bool                `json:"testPassed,omitempty"`
	DerivedKeyMaterial hexEncodedByteString `json:"dkm,omitempty"`
}

type auxFunctionType uint

func (a *auxFunctionType) setFromString(v string) {
	if strings.HasPrefix(v, "HMAC-") {
		*a = hmacAuxFunction
	} else if strings.HasPrefix(v, "SHA-") || strings.HasPrefix(v, "SHA2-") || strings.HasPrefix(v, "SHA3-") {
		*a = digestAuxFunction
	} else {
		*a = unknownAuxFunction
	}
}

const (
	unknownAuxFunction auxFunctionType = iota
	digestAuxFunction
	hmacAuxFunction
)
