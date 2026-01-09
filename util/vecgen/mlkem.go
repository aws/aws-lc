package main

import (
	"encoding/hex"
	"fmt"

	"github.com/cloudflare/circl/kem"
	"github.com/cloudflare/circl/kem/schemes"
)

type MLKEMParams struct {
	Name   string
	Scheme kem.Scheme
}

func (p *MLKEMParams) EKLen() int { return p.Scheme.PublicKeySize() }
func (p *MLKEMParams) DKLen() int { return p.Scheme.PrivateKeySize() }
func (p *MLKEMParams) CTLen() int { return p.Scheme.CiphertextSize() }

var mlkemParams = []MLKEMParams{
	{Name: "ML-KEM-512"},
	{Name: "ML-KEM-768"},
	{Name: "ML-KEM-1024"},
}

// MLKEMDecapsTestVector represents a single ML-KEM decapsulation test case
type MLKEMDecapsTestVector struct {
	TcID    int      `json:"tcId"`
	Comment string   `json:"comment"`
	DK      string   `json:"dk"`
	C       string   `json:"c"`
	Result  string   `json:"result"`
	Flags   []string `json:"flags"`
}

// generateValidKeyPair generates a valid ML-KEM key pair using a fixed seed for reproducibility
func generateValidKeyPair(params *MLKEMParams) (kem.PrivateKey, kem.PublicKey) {
	seed := generateReproducibleSeed(params.Scheme.SeedSize())
	pk, sk := params.Scheme.DeriveKeyPair(seed)
	return sk, pk
}

// generateValidCiphertext generates a valid ciphertext for a given encapsulation key
func generateValidCiphertext(params *MLKEMParams, pk kem.PublicKey) []byte {
	seed := generateReproducibleSeed(params.Scheme.EncapsulationSeedSize())
	ct, _, err := params.Scheme.EncapsulateDeterministically(pk, seed)
	if err != nil {
		panic(fmt.Sprintf("Failed to encapsulate: %v", err))
	}
	return ct
}

// corruptDKHash corrupts the hash portion of a decapsulation key
func corruptDKHash(params *MLKEMParams, dkBytes []byte) []byte {
	corrupted := make([]byte, len(dkBytes))
	copy(corrupted, dkBytes)
	// Hash is at bytes [dkPKE_len + ekLen : dkPKE_len + ekLen + 32]
	//
	// dkPKE_len = len(ByteEncode12) + len(rho)
	//           = ekPKE_len + 32
	//           = ekLen + 32
	//
	// https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf#algorithm.16
	// https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf#algorithm.13
	//
	// For ML-KEM-512: [768+800:768+800+32] = [1568:1600]
	ekLen := params.EKLen()
	dkPKELen := ekLen - 32
	hashStart := dkPKELen + ekLen
	corrupted[hashStart] ^= 0x01 // Flip one bit in the hash
	return corrupted
}

// corruptDKEmbeddedEK corrupts the embedded ek
func corruptDKEmbeddedEK(params *MLKEMParams, dkBytes []byte) []byte {
	corrupted := make([]byte, len(dkBytes))
	copy(corrupted, dkBytes)

	// Corrupt the embedded ek at bytes [dkPKE_len : dkPKE_len + ekLen]
	// https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf#algorithm.16
	ekLen := params.EKLen()
	dkPKELen := ekLen - 32
	ekStart := dkPKELen
	corrupted[ekStart] ^= 0xFF // Flip first byte of embedded ek

	return corrupted
}

// generateMLKEMDecapsTestVectors generates test vectors for a specific ML-KEM parameter set
func generateMLKEMDecapsTestVectors(params *MLKEMParams) []MLKEMDecapsTestVector {
	tests := []MLKEMDecapsTestVector{}
	tcID := 1

	// Generate one honest key pair for all tests
	sk, pk := generateValidKeyPair(params)
	skBytes, err := sk.MarshalBinary()
	if err != nil {
		panic(fmt.Sprintf("Failed to marshal private key: %v", err))
	}

	// Generate one valid ciphertext
	validCT := generateValidCiphertext(params, pk)

	// Valid test case
	tests = append(tests, MLKEMDecapsTestVector{
		TcID:    tcID,
		Comment: "Valid decapsulation key and ciphertext",
		DK:      hex.EncodeToString(skBytes),
		C:       hex.EncodeToString(validCT),
		Result:  "valid",
		Flags:   []string{},
	})
	tcID++

	// Test Class 1: Invalid ciphertext length
	// FIPS 203 Section 7.3 - Check 1: |c| = 32(du*k + dv)

	ctLen := params.CTLen()
	dkLen := params.DKLen()

	// Ciphertext too short by 1 byte
	ctShort := make([]byte, ctLen-1)
	copy(ctShort, validCT[:ctLen-1])
	tests = append(tests, MLKEMDecapsTestVector{
		TcID:    tcID,
		Comment: fmt.Sprintf("Ciphertext too short (%d bytes instead of %d)", ctLen-1, ctLen),
		DK:      hex.EncodeToString(skBytes),
		C:       hex.EncodeToString(ctShort),
		Result:  "invalid",
		Flags:   []string{"IncorrectCiphertextLength"},
	})
	tcID++

	// Ciphertext too long by 1 byte
	ctLong := make([]byte, ctLen+1)
	copy(ctLong, validCT)
	tests = append(tests, MLKEMDecapsTestVector{
		TcID:    tcID,
		Comment: fmt.Sprintf("Ciphertext too long (%d bytes instead of %d)", ctLen+1, ctLen),
		DK:      hex.EncodeToString(skBytes),
		C:       hex.EncodeToString(ctLong),
		Result:  "invalid",
		Flags:   []string{"IncorrectCiphertextLength"},
	})
	tcID++

	// Test Class 2: Invalid decapsulation key length
	// FIPS 203 Section 7.3 - Check 2: |dk| = 768k + 96

	// Decapsulation key too short by 1 byte
	skShort := skBytes[:dkLen-1]
	tests = append(tests, MLKEMDecapsTestVector{
		TcID:    tcID,
		Comment: fmt.Sprintf("Decapsulation key too short (%d bytes instead of %d)", dkLen-1, dkLen),
		DK:      hex.EncodeToString(skShort),
		C:       hex.EncodeToString(validCT),
		Result:  "invalid",
		Flags:   []string{"IncorrectDecapsulationKeyLength"},
	})
	tcID++

	// Decapsulation key too long by 1 byte
	skLong := make([]byte, dkLen+1)
	copy(skLong, skBytes)
	tests = append(tests, MLKEMDecapsTestVector{
		TcID:    tcID,
		Comment: fmt.Sprintf("Decapsulation key too long (%d bytes instead of %d)", dkLen+1, dkLen),
		DK:      hex.EncodeToString(skLong),
		C:       hex.EncodeToString(validCT),
		Result:  "invalid",
		Flags:   []string{"IncorrectDecapsulationKeyLength"},
	})
	tcID++

	// Test Class 3: Invalid decapsulation key
	// FIPS 203 Section 7.3 - Check 3: check the embedded hash

	// Corrupt the hash in the decapsulation key
	skCorruptedHash := corruptDKHash(params, skBytes)
	tests = append(tests, MLKEMDecapsTestVector{
		TcID:    tcID,
		Comment: "Decapsulation key with corrupted hash",
		DK:      hex.EncodeToString(skCorruptedHash),
		C:       hex.EncodeToString(validCT),
		Result:  "invalid",
		Flags:   []string{"InvalidDecapsulationKey"},
	})
	tcID++

	// Corrupt the embedded ek in the decapsulation key
	skCorruptedEK := corruptDKEmbeddedEK(params, skBytes)
	tests = append(tests, MLKEMDecapsTestVector{
		TcID:    tcID,
		Comment: "Decapsulation key with corrupted embedded encapsulation key",
		DK:      hex.EncodeToString(skCorruptedEK),
		C:       hex.EncodeToString(validCT),
		Result:  "invalid",
		Flags:   []string{"InvalidDecapsulationKey"},
	})
	tcID++

	return tests
}

// initializeMLKEMSchemes initializes all ML-KEM schemes
func initializeMLKEMSchemes() {
	for i := range mlkemParams {
		mlkemParams[i].Scheme = schemes.ByName(mlkemParams[i].Name)
		if mlkemParams[i].Scheme == nil {
			panic(fmt.Sprintf("%s scheme not found", mlkemParams[i].Name))
		}
	}
}

// generateMLKEMDecapsVectors generates ML-KEM decapsulation validation test vectors
// Returns a map of filename -> test data
func generateMLKEMDecapsVectors() map[string]TestData[MLKEMDecapsTestVector] {
	// Initialize all ML-KEM schemes
	initializeMLKEMSchemes()

	testData := make(map[string]TestData[MLKEMDecapsTestVector])

	// Generate test vectors for each parameter set
	for _, params := range mlkemParams {
		tests := generateMLKEMDecapsTestVectors(&params)

		// Convert ML-KEM-512 -> mlkem_512
		filePrefix := fmt.Sprintf("mlkem_%s", params.Name[7:]) // Extract "512", "768", or "1024"
		filename := fmt.Sprintf("%s_semi_expanded_decaps_test.json", filePrefix)
		
		testData[filename] = TestData[MLKEMDecapsTestVector]{
			ParameterSet: params.Name,
			Type:         "MLKEMDecapsValidationTest",
			Notes: map[string]any{
				"IncorrectCiphertextLength": map[string]string{
					"bugType":     "BASIC",
					"description": "The ciphertext has incorrect length.",
				},
				"IncorrectDecapsulationKeyLength": map[string]string{
					"bugType":     "BASIC",
					"description": "The decapsulation key has incorrect length.",
				},
				"InvalidDecapsulationKey": map[string]string{
					"bugType":     "BASIC",
					"description": "The decapsulation key is invalid.",
				},
			},
			Tests: tests,
		}
	}
	
	return testData
}
