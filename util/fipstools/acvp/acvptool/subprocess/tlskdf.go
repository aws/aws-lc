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
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
)

type tlsKDFVectorSet struct {
	Mode   string            `json:"mode"`
	Groups []tlsKDFTestGroup `json:"testGroups"`
}

type tlsKDFTestGroup struct {
	ID    uint64       `json:"tgId"`
	Hash  string       `json:"hashAlg"`
	Tests []tlsKDFTest `json:"tests"`
	// Below values are unique to TLS Test Groups
	TLSVersion   string `json:"tlsVersion"`
	KeyBlockBits uint64 `json:"keyBlockLength"`
	PMSLength    uint64 `json:"preMasterSecretLength"`
	//Below values are unique to SSH Test Groups
	TestType string `json:"testType"`
	Cipher   string `json:"cipher"`
}

type tlsKDFTest struct {
	ID uint64 `json:"tcId"`
	// Below values are unique to TLS Test Groups
	PMSHex string `json:"preMasterSecret"`
	// ClientHelloRandomHex and ServerHelloRandomHex are used for deriving the
	// master secret. ClientRandomHex and ServerRandomHex are used for deriving the
	// key block. Having different values for these is not possible in a TLS
	// handshake unless you squint at a resumption handshake and somehow rederive
	// the master secret from the session information during resumption.
	ClientHelloRandomHex string `json:"clientHelloRandom"`
	ServerHelloRandomHex string `json:"serverHelloRandom"`
	ClientRandomHex      string `json:"clientRandom"`
	ServerRandomHex      string `json:"serverRandom"`
	SessionHashHex       string `json:"sessionHash"`
	// Below values are unique to SSH Test Groups
	SecretValHex string `json:"k"`
	HashValHex   string `json:"h"`
	SessionIdHex string `json:"sessionId"`
}

type tlsKDFTestGroupResponse struct {
	ID    uint64               `json:"tgId"`
	Tests []tlsKDFTestResponse `json:"tests"`
}

type tlsKDFTestResponse struct {
	ID uint64 `json:"tcId"`
	// Below values are unique to TLS Test Groups
	MasterSecretHex string `json:"masterSecret,omitempty"`
	KeyBlockHex     string `json:"keyBlock,omitempty"`
	// Below values are unique to SSH Test Groups
	InitialIvClientHex     string `json:"initialIvClient,omitempty"`
	InitialIvServerHex     string `json:"initialIvServer,omitempty"`
	EncryptionKeyClientHex string `json:"encryptionKeyClient,omitempty"`
	EncryptionKeyServerHex string `json:"encryptionKeyServer,omitempty"`
	IntegrityKeyClientHex  string `json:"integrityKeyClient,omitempty"`
	IntegritykeyServerHex  string `json:"integrityKeyServer,omitempty"`
}

type tlsKDF struct {
	algo string
}

var ivLenMap = map[string]uint32{
	"AES-128": 16,
	"AES-192": 16,
	"AES-256": 16,
	"TDES":    8,
}

var encyrptionKeyLenMap = map[string]uint32{
	"AES-128": 16,
	"AES-192": 24,
	"AES-256": 32,
	"TDES":    24,
}

var integrityKeyLenMap = map[string]uint32{
	"SHA-1":    20,
	"SHA2-224": 28,
	"SHA2-256": 32,
	"SHA2-384": 48,
	"SHA2-512": 64,
}

func ProcessHeader(mode string, k *tlsKDF, group tlsKDFTestGroup) (string, error) {
	var method string
	var err error

	if mode == "ssh" {
		method = "SSHKDF/" + group.Hash
		err = nil
	} else if mode == "tls" || mode == "KDF" {
		method, err = ProcessTLSHeader(k, group)
	}

	return method, err
}

func ProcessTLSHeader(k *tlsKDF, group tlsKDFTestGroup) (string, error) {
	var tlsVer string
	// See https://pages.nist.gov/ACVP/draft-celi-acvp-kdf-tls.html#name-supported-kdfs for differences between
	// kdf-components and TLS-v1.2
	switch k.algo {
	case "kdf-components":
		// kdf-components supports TLS 1.0, 1.1, and 1.2 tests
		switch group.TLSVersion {
		case "v1.0/1.1":
			tlsVer = "1.0"
		case "v1.2":
			tlsVer = "1.2"
		default:
			return "", fmt.Errorf("unknown TLS version %q", group.TLSVersion)
		}
	case "TLS-v1.2":
		// The new extended master secret (RFC7627) tests only support TLS 1.2 as the name implies
		tlsVer = "1.2"
	default:
		return "", fmt.Errorf("unknown algorithm %q", k.algo)
	}

	hashIsTLS10 := false
	switch group.Hash {
	case "SHA-1":
		hashIsTLS10 = true
	case "SHA2-256", "SHA2-384", "SHA2-512":
		break
	default:
		return "", fmt.Errorf("unknown hash %q", group.Hash)
	}

	if (tlsVer == "1.0") != hashIsTLS10 {
		return "", fmt.Errorf("hash %q not permitted with TLS version %q", group.Hash, group.TLSVersion)
	}

	if group.KeyBlockBits%8 != 0 {
		return "", fmt.Errorf("requested key-block length (%d bits) is not a whole number of bytes", group.KeyBlockBits)
	}

	method := "TLSKDF/" + tlsVer + "/" + group.Hash

	return method, nil
}

func HandleTLS(test tlsKDFTest, k *tlsKDF, m Transactable, method string, group tlsKDFTestGroup, response *tlsKDFTestGroupResponse) error {
	// See https://pages.nist.gov/ACVP/draft-celi-acvp-kdf-tls.html
	pms, err := hex.DecodeString(test.PMSHex)
	if err != nil {
		return err
	}

	clientHelloRandom, err := hex.DecodeString(test.ClientHelloRandomHex)
	if err != nil {
		return err
	}

	serverHelloRandom, err := hex.DecodeString(test.ServerHelloRandomHex)
	if err != nil {
		return err
	}

	clientRandom, err := hex.DecodeString(test.ClientRandomHex)
	if err != nil {
		return err
	}

	serverRandom, err := hex.DecodeString(test.ServerRandomHex)
	if err != nil {
		return err
	}

	sessionHash, err := hex.DecodeString(test.SessionHashHex)
	if err != nil {
		return err
	}

	const (
		masterSecretLength = 48
		masterSecretLabel  = "master secret"
		extendedLabel      = "extended master secret"
		keyBlockLabel      = "key expansion"
	)

	var outLenBytes [4]byte
	binary.LittleEndian.PutUint32(outLenBytes[:], uint32(masterSecretLength))
	var result [][]byte
	switch k.algo {
	case "kdf-components":
		result, err = m.Transact(method, 1, outLenBytes[:], pms, []byte(masterSecretLabel), clientHelloRandom, serverHelloRandom)
	case "TLS-v1.2":
		result, err = m.Transact(method, 1, outLenBytes[:], pms, []byte(extendedLabel), sessionHash, nil)
	default:
		return fmt.Errorf("unknown algorithm %q", k.algo)
	}
	if err != nil {
		return err
	}
	binary.LittleEndian.PutUint32(outLenBytes[:], uint32(group.KeyBlockBits/8))
	// TLS 1.0, 1.1, and 1.2 use a different order for the client and server
	// randoms when computing the key block.
	result2, err := m.Transact(method, 1, outLenBytes[:], result[0], []byte(keyBlockLabel), serverRandom, clientRandom)
	if err != nil {
		return err
	}

	response.Tests = append(response.Tests, tlsKDFTestResponse{
		ID:              test.ID,
		MasterSecretHex: hex.EncodeToString(result[0]),
		KeyBlockHex:     hex.EncodeToString(result2[0]),
	})

	return nil
}

func HandleSSH(test tlsKDFTest, k *tlsKDF, m Transactable, method string, group tlsKDFTestGroup, response *tlsKDFTestGroupResponse) error {
	// See https://pages.nist.gov/ACVP/draft-celi-acvp-kdf-ssh.html
	secretVal, err := hex.DecodeString(test.SecretValHex)
	if err != nil {
		return err
	}

	hashVal, err := hex.DecodeString(test.HashValHex)
	if err != nil {
		return err
	}

	sessionId, err := hex.DecodeString(test.SessionIdHex)
	if err != nil {
		return err
	}

	// NIST SP 800-135 says that the lengths of the IVs and encryption keys are determined by the supported block ciphers
	// We can look at https://github.com/usnistgov/ACVP-Server/blob/master/gen-val/json-files/kdf-components-ssh-1.0/internalProjection.json
	// to determine what these lengths are
	ivLen := ivLenMap[group.Cipher]
	encyrptionKeyLen := encyrptionKeyLenMap[group.Cipher]
	integrityKeyLen := integrityKeyLenMap[group.Hash]

	// Definitions for last argument of Transact() can be found in aws-lc/include/openssl/sshkdf.h
	initialIvClient, err := m.Transact(method, 1,
		secretVal, hashVal, sessionId,
		uint32le(65), uint32le(ivLen))
	if err != nil {
		return err
	}

	initialIvServer, err := m.Transact(method, 1,
		secretVal, hashVal, sessionId,
		uint32le(66), uint32le(ivLen))
	if err != nil {
		return err
	}

	encryptionKeyClient, err := m.Transact(method, 1,
		secretVal, hashVal, sessionId,
		uint32le(67), uint32le(encyrptionKeyLen))
	if err != nil {
		return err
	}

	encryptionKeyServer, err := m.Transact(method, 1,
		secretVal, hashVal, sessionId,
		uint32le(68), uint32le(encyrptionKeyLen))
	if err != nil {
		return err
	}

	integrityKeyClient, err := m.Transact(method, 1,
		secretVal, hashVal, sessionId,
		uint32le(69), uint32le(integrityKeyLen))
	if err != nil {
		return err
	}

	integrityKeyServer, err := m.Transact(method, 1,
		secretVal, hashVal, sessionId,
		uint32le(70), uint32le(integrityKeyLen))
	if err != nil {
		return err
	}

	response.Tests = append(response.Tests, tlsKDFTestResponse{
		ID:                     test.ID,
		InitialIvClientHex:     hex.EncodeToString(initialIvClient[0]),
		InitialIvServerHex:     hex.EncodeToString(initialIvServer[0]),
		EncryptionKeyClientHex: hex.EncodeToString(encryptionKeyClient[0]),
		EncryptionKeyServerHex: hex.EncodeToString(encryptionKeyServer[0]),
		IntegrityKeyClientHex:  hex.EncodeToString(integrityKeyClient[0]),
		IntegritykeyServerHex:  hex.EncodeToString(integrityKeyServer[0]),
	})

	return nil
}

func (k *tlsKDF) Process(vectorSet []byte, m Transactable) (interface{}, error) {
	var parsed tlsKDFVectorSet
	if err := json.Unmarshal(vectorSet, &parsed); err != nil {
		return nil, err
	}

	// See https://pages.nist.gov/ACVP/draft-celi-acvp-kdf-tls.html
	var ret []tlsKDFTestGroupResponse
	for _, group := range parsed.Groups {
		response := tlsKDFTestGroupResponse{
			ID: group.ID,
		}

		method, err := ProcessHeader(parsed.Mode, k, group)
		if err != nil {
			return nil, err
		}

		for _, test := range group.Tests {
			if parsed.Mode == "ssh" {
				err = HandleSSH(test, k, m, method, group, &response)
			} else if parsed.Mode == "tls" || parsed.Mode == "KDF" {
				err = HandleTLS(test, k, m, method, group, &response)
			}

			if err != nil {
				return nil, err
			}
		}

		ret = append(ret, response)
	}

	return ret, nil
}
