// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package subprocess

import "testing"

type hashTestTransactable struct {
	called bool
	args   [][]byte
}

func (m *hashTestTransactable) Transact(_ string, _ int, args ...[]byte) ([][]byte, error) {
	m.called = true
	m.args = args
	return [][]byte{{}}, nil
}

func (*hashTestTransactable) TransactAsync(_ string, _ int, _ [][]byte, _ func([][]byte) error) {
	panic("unexpected asynchronous transaction")
}

func (*hashTestTransactable) Barrier(_ func()) error {
	panic("unexpected barrier")
}

func (*hashTestTransactable) Flush() error {
	panic("unexpected flush")
}

func TestHashPrimitiveRejectsOversizedSHAKEOutput(t *testing.T) {
	vectorSet := []byte(`{
		"testGroups": [{
			"tgId": 1,
			"testType": "AFT",
			"tests": [{
				"tcId": 1,
				"len": 8,
				"msg": "ab",
				"outLen": 65544
			}]
		}]
	}`)
	transactable := &hashTestTransactable{}

	if _, err := (&hashPrimitive{algo: "SHAKE-128", size: -1}).Process(vectorSet, transactable); err == nil {
		t.Fatal("oversized SHAKE output length was accepted")
	}
	if transactable.called {
		t.Fatal("oversized SHAKE output length was sent to modulewrapper")
	}
}

func TestHashPrimitiveAcceptsMaximumSHAKEOutput(t *testing.T) {
	vectorSet := []byte(`{
		"testGroups": [{
			"tgId": 1,
			"testType": "AFT",
			"tests": [{
				"tcId": 1,
				"len": 8,
				"msg": "ab",
				"outLen": 65536
			}]
		}]
	}`)
	transactable := &hashTestTransactable{}

	if _, err := (&hashPrimitive{algo: "SHAKE-128", size: -1}).Process(vectorSet, transactable); err != nil {
		t.Fatalf("maximum SHAKE output length was rejected: %v", err)
	}
	if !transactable.called {
		t.Fatal("maximum SHAKE output length was not sent to modulewrapper")
	}
	if len(transactable.args) != 2 || len(transactable.args[1]) != 4 {
		t.Fatalf("unexpected SHAKE arguments: %#v", transactable.args)
	}
	if got, want := NativeEndian.Uint32(transactable.args[1]), uint32(8192); got != want {
		t.Fatalf("output length sent to modulewrapper = %d bytes, want %d", got, want)
	}
}
