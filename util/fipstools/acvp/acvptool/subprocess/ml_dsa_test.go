// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package subprocess

import (
	"reflect"
	"testing"
)

func TestMlDsaExternalMuJSONTags(t *testing.T) {
	for _, group := range []any{
		mlDsaSigGenTestGroup{},
		mlDsaSigVerTestGroup{},
	} {
		field, ok := reflect.TypeOf(group).FieldByName("ExternalMu")
		if !ok {
			t.Fatalf("%T has no ExternalMu field", group)
		}
		if got, want := field.Tag.Get("json"), "externalMu"; got != want {
			t.Errorf("%T ExternalMu JSON tag = %q, want %q", group, got, want)
		}
	}
}
