// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
package subprocess

import (
	"encoding/json"
	"fmt"
)

type kdaPrimitive struct {
	modes map[string]kdaModePrimitive
}

type kdaModePrimitive interface {
	ProcessKDA(vectorSet []byte, t Transactable) (interface{}, error)
}

func (k *kdaPrimitive) Process(vectorSet []byte, t Transactable) (interface{}, error) {
	var partial struct {
		Mode string `json:"mode"`
	}

	if err := json.Unmarshal(vectorSet, &partial); err != nil {
		return nil, err
	}

	prim, ok := k.modes[partial.Mode]
	if !ok {
		return nil, fmt.Errorf("unsupported KDA mode(%v)", partial.Mode)
	}

	return prim.ProcessKDA(vectorSet, t)
}
