// Copyright (c) 2020, Google Inc.
// SPDX-License-Identifier: ISC

//go:build ignore

package main

import (
	"bytes"
	"crypto/elliptic"
	"fmt"
	"io"
	"math"
	"math/big"
	"os"
	"strings"
)

func main() {
	if err := writeBuiltinCurves("builtin_curves.h"); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing builtin_curves.h: %s\n", err)
		os.Exit(1)
	}

	if err := writeP256NistzTable("p256-nistz-table.h"); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing p256-nistz-table.h: %s\n", err)
		os.Exit(1)
	}

	if err := writeP256Table("p256_table.h"); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing p256_table.h: %s\n", err)
		os.Exit(1)
	}

	if err := writeP384Table("p384_table.h"); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing p384_table.h: %s\n", err)
		os.Exit(1)
	}

	if err := writeP521Table("p521_table.h"); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing p521_table.h: %s\n", err)
		os.Exit(1)
	}
}

func bigFromHex(s string) *big.Int {
	b, ok := new(big.Int).SetString(s, 16)
	if !ok {
		panic("crypto/elliptic: internal error: invalid encoding")
	}
	return b
}

type secp256k1 struct {
	// Cheating the interface implementation: just embed the definition
	// as we don't need to implement all the other functions for this tool.
	elliptic.Curve
}

// Params is the only function we care about
func (*secp256k1) Params() *elliptic.CurveParams {
	return &elliptic.CurveParams{
		Name:    "secp256k1",
		BitSize: 256,
		// FIPS 186-4, section D.1.2.2
		P:  bigFromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
		N:  bigFromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
		B:  bigFromHex("0000000000000000000000000000000000000000000000000000000000000007"),
		Gx: bigFromHex("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
		Gy: bigFromHex("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
	}
}

// SECP256K1 is a helper function that returns a new copy of the curve behind the interface
func SECP256K1() elliptic.Curve {
	return &secp256k1{}
}

// curveWithA wraps an elliptic.Curve and adds an A coefficient field.
// The standard Go elliptic.CurveParams only has P, N, B, Gx, Gy (assuming a = -3).
// Brainpool curves have arbitrary a values, so we need to carry them separately.
type curveWithA struct {
	elliptic.Curve
	A *big.Int
}

type brainpoolP224r1 struct{ elliptic.Curve }

func (*brainpoolP224r1) Params() *elliptic.CurveParams {
	// RFC 5639, Section 3.3 — brainpoolP224r1
	// https://datatracker.ietf.org/doc/html/rfc5639#section-3.3
	return &elliptic.CurveParams{
		Name:    "brainpoolP224r1",
		BitSize: 224,
		P:  bigFromHex("D7C134AA264366862A18302575D1D787B09F075797DA89F57EC8C0FF"), // p (field prime)
		N:  bigFromHex("D7C134AA264366862A18302575D0FB98D116BC4B6DDEBCA3A5A7939F"), // q (group order)
		B:  bigFromHex("2580F63CCFE44138870713B1A92369E33E2135D266DBB372386C400B"), // B (curve coefficient)
		Gx: bigFromHex("0D9029AD2C7E5CF4340823B2A87DC68C9E4CE3174C1E6EFDEE12C07D"), // x (generator)
		Gy: bigFromHex("58AA56F772C0726F24C6B89E4ECDAC24354B9E99CAA3F6D3761402CD"), // y (generator)
	}
}

func BrainpoolP224r1() *curveWithA {
	return &curveWithA{
		Curve: &brainpoolP224r1{},
		// RFC 5639, Section 3.3 — A (curve coefficient)
		A: bigFromHex("68A5E62CA9CE6C1C299803A6C1530B514E182AD8B0042A59CAD29F43"),
	}
}

type brainpoolP256r1 struct{ elliptic.Curve }

func (*brainpoolP256r1) Params() *elliptic.CurveParams {
	// RFC 5639, Section 3.4 — brainpoolP256r1
	// https://datatracker.ietf.org/doc/html/rfc5639#section-3.4
	return &elliptic.CurveParams{
		Name:    "brainpoolP256r1",
		BitSize: 256,
		P:  bigFromHex("A9FB57DBA1EEA9BC3E660A909D838D726E3BF623D52620282013481D1F6E5377"), // p (field prime)
		N:  bigFromHex("A9FB57DBA1EEA9BC3E660A909D838D718C397AA3B561A6F7901E0E82974856A7"), // q (group order)
		B:  bigFromHex("26DC5C6CE94A4B44F330B5D9BBD77CBF958416295CF7E1CE6BCCDC18FF8C07B6"), // B (curve coefficient)
		Gx: bigFromHex("8BD2AEB9CB7E57CB2C4B482FFC81B7AFB9DE27E1E3BD23C23A4453BD9ACE3262"), // x (generator)
		Gy: bigFromHex("547EF835C3DAC4FD97F8461A14611DC9C27745132DED8E545C1D54C72F046997"), // y (generator)
	}
}

func BrainpoolP256r1() *curveWithA {
	return &curveWithA{
		Curve: &brainpoolP256r1{},
		// RFC 5639, Section 3.4 — A (curve coefficient)
		A: bigFromHex("7D5A0975FC2C3057EEF67530417AFFE7FB8055C126DC5C6CE94A4B44F330B5D9"),
	}
}

type brainpoolP320r1 struct{ elliptic.Curve }

func (*brainpoolP320r1) Params() *elliptic.CurveParams {
	// RFC 5639, Section 3.5 — brainpoolP320r1
	// https://datatracker.ietf.org/doc/html/rfc5639#section-3.5
	return &elliptic.CurveParams{
		Name:    "brainpoolP320r1",
		BitSize: 320,
		P:  bigFromHex("D35E472036BC4FB7E13C785ED201E065F98FCFA6F6F40DEF4F92B9EC7893EC28FCD412B1F1B32E27"), // p
		N:  bigFromHex("D35E472036BC4FB7E13C785ED201E065F98FCFA5B68F12A32D482EC7EE8658E98691555B44C59311"), // q
		B:  bigFromHex("520883949DFDBC42D3AD198640688A6FE13F41349554B49ACC31DCCD884539816F5EB4AC8FB1F1A6"), // B
		Gx: bigFromHex("43BD7E9AFB53D8B85289BCC48EE5BFE6F20137D10A087EB6E7871E2A10A599C710AF8D0D39E20611"), // x
		Gy: bigFromHex("14FDD05545EC1CC8AB4093247F77275E0743FFED117182EAA9C77877AAAC6AC7D35245D1692E8EE1"), // y
	}
}

func BrainpoolP320r1() *curveWithA {
	return &curveWithA{
		Curve: &brainpoolP320r1{},
		// RFC 5639, Section 3.5 — A (curve coefficient)
		A: bigFromHex("3EE30B568FBAB0F883CCEBD46D3F3BB8A2A73513F5EB79DA66190EB085FFA9F492F375A97D860EB4"),
	}
}

type brainpoolP384r1 struct{ elliptic.Curve }

func (*brainpoolP384r1) Params() *elliptic.CurveParams {
	// RFC 5639, Section 3.6 — brainpoolP384r1
	// https://datatracker.ietf.org/doc/html/rfc5639#section-3.6
	return &elliptic.CurveParams{
		Name:    "brainpoolP384r1",
		BitSize: 384,
		P:  bigFromHex("8CB91E82A3386D280F5D6F7E50E641DF152F7109ED5456B412B1DA197FB71123ACD3A729901D1A71874700133107EC53"), // p
		N:  bigFromHex("8CB91E82A3386D280F5D6F7E50E641DF152F7109ED5456B31F166E6CAC0425A7CF3AB6AF6B7FC3103B883202E9046565"), // q
		B:  bigFromHex("04A8C7DD22CE28268B39B55416F0447C2FB77DE107DCD2A62E880EA53EEB62D57CB4390295DBC9943AB78696FA504C11"), // B
		Gx: bigFromHex("1D1C64F068CF45FFA2A63A81B7C13F6B8847A3E77EF14FE3DB7FCAFE0CBD10E8E826E03436D646AAEF87B2E247D4AF1E"), // x
		Gy: bigFromHex("8ABE1D7520F9C2A45CB1EB8E95CFD55262B70B29FEEC5864E19C054FF99129280E4646217791811142820341263C5315"), // y
	}
}

func BrainpoolP384r1() *curveWithA {
	return &curveWithA{
		Curve: &brainpoolP384r1{},
		// RFC 5639, Section 3.6 — A (curve coefficient)
		A: bigFromHex("7BC382C63D8C150C3C72080ACE05AFA0C2BEA28E4FB22787139165EFBA91F90F8AA5814A503AD4EB04A8C7DD22CE2826"),
	}
}

type brainpoolP512r1 struct{ elliptic.Curve }

func (*brainpoolP512r1) Params() *elliptic.CurveParams {
	// RFC 5639, Section 3.7 — brainpoolP512r1
	// https://datatracker.ietf.org/doc/html/rfc5639#section-3.7
	return &elliptic.CurveParams{
		Name:    "brainpoolP512r1",
		BitSize: 512,
		P:  bigFromHex("AADD9DB8DBE9C48B3FD4E6AE33C9FC07CB308DB3B3C9D20ED6639CCA703308717D4D9B009BC66842AECDA12AE6A380E62881FF2F2D82C68528AA6056583A48F3"), // p
		N:  bigFromHex("AADD9DB8DBE9C48B3FD4E6AE33C9FC07CB308DB3B3C9D20ED6639CCA70330870553E5C414CA92619418661197FAC10471DB1D381085DDADDB58796829CA90069"), // q
		B:  bigFromHex("3DF91610A83441CAEA9863BC2DED5D5AA8253AA10A2EF1C98B9AC8B57F1117A72BF2C7B9E7C1AC4D77FC94CADC083E67984050B75EBAE5DD2809BD638016F723"), // B
		Gx: bigFromHex("81AEE4BDD82ED9645A21322E9C4C6A9385ED9F70B5D916C1B43B62EEF4D0098EFF3B1F78E2D0D48D50D1687B93B97D5F7C6D5047406A5E688B352209BCB9F822"), // x
		Gy: bigFromHex("7DDE385D566332ECC0EABFA9CF7822FDF209F70024A57B1AA000C55B881F8111B2DCDE494A5F485E5BCA4BD88A2763AED1CA2B2FA8F0540678CD1E0F3AD80892"), // y
	}
}

func BrainpoolP512r1() *curveWithA {
	return &curveWithA{
		Curve: &brainpoolP512r1{},
		// RFC 5639, Section 3.7 — A (curve coefficient)
		A: bigFromHex("7830A3318B603B89E2327145AC234CC594CBDD8D3DF91610A83441CAEA9863BC2DED5D5AA8253AA10A2EF1C98B9AC8B57F1117A72BF2C7B9E7C1AC4D77FC94CA"),
	}
}

func writeBuiltinCurves(path string) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	w := &columnWriter{w: f}

	const fileHeader = `// Copyright (c) 2023, Google Inc.
// SPDX-License-Identifier: ISC

// This file is generated by make_tables.go.
`
	if _, err := io.WriteString(w, fileHeader); err != nil {
		return err
	}
	// P-224 is the only curve where we have a non-Montgomery implementation.
	if err := writeCurveData(w, elliptic.P224(), true); err != nil {
		return err
	}
	if err := writeCurveData(w, elliptic.P256(), false); err != nil {
		return err
	}
	if err := writeCurveData(w, elliptic.P384(), false); err != nil {
		return err
	}
	if err := writeCurveData(w, elliptic.P521(), true); err != nil {
		return err
	}
	if err := writeCurveData(w, SECP256K1(), false); err != nil {
		return err
	}
	// Brainpool curves from RFC 5639. These use generic Montgomery arithmetic
	// (EC_GFp_mont_method) like secp256k1, but with arbitrary a coefficients.
	if err := writeCurveDataWithA(w, BrainpoolP224r1()); err != nil {
		return err
	}
	if err := writeCurveDataWithA(w, BrainpoolP256r1()); err != nil {
		return err
	}
	if err := writeCurveDataWithA(w, BrainpoolP320r1()); err != nil {
		return err
	}
	if err := writeCurveDataWithA(w, BrainpoolP384r1()); err != nil {
		return err
	}
	if err := writeCurveDataWithA(w, BrainpoolP512r1()); err != nil {
		return err
	}
	return nil
}

// writeCurveDataWithA is like writeCurveData but also emits the Montgomery form
// of the a coefficient, for curves where a is not -3 or 0.
func writeCurveDataWithA(w *columnWriter, ca *curveWithA) error {
	if err := writeCurveData(w, ca.Curve, false); err != nil {
		return err
	}
	params := ca.Curve.Params()
	cName := strings.Replace(params.Name, "-", "", -1)

	if _, err := io.WriteString(w, "#if defined(OPENSSL_64_BIT)\n"); err != nil {
		return err
	}
	if err := writeDecl(w, ca.Curve, 64, fmt.Sprintf("k%sMontA", cName), toMontgomery(ca.A, params.P, 64)); err != nil {
		return err
	}
	if _, err := io.WriteString(w, "#elif defined(OPENSSL_32_BIT)\n"); err != nil {
		return err
	}
	if err := writeDecl(w, ca.Curve, 32, fmt.Sprintf("k%sMontA", cName), toMontgomery(ca.A, params.P, 32)); err != nil {
		return err
	}
	if _, err := io.WriteString(w, "#else\n#error \"unknown word size\"\n#endif\n"); err != nil {
		return err
	}
	return nil
}

func writeCurveData(w *columnWriter, curve elliptic.Curve, includeNonMontgomery bool) error {
	params := curve.Params()
	if _, err := fmt.Fprintf(w, "\n// %s\n", params.Name); err != nil {
		return err
	}

	cName := strings.Replace(params.Name, "-", "", -1)
	writeDecls := func(bits int) error {
		if err := writeDecl(w, curve, bits, fmt.Sprintf("k%sField", cName), params.P); err != nil {
			return err
		}
		if err := writeDecl(w, curve, bits, fmt.Sprintf("k%sOrder", cName), params.N); err != nil {
			return err
		}
		if includeNonMontgomery {
			if err := writeDecl(w, curve, bits, fmt.Sprintf("k%sB", cName), params.B); err != nil {
				return err
			}
			if err := writeDecl(w, curve, bits, fmt.Sprintf("k%sGX", cName), params.Gx); err != nil {
				return err
			}
			if err := writeDecl(w, curve, bits, fmt.Sprintf("k%sGY", cName), params.Gy); err != nil {
				return err
			}
		}
		if err := writeDecl(w, curve, bits, fmt.Sprintf("k%sFieldR", cName), montgomeryR(params.P, bits)); err != nil {
			return err
		}
		if err := writeDecl(w, curve, bits, fmt.Sprintf("k%sFieldRR", cName), montgomeryRR(params.P, bits)); err != nil {
			return err
		}
		if err := writeDecl(w, curve, bits, fmt.Sprintf("k%sOrderRR", cName), montgomeryRR(params.N, bits)); err != nil {
			return err
		}
		if err := writeDecl(w, curve, bits, fmt.Sprintf("k%sMontB", cName), toMontgomery(params.B, params.P, bits)); err != nil {
			return err
		}
		if err := writeDecl(w, curve, bits, fmt.Sprintf("k%sMontGX", cName), toMontgomery(params.Gx, params.P, bits)); err != nil {
			return err
		}
		if err := writeDecl(w, curve, bits, fmt.Sprintf("k%sMontGY", cName), toMontgomery(params.Gy, params.P, bits)); err != nil {
			return err
		}
		return nil
	}

	if _, err := fmt.Fprintf(w, "OPENSSL_UNUSED static const uint64_t k%sFieldN0 = 0x%016x;\n", cName, montgomeryN0(params.P)); err != nil {
		return err
	}
	if _, err := fmt.Fprintf(w, "OPENSSL_UNUSED static const uint64_t k%sOrderN0 = 0x%016x;\n", cName, montgomeryN0(params.N)); err != nil {
		return err
	}

	if _, err := io.WriteString(w, "#if defined(OPENSSL_64_BIT)\n"); err != nil {
		return err
	}
	if err := writeDecls(64); err != nil {
		return err
	}
	if _, err := io.WriteString(w, "#elif defined(OPENSSL_32_BIT)\n"); err != nil {
		return err
	}
	if err := writeDecls(32); err != nil {
		return err
	}
	if _, err := io.WriteString(w, "#else\n#error \"unknown word size\"\n#endif\n"); err != nil {
		return err
	}
	return nil
}

func writeP256NistzTable(path string) error {
	curve := elliptic.P256()
	tables := make([][][2]*big.Int, 0, 37)
	for shift := 0; shift < 256; shift += 7 {
		row := makeMultiples(curve, 64, shift)
		tables = append(tables, row)
	}

	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	w := &columnWriter{w: f}

	const fileHeader = `/*
 * Copyright 2014-2016 The OpenSSL Project Authors. All Rights Reserved.
 * Copyright (c) 2015, Intel Inc.
 *
 * Licensed under the OpenSSL license (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

// This is the precomputed constant time access table for the code in
// p256-nistz.c, for the default generator. The table consists of 37
// subtables, each subtable contains 64 affine points. The affine points are
// encoded as eight uint64's, four for the x coordinate and four for the y.
// Both values are in little-endian order. There are 37 tables because a
// signed, 6-bit wNAF form of the scalar is used and ceil(256/(6 + 1)) = 37.
// Within each table there are 64 values because the 6-bit wNAF value can take
// 64 values, ignoring the sign bit, which is implemented by performing a
// negation of the affine point when required. We would like to align it to 2MB
// in order to increase the chances of using a large page but that appears to
// lead to invalid ELF files being produced.

// This file is generated by make_tables.go.

static const alignas(4096) PRECOMP256_ROW ecp_nistz256_precomputed[37] = `
	if _, err := io.WriteString(w, fileHeader); err != nil {
		return err
	}
	if err := writeTables(w, curve, tables, writeBNMont, nil); err != nil {
		return err
	}
	if _, err := io.WriteString(w, ";\n"); err != nil {
		return err
	}

	return nil
}

func writeP256Table(path string) error {

	win_size := 5                                                       // window size for the comb multiplication
	pts_per_subtable := (1 << win_size) >> 1                            // we keep only the odd multiples
	num_subtables := int(math.Ceil(float64(256) / float64(win_size*4))) // we use comb mul with step 4

	curve := elliptic.P256()
	tables := make([][][2]*big.Int, 0, num_subtables)
	for i := 0; i < num_subtables; i += 1 {
		row := makeOddMultiples(curve, pts_per_subtable, i*win_size*4)
		tables = append(tables, row)
	}

	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	w := &columnWriter{w: f}

	const fileHeader = `// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This file is generated by make_tables.go.

#if defined(EC_NISTP_USE_64BIT_LIMB)`

	table_def_str := fmt.Sprintf("static const fiat_p256_felem fiat_p256_g_pre_comp[%d][%d][2] = ", num_subtables, pts_per_subtable)

	if _, err := io.WriteString(w, fileHeader+"\n"+table_def_str); err != nil {
		return err
	}
	if err := writeTables(w, curve, tables, writeU64Mont, nil); err != nil {
		return err
	}
	if _, err := io.WriteString(w, ";\n#else\n"+table_def_str); err != nil {
		return err
	}
	if err := writeTables(w, curve, tables, writeU32Mont, nil); err != nil {
		return err
	}
	if _, err := io.WriteString(w, ";\n#endif\n"); err != nil {
		return err
	}

	return nil
}

func writeP384Table(path string) error {

	win_size := 5                                                       // window size for the comb multiplication
	pts_per_subtable := (1 << win_size) >> 1                            // we keep only the odd multiples
	num_subtables := int(math.Ceil(float64(384) / float64(win_size*4))) // we use comb mul with step 4

	curve := elliptic.P384()
	tables := make([][][2]*big.Int, 0, num_subtables)
	for i := 0; i < num_subtables; i += 1 {
		row := makeOddMultiples(curve, pts_per_subtable, i*win_size*4)
		tables = append(tables, row)
	}

	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	w := &columnWriter{w: f}

	const fileHeader = `// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This file is generated by make_tables.go.

// P-384 base point pre computation
// --------------------------------
//
// Based on windows size equal to 5, the precomputed table for the base point G
// of P-384, |p384_g_pre_comp|, consists of 20 sub-tables, each holding 16
// points. A point is represented by a pair of field elements (x, y).
//
// The j-th point of the i-th sub-table is:
//     p384_g_pre_comp[i][j] = [(2j + 1)2^{20i}]G.
// The table is populated with such points for i in [0, 19] and j in [0, 15];
// and used in mul_base and mul_public functions in |p384.c| for computing
// a scalar product with the Comb method (see the functions for details).
//
// The table and its usage in scalar multiplications are adapted from
// ECCKiila project (https://arxiv.org/abs/2007.11481). The table generation
// is based on the generation method in:
// https://gitlab.com/nisec/ecckiila/-/blob/master/main.py#L296

#if defined(EC_NISTP_USE_64BIT_LIMB)`

	table_def_str := fmt.Sprintf("static const p384_felem p384_g_pre_comp[%d][%d][2] = ", num_subtables, pts_per_subtable)

	if _, err := io.WriteString(w, fileHeader+"\n"+table_def_str); err != nil {
		return err
	}
	if err := writeTables(w, curve, tables, writeU64Mont, nil); err != nil {
		return err
	}
	if _, err := io.WriteString(w, ";\n#else\n"+table_def_str); err != nil {
		return err
	}
	if err := writeTables(w, curve, tables, writeU32Mont, nil); err != nil {
		return err
	}
	if _, err := io.WriteString(w, ";\n#endif\n"); err != nil {
		return err
	}

	return nil
}

func writeP521Table(path string) error {

	win_size := 5                                                       // window size for the comb multiplication
	pts_per_subtable := (1 << win_size) >> 1                            // we keep only the odd multiples
	num_subtables := int(math.Ceil(float64(521) / float64(win_size*4))) // we use comb mul with step 4

	curve := elliptic.P521()
	tables := make([][][2]*big.Int, 0, num_subtables)
	for i := 0; i < num_subtables; i += 1 {
		row := makeOddMultiples(curve, pts_per_subtable, i*win_size*4)
		tables = append(tables, row)
	}

	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	w := &columnWriter{w: f}

	const fileHeader = `// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This file is generated by make_tables.go.

// P-521 base point pre computation
// --------------------------------
//
// Based on windows size equal to 5, the precomputed table for the base point G
// of P-521, |p521_g_pre_comp|, consists of 27 sub-tables, each holding 16
// points. A point is represented by a pair of field elements (x, y).
//
// The j-th point of the i-th sub-table is:
//     p521_g_pre_comp[i][j] = [(2j + 1)2^{20i}]G.
// The table is populated with such points for i in [0, 26] and j in [0, 15];
// and used in mul_base and mul_public functions in |p521.c| for computing
// a scalar product with the Comb method (see the functions for details).
//
// The table and its usage in scalar multiplications are adapted from
// ECCKiila project (https://arxiv.org/abs/2007.11481). The table generation
// is based on the generation method in:
// https://gitlab.com/nisec/ecckiila/-/blob/master/main.py#L296

#if defined(EC_NISTP_USE_S2N_BIGNUM)`

	table_def_str := fmt.Sprintf("static const p521_felem p521_g_pre_comp[%d][%d][2] = ", num_subtables, pts_per_subtable)

	if _, err := io.WriteString(w, fileHeader+"\n"+table_def_str); err != nil {
		return err
	}
	if err := writeTables(w, curve, tables, writeU64, nil); err != nil {
		return err
	}
	if _, err := io.WriteString(w, ";\n#else\n#if defined(EC_NISTP_USE_64BIT_LIMB)\n"+table_def_str); err != nil {
		return err
	}
	// P-521 Fiat-crypto implementation for 64-bit systems represents a field
	// element by an array of 58-bit digits stored in 64-bit containers.
	if err := writeTables(w, curve, tables, writeU58, nil); err != nil {
		return err
	}
	if _, err := io.WriteString(w, ";\n#else\n"+table_def_str); err != nil {
		return err
	}
	// P-521 Fiat-crypto implementation for 32-bit systems represents a field
	// element by an array of digits where digits have bit-size as listed below.
	var bitSizes = [...]uint{28, 27, 28, 27, 28, 27, 27, 28, 27, 28, 27, 28, 27, 27, 28, 27, 28, 27, 27}
	if err := writeTables(w, curve, tables, writeU32Custom, bitSizes[:]); err != nil {
		return err
	}
	if _, err := io.WriteString(w, ";\n#endif\n#endif\n"); err != nil {
		return err
	}

	return nil
}

// makeMultiples returns a table of the first n multiples of 2^shift * G,
// starting from 1 * 2^shift * G.
func makeMultiples(curve elliptic.Curve, n, shift int) [][2]*big.Int {
	ret := make([][2]*big.Int, n)
	x, y := curve.Params().Gx, curve.Params().Gy
	for j := 0; j < shift; j++ {
		x, y = curve.Double(x, y)
	}
	ret[1-1] = [2]*big.Int{x, y}
	for i := 2; i <= n; i++ {
		if i&1 == 0 {
			x, y := curve.Double(ret[i/2-1][0], ret[i/2-1][1])
			ret[i-1] = [2]*big.Int{x, y}
		} else {
			x, y := curve.Add(ret[i-1-1][0], ret[i-1-1][1], ret[1-1][0], ret[1-1][1])
			ret[i-1] = [2]*big.Int{x, y}
		}
	}
	return ret
}

// makeOddMultiples returns a table of the first n odd multiples of 2^shift * G
// starting from 1 * 2^shift * G.
func makeOddMultiples(curve elliptic.Curve, n, shift int) [][2]*big.Int {
	ret := make([][2]*big.Int, n)
	x, y := curve.Params().Gx, curve.Params().Gy
	cnt := 0
	for j := 0; j < shift; j++ {
		x, y = curve.Double(x, y)
		cnt++
	}

	ret[0] = [2]*big.Int{x, y}
	x2, y2 := curve.Double(x, y)

	for i := 1; i < n; i++ {
		x, y := curve.Add(ret[i-1][0], ret[i-1][1], x2, y2)
		ret[i] = [2]*big.Int{x, y}
	}

	return ret
}

// makeComb returns a table of 2^size - 1 points. The i-1th entry is k*G.
// If i is represented in binary by b0*2^0 + b1*2^1 + ... bn*2^n, k is
// b0*2^(shift + 0*stride) + b1*2^(shift + 1*stride) + ... + bn*2^(shift + n*stride).
// The entry for i = 0 is omitted because it is always the point at infinity.
func makeComb(curve elliptic.Curve, stride, size, shift int) [][2]*big.Int {
	ret := make([][2]*big.Int, 1<<size-1)
	x, y := curve.Params().Gx, curve.Params().Gy
	for j := 0; j < shift; j++ {
		x, y = curve.Double(x, y)
	}
	ret[1<<0-1] = [2]*big.Int{x, y}
	for i := 1; i < size; i++ {
		// Entry 2^i is entry 2^(i-1) doubled stride times.
		x, y = ret[1<<(i-1)-1][0], ret[1<<(i-1)-1][1]
		for j := 0; j < stride; j++ {
			x, y = curve.Double(x, y)
		}
		ret[1<<i-1] = [2]*big.Int{x, y}
		// The remaining entries with MSB 2^i are computed by adding entry 2^i
		// to the corresponding previous entry.
		for j := 1; j < 1<<i; j++ {
			x, y = curve.Add(ret[1<<i-1][0], ret[1<<i-1][1], ret[j-1][0], ret[j-1][1])
			ret[1<<i+j-1] = [2]*big.Int{x, y}
		}
	}
	return ret
}

func montgomeryR(p *big.Int, wordSize int) *big.Int {
	// R is the bit width of p, rounded up to word size.
	rounded := wordSize * ((p.BitLen() + wordSize - 1) / wordSize)
	R := new(big.Int).SetInt64(1)
	R.Lsh(R, uint(rounded))
	R.Mod(R, p)
	return R
}

func montgomeryRR(p *big.Int, wordSize int) *big.Int {
	R := montgomeryR(p, wordSize)
	R.Mul(R, R)
	R.Mod(R, p)
	return R
}

func montgomeryN0(p *big.Int) uint64 {
	two64 := new(big.Int)
	two64 = two64.SetBit(two64, 64, 1)
	n0 := new(big.Int).Neg(p)
	n0 = n0.ModInverse(n0, two64)
	if !n0.IsUint64() {
		panic("n0 should fit in uint64")
	}
	return n0.Uint64()
}

// toMontgomery returns n×R mod p, where R is the Montgomery factor.
func toMontgomery(n, p *big.Int, wordSize int) *big.Int {
	ret := montgomeryR(p, wordSize)
	ret.Mul(ret, n)
	ret.Mod(ret, p)
	return ret
}

func bigIntToU64s(curve elliptic.Curve, n *big.Int) []uint64 {
	words := (curve.Params().BitSize + 63) / 64
	ret := make([]uint64, words)
	bytes := n.Bytes()
	for i, b := range bytes {
		i = len(bytes) - i - 1
		ret[i/8] |= uint64(b) << (8 * (i % 8))
	}
	return ret
}

// Convert big int to an array of 58-bit digits.
// This is needed for P-521 Fiat-crypto implementation in third_party/fiat/p521_64.h.
func bigIntToU58s(curve elliptic.Curve, n *big.Int) []uint64 {
	words := (curve.Params().BitSize + 57) / 58
	ret := make([]uint64, words)
	mask := big.NewInt((1 << 58) - 1)
	tmp := new(big.Int).Set(n)
	for i := 0; i < words; i++ {
		ret[i] = new(big.Int).And(tmp, mask).Uint64()
		tmp.Rsh(tmp, 58)
	}
	return ret
}

// Convert big int to an array of digits where each digit
// has bit-size as specified in the input bitSizes array
// This is needed for P-521 Fiat-crypto implementation in third_party/fiat/p521_32.h.
// Sizes do not exceed 32 bits.
func bigIntToUCustom(curve elliptic.Curve, n *big.Int, bitSizes []uint) []uint32 {
	words := len(bitSizes)
	ret := make([]uint32, words)
	tmp := new(big.Int).Set(n)
	for i, bits := range bitSizes {
		mask := big.NewInt((1 << bits) - 1)
		ret[i] = uint32(new(big.Int).And(tmp, mask).Uint64())
		tmp.Rsh(tmp, bits)
	}
	return ret
}

func bigIntToU32s(curve elliptic.Curve, n *big.Int) []uint32 {
	words := (curve.Params().BitSize + 31) / 32
	ret := make([]uint32, words)
	bytes := n.Bytes()
	for i, b := range bytes {
		i = len(bytes) - i - 1
		ret[i/4] |= uint32(b) << (8 * (i % 4))
	}
	return ret
}

// A columnWriter is an io.Writer that tracks the number of columns in the
// current line.
type columnWriter struct {
	w      io.Writer
	column int
}

func (c *columnWriter) Write(p []byte) (n int, err error) {
	n, err = c.w.Write(p)
	idx := bytes.LastIndexByte(p[:n], '\n')
	if idx < 0 {
		c.column += n
	} else {
		c.column = n - idx - 1
	}
	return
}

func writeIndent(w io.Writer, indent int) error {
	for i := 0; i < indent; i++ {
		if _, err := io.WriteString(w, " "); err != nil {
			return err
		}
	}
	return nil
}

func writeWordsBraced[Word any](w *columnWriter, words []Word, format func(Word) string) error {
	if _, err := io.WriteString(w, "{"); err != nil {
		return err
	}
	if err := writeWords(w, words, format); err != nil {
		return err
	}
	if _, err := io.WriteString(w, "}"); err != nil {
		return err
	}
	return nil
}

func writeWords[Word any](w *columnWriter, words []Word, format func(Word) string) error {
	indent := w.column
	for i, word := range words {
		str := format(word)
		if i > 0 {
			if w.column+1+len(str) > 80 {
				if _, err := io.WriteString(w, ",\n"); err != nil {
					return err
				}
				if err := writeIndent(w, indent); err != nil {
					return err
				}
			} else {
				if _, err := io.WriteString(w, ", "); err != nil {
					return err
				}
			}
		}
		if _, err := io.WriteString(w, str); err != nil {
			return err
		}
	}
	return nil
}

func writeDecl(w *columnWriter, curve elliptic.Curve, bits int, decl string, n *big.Int) error {
	if _, err := fmt.Fprintf(w, "OPENSSL_UNUSED static const uint%d_t %s[] = {\n    ", bits, decl); err != nil {
		return err
	}
	if bits == 32 {
		if err := writeWords(w, bigIntToU32s(curve, n), formatU32); err != nil {
			return err
		}
	} else if bits == 64 {
		if err := writeWords(w, bigIntToU64s(curve, n), formatU64); err != nil {
			return err
		}
	} else {
		panic("unknown bit count")
	}
	if _, err := fmt.Fprintf(w, "};\n"); err != nil {
		return err
	}
	return nil
}

func formatBN(word uint64) string {
	return fmt.Sprintf("TOBN(0x%08x, 0x%08x)", uint32(word>>32), uint32(word))
}

func formatU64(word uint64) string {
	return fmt.Sprintf("0x%016x", word)
}

func formatU32(word uint32) string {
	return fmt.Sprintf("0x%08x", word)
}

func writeBNMont(w *columnWriter, curve elliptic.Curve, n *big.Int, bitSizes []uint) error {
	n32 := toMontgomery(n, curve.Params().P, 32)
	n64 := toMontgomery(n, curve.Params().P, 64)
	if n32.Cmp(n64) != 0 {
		panic(fmt.Sprintf("Montgomery form for %s is inconsistent between 32-bit and 64-bit", curve.Params().Name))
	}
	return writeWordsBraced(w, bigIntToU64s(curve, n64), formatBN)
}

func writeU64Mont(w *columnWriter, curve elliptic.Curve, n *big.Int, bitSizes []uint) error {
	n = toMontgomery(n, curve.Params().P, 64)
	return writeWordsBraced(w, bigIntToU64s(curve, n), formatU64)
}

func writeU32Mont(w *columnWriter, curve elliptic.Curve, n *big.Int, bitSizes []uint) error {
	n = toMontgomery(n, curve.Params().P, 32)
	return writeWordsBraced(w, bigIntToU32s(curve, n), formatU32)
}

func writeU64(w *columnWriter, curve elliptic.Curve, n *big.Int, bitSizes []uint) error {
	return writeWordsBraced(w, bigIntToU64s(curve, n), formatU64)
}

// This is needed for P-521 Fiat-crypto implementation.
func writeU58(w *columnWriter, curve elliptic.Curve, n *big.Int, bitSizes []uint) error {
	return writeWordsBraced(w, bigIntToU58s(curve, n), formatU64)
}

// Write a big int to an array of digits where each digit
// has bit-size as specified in the input bitSizes array
// This is needed for P-521 Fiat-crypto implementation.
func writeU32Custom(w *columnWriter, curve elliptic.Curve, n *big.Int, bitSizes []uint) error {
	return writeWordsBraced(w, bigIntToUCustom(curve, n, bitSizes), formatU32)
}

func writeU32(w *columnWriter, curve elliptic.Curve, n *big.Int, bitSizes []uint) error {
	return writeWordsBraced(w, bigIntToU32s(curve, n), formatU32)
}

type writeBigIntFunc func(w *columnWriter, curve elliptic.Curve, n *big.Int, bitSizes []uint) error

func writeTable(w *columnWriter, curve elliptic.Curve, table [][2]*big.Int, writeBigInt writeBigIntFunc, writeBigIntBitSizes []uint) error {
	if _, err := io.WriteString(w, "{"); err != nil {
		return err
	}
	indent := w.column
	for i, point := range table {
		if i != 0 {
			if _, err := io.WriteString(w, ",\n"); err != nil {
				return err
			}
			if err := writeIndent(w, indent); err != nil {
				return err
			}
		}
		if _, err := io.WriteString(w, "{"); err != nil {
			return err
		}
		if err := writeBigInt(w, curve, point[0], writeBigIntBitSizes); err != nil {
			return err
		}
		if _, err := io.WriteString(w, ",\n"); err != nil {
			return err
		}
		if err := writeIndent(w, indent+1); err != nil {
			return err
		}
		if err := writeBigInt(w, curve, point[1], writeBigIntBitSizes); err != nil {
			return err
		}
		if _, err := io.WriteString(w, "}"); err != nil {
			return err
		}
	}
	if _, err := io.WriteString(w, "}"); err != nil {
		return err
	}
	return nil
}

func writeTables(w *columnWriter, curve elliptic.Curve, tables [][][2]*big.Int, writeBigInt writeBigIntFunc, writeBigIntBitSizes []uint) error {
	if _, err := io.WriteString(w, "{\n    "); err != nil {
		return err
	}
	indent := w.column
	for i, table := range tables {
		if i != 0 {
			if _, err := io.WriteString(w, ",\n"); err != nil {
				return err
			}
			if err := writeIndent(w, indent); err != nil {
				return err
			}
		}
		if err := writeTable(w, curve, table, writeBigInt, writeBigIntBitSizes); err != nil {
			return err
		}
	}
	if _, err := io.WriteString(w, "}"); err != nil {
		return err
	}
	return nil
}
