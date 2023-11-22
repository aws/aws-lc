(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. SPDX-License-Identifier: Apache-2.0 *)
(* This is an automatically generated file. *)

module Cryptol = Cryptol
module Air = Air
type bv_airExp = Air.airExp;;

let lowercase_H0 : Cryptol.cryExp = (Cryptol.CrySeq
  [(((Cryptol.number "0x6a09e667f3bcc908") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xbb67ae8584caa73b") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x3c6ef372fe94f82b") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xa54ff53a5f1d36f1") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x510e527fade682d1") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x9b05688c2b3e6c1f") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x1f83d9abfb41bd6b") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x5be0cd19137e2179") (Cryptol.seq "0x40" Cryptol.Bit)))])

let lowercase_K : Cryptol.cryExp = (Cryptol.CrySeq
  [(((Cryptol.number "0x428a2f98d728ae22") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x7137449123ef65cd") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xb5c0fbcfec4d3b2f") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xe9b5dba58189dbbc") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x3956c25bf348b538") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x59f111f1b605d019") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x923f82a4af194f9b") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xab1c5ed5da6d8118") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xd807aa98a3030242") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x12835b0145706fbe") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x243185be4ee4b28c") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x550c7dc3d5ffb4e2") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x72be5d74f27b896f") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x80deb1fe3b1696b1") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x9bdc06a725c71235") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xc19bf174cf692694") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xe49b69c19ef14ad2") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xefbe4786384f25e3") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xfc19dc68b8cd5b5") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x240ca1cc77ac9c65") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x2de92c6f592b0275") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x4a7484aa6ea6e483") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x5cb0a9dcbd41fbd4") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x76f988da831153b5") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x983e5152ee66dfab") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xa831c66d2db43210") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xb00327c898fb213f") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xbf597fc7beef0ee4") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xc6e00bf33da88fc2") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xd5a79147930aa725") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x6ca6351e003826f") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x142929670a0e6e70") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x27b70a8546d22ffc") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x2e1b21385c26c926") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x4d2c6dfc5ac42aed") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x53380d139d95b3df") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x650a73548baf63de") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x766a0abb3c77b2a8") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x81c2c92e47edaee6") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x92722c851482353b") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xa2bfe8a14cf10364") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xa81a664bbc423001") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xc24b8b70d0f89791") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xc76c51a30654be30") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xd192e819d6ef5218") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xd69906245565a910") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xf40e35855771202a") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x106aa07032bbd1b8") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x19a4c116b8d2d0c8") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x1e376c085141ab53") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x2748774cdf8eeb99") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x34b0bcb5e19b48a8") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x391c0cb3c5c95a63") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x4ed8aa4ae3418acb") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x5b9cca4f7763e373") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x682e6ff3d6b2b8a3") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x748f82ee5defb2fc") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x78a5636f43172f60") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x84c87814a1f0ab72") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x8cc702081a6439ec") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x90befffa23631e28") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xa4506cebde82bde9") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xbef9a3f7b2c67915") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xc67178f2e372532b") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xca273eceea26619c") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xd186b8c721c0c207") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xeada7dd6cde0eb1e") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xf57d4f7fee6ed178") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x6f067aa72176fba") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0xa637dc5a2c898a6") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x113f9804bef90dae") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x1b710b35131c471b") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x28db77f523047d84") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x32caab7b40c72493") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x3c9ebe0a15c9bebc") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x431d67c49c100d4c") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x4cc5d4becb3e42b6") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x597f299cfc657e2a") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x5fcb6fab3ad6faec") (Cryptol.seq "0x40" Cryptol.Bit)));
   (((Cryptol.number "0x6c44198c4a475817") (Cryptol.seq "0x40" Cryptol.Bit)))])

let cry_S0 : Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_x : Cryptol.cryExp) ->
    ((((Cryptol.bvxor (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.bvxor (Cryptol.seq "0x40" Cryptol.Bit))) (((((((Cryptol.bvror "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0x1c") Cryptol.Integer)))) (((((((Cryptol.bvror "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0x22") Cryptol.Integer))))) (((((((Cryptol.bvror "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0x27") Cryptol.Integer)))))

let air_S0 =
  (Cryptol.defun "spec.SHA512rec.air_S0" [(Cryptol.sb "lowercase_x" 64)]  (Cryptol.toAir (cry_S0 (Cryptol.toCry1Dim (Cryptol.sb "lowercase_x" 64)))))

let lowercase_S0 lowercase_x =
  (Cryptol.toCry1Dim (Cryptol.apply air_S0 [(Cryptol.toAir lowercase_x)]))

let cry_S1 : Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_x : Cryptol.cryExp) ->
    ((((Cryptol.bvxor (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.bvxor (Cryptol.seq "0x40" Cryptol.Bit))) (((((((Cryptol.bvror "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0xe") Cryptol.Integer)))) (((((((Cryptol.bvror "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0x12") Cryptol.Integer))))) (((((((Cryptol.bvror "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0x29") Cryptol.Integer)))))

let air_S1 =
  (Cryptol.defun "spec.SHA512rec.air_S1" [(Cryptol.sb "lowercase_x" 64)]  (Cryptol.toAir (cry_S1 (Cryptol.toCry1Dim (Cryptol.sb "lowercase_x" 64)))))

let lowercase_S1 lowercase_x =
  (Cryptol.toCry1Dim (Cryptol.apply air_S1 [(Cryptol.toAir lowercase_x)]))

let cry_s0 : Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_x : Cryptol.cryExp) ->
    ((((Cryptol.bvxor (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.bvxor (Cryptol.seq "0x40" Cryptol.Bit))) (((((((Cryptol.bvror "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0x1") Cryptol.Integer)))) (((((((Cryptol.bvror "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0x8") Cryptol.Integer))))) (((((((Cryptol.bvrsh "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0x7") Cryptol.Integer)))))

let air_s0 =
  (Cryptol.defun "spec.SHA512rec.air_s0" [(Cryptol.sb "lowercase_x" 64)]  (Cryptol.toAir (cry_s0 (Cryptol.toCry1Dim (Cryptol.sb "lowercase_x" 64)))))

let lowercase_s0 lowercase_x =
  (Cryptol.toCry1Dim (Cryptol.apply air_s0 [(Cryptol.toAir lowercase_x)]))

let cry_s1 : Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_x : Cryptol.cryExp) ->
    ((((Cryptol.bvxor (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.bvxor (Cryptol.seq "0x40" Cryptol.Bit))) (((((((Cryptol.bvror "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0x13") Cryptol.Integer)))) (((((((Cryptol.bvror "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0x3d") Cryptol.Integer))))) (((((((Cryptol.bvrsh "0x40") Cryptol.Integer) Cryptol.Bit))) lowercase_x) (((Cryptol.number "0x6") Cryptol.Integer)))))

let air_s1 =
  (Cryptol.defun "spec.SHA512rec.air_s1" [(Cryptol.sb "lowercase_x" 64)]  (Cryptol.toAir (cry_s1 (Cryptol.toCry1Dim (Cryptol.sb "lowercase_x" 64)))))

let lowercase_s1 lowercase_x =
  (Cryptol.toCry1Dim (Cryptol.apply air_s1 [(Cryptol.toAir lowercase_x)]))

let cry_Ch : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_x : Cryptol.cryExp)
    (lowercase_y : Cryptol.cryExp)
    (lowercase_z : Cryptol.cryExp) ->
    ((((Cryptol.bvxor (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.bvand (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_x) lowercase_y)) ((((Cryptol.bvand (Cryptol.seq "0x40" Cryptol.Bit))) (((Cryptol.bvnot (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_x)) lowercase_z)))

let air_Ch =
  (Cryptol.defun "spec.SHA512rec.air_Ch" [(Cryptol.sb "lowercase_x" 64);
  (Cryptol.sb "lowercase_y" 64);
  (Cryptol.sb "lowercase_z" 64)]  (Cryptol.toAir (cry_Ch (Cryptol.toCry1Dim (Cryptol.sb "lowercase_x" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_y" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_z" 64)))))

let lowercase_Ch lowercase_x lowercase_y lowercase_z =
  (Cryptol.toCry1Dim (Cryptol.apply air_Ch [(Cryptol.toAir lowercase_x);
  (Cryptol.toAir lowercase_y);
  (Cryptol.toAir lowercase_z)]))

let cry_Maj : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_x : Cryptol.cryExp)
    (lowercase_y : Cryptol.cryExp)
    (lowercase_z : Cryptol.cryExp) ->
    ((((Cryptol.bvxor (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.bvxor (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.bvand (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_x) lowercase_y)) ((((Cryptol.bvand (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_x) lowercase_z))) ((((Cryptol.bvand (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_y) lowercase_z)))

let air_Maj =
  (Cryptol.defun "spec.SHA512rec.air_Maj" [(Cryptol.sb "lowercase_x" 64);
  (Cryptol.sb "lowercase_y" 64);
  (Cryptol.sb "lowercase_z" 64)]  (Cryptol.toAir (cry_Maj (Cryptol.toCry1Dim (Cryptol.sb "lowercase_x" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_y" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_z" 64)))))

let lowercase_Maj lowercase_x lowercase_y lowercase_z =
  (Cryptol.toCry1Dim (Cryptol.apply air_Maj [(Cryptol.toAir lowercase_x);
  (Cryptol.toAir lowercase_y);
  (Cryptol.toAir lowercase_z)]))

let cry_messageSchedule_Word : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_w1 : Cryptol.cryExp)
    (lowercase_w2 : Cryptol.cryExp)
    (lowercase_w3 : Cryptol.cryExp)
    (lowercase_w4 : Cryptol.cryExp) ->
    ((((Cryptol.add (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.add (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.add (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_w1) (lowercase_s0 lowercase_w2))) lowercase_w3)) (lowercase_s1 lowercase_w4)))

let air_messageSchedule_Word =
  (Cryptol.defun "spec.SHA512rec.air_messageSchedule_Word" [(Cryptol.sb "lowercase_w1" 64);
  (Cryptol.sb "lowercase_w2" 64);
  (Cryptol.sb "lowercase_w3" 64);
  (Cryptol.sb "lowercase_w4" 64)]  (Cryptol.toAir (cry_messageSchedule_Word (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w1" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w2" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w3" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w4" 64)))))

let lowercase_messageSchedule_Word lowercase_w1
  lowercase_w2
  lowercase_w3
  lowercase_w4 =
  (Cryptol.toCry1Dim (Cryptol.apply air_messageSchedule_Word [(Cryptol.toAir lowercase_w1);
  (Cryptol.toAir lowercase_w2);
  (Cryptol.toAir lowercase_w3);
  (Cryptol.toAir lowercase_w4)]))

let rec lowercase_messageSchedule_Common_helper : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_Mi : Cryptol.cryExp)
    (lowercase_ind : Cryptol.cryExp)
    (lowercase_acc : Cryptol.cryExp) ->
    (if ((((Cryptol.geq Cryptol.Integer)) lowercase_ind) (((Cryptol.number "0x50") Cryptol.Integer)))
     then lowercase_acc
     else (if ((((Cryptol.lt Cryptol.Integer)) lowercase_ind) (((Cryptol.number "0x10") Cryptol.Integer)))
           then ((lowercase_messageSchedule_Common_helper lowercase_Mi ((((Cryptol.add Cryptol.Integer)) lowercase_ind) (((Cryptol.number "0x1") Cryptol.Integer)))) (((((((Cryptol.update "0x50") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) lowercase_ind) ((((((Cryptol.at "0x10") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_Mi) lowercase_ind)))
           else (let lowercase_w1 : Cryptol.cryExp =
             ((((((Cryptol.at "0x50") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) ((((Cryptol.sub Cryptol.Integer)) lowercase_ind) (((Cryptol.number "0x10") Cryptol.Integer))))
             in
           let lowercase_w2 : Cryptol.cryExp =
             ((((((Cryptol.at "0x50") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) ((((Cryptol.sub Cryptol.Integer)) lowercase_ind) (((Cryptol.number "0xf") Cryptol.Integer))))
             in
           let lowercase_w3 : Cryptol.cryExp =
             ((((((Cryptol.at "0x50") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) ((((Cryptol.sub Cryptol.Integer)) lowercase_ind) (((Cryptol.number "0x7") Cryptol.Integer))))
             in
           let lowercase_w4 : Cryptol.cryExp =
             ((((((Cryptol.at "0x50") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) ((((Cryptol.sub Cryptol.Integer)) lowercase_ind) (((Cryptol.number "0x2") Cryptol.Integer))))
             in
           ((lowercase_messageSchedule_Common_helper lowercase_Mi ((((Cryptol.add Cryptol.Integer)) lowercase_ind) (((Cryptol.number "0x1") Cryptol.Integer)))) (((((((Cryptol.update "0x50") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) lowercase_ind) (((lowercase_messageSchedule_Word lowercase_w1 lowercase_w2) lowercase_w3) lowercase_w4)))))))

let lowercase_messageSchedule_Common_rec : Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_Mi : Cryptol.cryExp) ->
    ((lowercase_messageSchedule_Common_helper lowercase_Mi (((Cryptol.number "0x0") Cryptol.Integer))) ((Cryptol.zero (Cryptol.seq "0x50" (Cryptol.seq "0x40" Cryptol.Bit))))))

let cry_compress_Common_t1 : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_e : Cryptol.cryExp)
    (lowercase_f : Cryptol.cryExp)
    (lowercase_g : Cryptol.cryExp)
    (lowercase_h : Cryptol.cryExp)
    (lowercase_kt : Cryptol.cryExp)
    (lowercase_wt : Cryptol.cryExp) ->
    ((((Cryptol.add (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.add (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.add (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.add (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_h) (lowercase_S1 lowercase_e))) ((lowercase_Ch lowercase_e lowercase_f) lowercase_g))) lowercase_kt)) lowercase_wt))

let air_compress_Common_t1 =
  (Cryptol.defun "spec.SHA512rec.air_compress_Common_t1" [(Cryptol.sb "lowercase_e" 64);
  (Cryptol.sb "lowercase_f" 64);
  (Cryptol.sb "lowercase_g" 64);
  (Cryptol.sb "lowercase_h" 64);
  (Cryptol.sb "lowercase_kt" 64);
  (Cryptol.sb "lowercase_wt" 64)]  (Cryptol.toAir (cry_compress_Common_t1 (Cryptol.toCry1Dim (Cryptol.sb "lowercase_e" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_f" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_g" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_h" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_kt" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_wt" 64)))))

let lowercase_compress_Common_t1 lowercase_e
  lowercase_f
  lowercase_g
  lowercase_h
  lowercase_kt
  lowercase_wt =
  (Cryptol.toCry1Dim (Cryptol.apply air_compress_Common_t1 [(Cryptol.toAir lowercase_e);
  (Cryptol.toAir lowercase_f);
  (Cryptol.toAir lowercase_g);
  (Cryptol.toAir lowercase_h);
  (Cryptol.toAir lowercase_kt);
  (Cryptol.toAir lowercase_wt)]))

let cry_compress_Common_t2 : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_a : Cryptol.cryExp)
    (lowercase_b : Cryptol.cryExp)
    (lowercase_c : Cryptol.cryExp) ->
    ((((Cryptol.add (Cryptol.seq "0x40" Cryptol.Bit))) (lowercase_S0 lowercase_a)) ((lowercase_Maj lowercase_a lowercase_b) lowercase_c)))

let air_compress_Common_t2 =
  (Cryptol.defun "spec.SHA512rec.air_compress_Common_t2" [(Cryptol.sb "lowercase_a" 64);
  (Cryptol.sb "lowercase_b" 64);
  (Cryptol.sb "lowercase_c" 64)]  (Cryptol.toAir (cry_compress_Common_t2 (Cryptol.toCry1Dim (Cryptol.sb "lowercase_a" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_b" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_c" 64)))))

let lowercase_compress_Common_t2 lowercase_a
  lowercase_b
  lowercase_c =
  (Cryptol.toCry1Dim (Cryptol.apply air_compress_Common_t2 [(Cryptol.toAir lowercase_a);
  (Cryptol.toAir lowercase_b);
  (Cryptol.toAir lowercase_c)]))

let cry_compress_Common_e : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_d : Cryptol.cryExp)
    (lowercase_T1 : Cryptol.cryExp) ->
    ((((Cryptol.add (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_d) lowercase_T1))

let air_compress_Common_e =
  (Cryptol.defun "spec.SHA512rec.air_compress_Common_e" [(Cryptol.sb "lowercase_d" 64);
  (Cryptol.sb "lowercase_T1" 64)]  (Cryptol.toAir (cry_compress_Common_e (Cryptol.toCry1Dim (Cryptol.sb "lowercase_d" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_T1" 64)))))

let lowercase_compress_Common_e lowercase_d lowercase_T1 =
  (Cryptol.toCry1Dim (Cryptol.apply air_compress_Common_e [(Cryptol.toAir lowercase_d);
  (Cryptol.toAir lowercase_T1)]))

let cry_compress_Common_a : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_T1 : Cryptol.cryExp)
    (lowercase_T2 : Cryptol.cryExp) ->
    ((((Cryptol.add (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_T1) lowercase_T2))

let air_compress_Common_a =
  (Cryptol.defun "spec.SHA512rec.air_compress_Common_a" [(Cryptol.sb "lowercase_T1" 64);
  (Cryptol.sb "lowercase_T2" 64)]  (Cryptol.toAir (cry_compress_Common_a (Cryptol.toCry1Dim (Cryptol.sb "lowercase_T1" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_T2" 64)))))

let lowercase_compress_Common_a lowercase_T1 lowercase_T2 =
  (Cryptol.toCry1Dim (Cryptol.apply air_compress_Common_a [(Cryptol.toAir lowercase_T1);
  (Cryptol.toAir lowercase_T2)]))

let rec lowercase_compress_Common_helper : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_H : Cryptol.cryExp)
    (lowercase_W : Cryptol.cryExp)
    (lowercase_ind : Cryptol.cryExp)
    (lowercase_acc : Cryptol.cryExp) ->
    (if ((((Cryptol.geq Cryptol.Integer)) lowercase_ind) (((Cryptol.number "0x50") Cryptol.Integer)))
     then ((((Cryptol.add (Cryptol.seq "0x8" (Cryptol.seq "0x40" Cryptol.Bit)))) lowercase_acc) lowercase_H)
     else (let lowercase_a : Cryptol.cryExp =
       ((((((Cryptol.at "0x8") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) (((Cryptol.number "0x0") Cryptol.Integer)))
       in
     let lowercase_b : Cryptol.cryExp =
       ((((((Cryptol.at "0x8") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) (((Cryptol.number "0x1") Cryptol.Integer)))
       in
     let lowercase_c : Cryptol.cryExp =
       ((((((Cryptol.at "0x8") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) (((Cryptol.number "0x2") Cryptol.Integer)))
       in
     let lowercase_d : Cryptol.cryExp =
       ((((((Cryptol.at "0x8") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) (((Cryptol.number "0x3") Cryptol.Integer)))
       in
     let lowercase_e : Cryptol.cryExp =
       ((((((Cryptol.at "0x8") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) (((Cryptol.number "0x4") Cryptol.Integer)))
       in
     let lowercase_f : Cryptol.cryExp =
       ((((((Cryptol.at "0x8") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) (((Cryptol.number "0x5") Cryptol.Integer)))
       in
     let lowercase_g : Cryptol.cryExp =
       ((((((Cryptol.at "0x8") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) (((Cryptol.number "0x6") Cryptol.Integer)))
       in
     let lowercase_h : Cryptol.cryExp =
       ((((((Cryptol.at "0x8") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_acc) (((Cryptol.number "0x7") Cryptol.Integer)))
       in
     let lowercase_T1 : Cryptol.cryExp =
       (((((lowercase_compress_Common_t1 lowercase_e lowercase_f) lowercase_g) lowercase_h) ((((((Cryptol.at "0x50") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_K) lowercase_ind)) ((((((Cryptol.at "0x50") (Cryptol.seq "0x40" Cryptol.Bit)) Cryptol.Integer)) lowercase_W) lowercase_ind))
       in
     let lowercase_T2 : Cryptol.cryExp =
       ((lowercase_compress_Common_t2 lowercase_a lowercase_b) lowercase_c)
       in
     let lowercase_h' : Cryptol.cryExp = lowercase_g in
     let lowercase_g' : Cryptol.cryExp = lowercase_f in
     let lowercase_f' : Cryptol.cryExp = lowercase_e in
     let lowercase_e' : Cryptol.cryExp =
       (lowercase_compress_Common_e lowercase_d lowercase_T1) in
     let lowercase_d' : Cryptol.cryExp = lowercase_c in
     let lowercase_c' : Cryptol.cryExp = lowercase_b in
     let lowercase_b' : Cryptol.cryExp = lowercase_a in
     let lowercase_a' : Cryptol.cryExp =
       (lowercase_compress_Common_a lowercase_T1 lowercase_T2) in
     (((lowercase_compress_Common_helper lowercase_H lowercase_W) ((((Cryptol.add Cryptol.Integer)) lowercase_ind) (((Cryptol.number "0x1") Cryptol.Integer)))) (Cryptol.CrySeq
     [lowercase_a'; lowercase_b'; lowercase_c'; lowercase_d';
      lowercase_e'; lowercase_f'; lowercase_g'; lowercase_h']))))) 
let lowercase_compress_Common_rec : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_H : Cryptol.cryExp)
    (lowercase_W : Cryptol.cryExp) ->
    (((lowercase_compress_Common_helper lowercase_H lowercase_W) (((Cryptol.number "0x0") Cryptol.Integer))) lowercase_H))

let cry_processBlock_Common_rec : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  (fun (lowercase_H : Cryptol.cryExp)
    (lowercase_w0 : Cryptol.cryExp)
    (lowercase_w1 : Cryptol.cryExp)
    (lowercase_w2 : Cryptol.cryExp)
    (lowercase_w3 : Cryptol.cryExp)
    (lowercase_w4 : Cryptol.cryExp)
    (lowercase_w5 : Cryptol.cryExp)
    (lowercase_w6 : Cryptol.cryExp)
    (lowercase_w7 : Cryptol.cryExp)
    (lowercase_w8 : Cryptol.cryExp)
    (lowercase_w9 : Cryptol.cryExp)
    (lowercase_w10 : Cryptol.cryExp)
    (lowercase_w11 : Cryptol.cryExp)
    (lowercase_w12 : Cryptol.cryExp)
    (lowercase_w13 : Cryptol.cryExp)
    (lowercase_w14 : Cryptol.cryExp)
    (lowercase_w15 : Cryptol.cryExp) ->
    (let lowercase_Mi : Cryptol.cryExp = (Cryptol.CrySeq
      [lowercase_w0; lowercase_w1; lowercase_w2; lowercase_w3;
       lowercase_w4; lowercase_w5; lowercase_w6; lowercase_w7;
       lowercase_w8; lowercase_w9; lowercase_w10; lowercase_w11;
       lowercase_w12; lowercase_w13; lowercase_w14; lowercase_w15]) in
    (((((Cryptol.join "0x8") "0x40") Cryptol.Bit)) (lowercase_compress_Common_rec (((((Cryptol.split "0x8") "0x40") Cryptol.Bit)) lowercase_H) (lowercase_messageSchedule_Common_rec lowercase_Mi)))))

let air_processBlock_Common_rec =
  (Cryptol.defun "spec.SHA512rec.air_processBlock_Common_rec" [(Cryptol.sb "lowercase_H" 512);
  (Cryptol.sb "lowercase_w0" 64);
  (Cryptol.sb "lowercase_w1" 64);
  (Cryptol.sb "lowercase_w2" 64);
  (Cryptol.sb "lowercase_w3" 64);
  (Cryptol.sb "lowercase_w4" 64);
  (Cryptol.sb "lowercase_w5" 64);
  (Cryptol.sb "lowercase_w6" 64);
  (Cryptol.sb "lowercase_w7" 64);
  (Cryptol.sb "lowercase_w8" 64);
  (Cryptol.sb "lowercase_w9" 64);
  (Cryptol.sb "lowercase_w10" 64);
  (Cryptol.sb "lowercase_w11" 64);
  (Cryptol.sb "lowercase_w12" 64);
  (Cryptol.sb "lowercase_w13" 64);
  (Cryptol.sb "lowercase_w14" 64);
  (Cryptol.sb "lowercase_w15" 64)]  (Cryptol.toAir (cry_processBlock_Common_rec (Cryptol.toCry1Dim (Cryptol.sb "lowercase_H" 512))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w0" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w1" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w2" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w3" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w4" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w5" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w6" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w7" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w8" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w9" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w10" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w11" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w12" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w13" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w14" 64))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_w15" 64)))))

let lowercase_processBlock_Common_rec lowercase_H
  lowercase_w0
  lowercase_w1
  lowercase_w2
  lowercase_w3
  lowercase_w4
  lowercase_w5
  lowercase_w6
  lowercase_w7
  lowercase_w8
  lowercase_w9
  lowercase_w10
  lowercase_w11
  lowercase_w12
  lowercase_w13
  lowercase_w14
  lowercase_w15 =
  (Cryptol.toCry1Dim (Cryptol.apply air_processBlock_Common_rec [(Cryptol.toAir lowercase_H);
  (Cryptol.toAir lowercase_w0);
  (Cryptol.toAir lowercase_w1);
  (Cryptol.toAir lowercase_w2);
  (Cryptol.toAir lowercase_w3);
  (Cryptol.toAir lowercase_w4);
  (Cryptol.toAir lowercase_w5);
  (Cryptol.toAir lowercase_w6);
  (Cryptol.toAir lowercase_w7);
  (Cryptol.toAir lowercase_w8);
  (Cryptol.toAir lowercase_w9);
  (Cryptol.toAir lowercase_w10);
  (Cryptol.toAir lowercase_w11);
  (Cryptol.toAir lowercase_w12);
  (Cryptol.toAir lowercase_w13);
  (Cryptol.toAir lowercase_w14);
  (Cryptol.toAir lowercase_w15)]))

let cry_processBlocks_rec : Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp -> Cryptol.cryExp =
  let lowercase_processBlocks_rec lowercase_H
  lowercase_num
  lowercase_data = (Cryptol.toCry1Dim (Cryptol.apply_rec "spec.SHA512rec.air_processBlocks_rec" [(Cryptol.toAir lowercase_H);
  (Cryptol.toAir lowercase_num);
  (Cryptol.toAir lowercase_data)] (Air.BV 512))) in
  (fun (lowercase_H : Cryptol.cryExp)
    (lowercase_num : Cryptol.cryExp)
    (lowercase_data : Cryptol.cryExp) ->
    (Cryptol.airIte ((((Cryptol.eqAir (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_num) (((Cryptol.number "0x0") (Cryptol.seq "0x40" Cryptol.Bit))))
     lowercase_H
     (let lowercase_last_Block : Cryptol.cryExp =
       ((((((((Cryptol.arrayRangeLookup (Cryptol.seq "0x40" Cryptol.Bit)) (Cryptol.seq "0x40" Cryptol.Bit)) "0x10")))) lowercase_data) ((((Cryptol.mul (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.mul (Cryptol.seq "0x40" Cryptol.Bit))) ((((Cryptol.sub (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_num) (((Cryptol.number "0x1") (Cryptol.seq "0x40" Cryptol.Bit))))) (((Cryptol.number "0x2") (Cryptol.seq "0x40" Cryptol.Bit))))) (((Cryptol.number "0x8") (Cryptol.seq "0x40" Cryptol.Bit)))))
       in
     let lowercase_prev_H : Cryptol.cryExp =
       ((lowercase_processBlocks_rec lowercase_H ((((Cryptol.sub (Cryptol.seq "0x40" Cryptol.Bit))) lowercase_num) (((Cryptol.number "0x1") (Cryptol.seq "0x40" Cryptol.Bit))))) lowercase_data)
       in
     let lowercase___p0 : Cryptol.cryExp = lowercase_last_Block in
     let lowercase_w0 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 0) in
     let lowercase_w1 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 1) in
     let lowercase_w2 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 2) in
     let lowercase_w3 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 3) in
     let lowercase_w4 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 4) in
     let lowercase_w5 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 5) in
     let lowercase_w6 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 6) in
     let lowercase_w7 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 7) in
     let lowercase_w8 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 8) in
     let lowercase_w9 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 9) in
     let lowercase_w10 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 10) in
     let lowercase_w11 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 11) in
     let lowercase_w12 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 12) in
     let lowercase_w13 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 13) in
     let lowercase_w14 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 14) in
     let lowercase_w15 : Cryptol.cryExp =
       (Cryptol.seqSel lowercase___p0 15) in
     ((((((((((((((((lowercase_processBlock_Common_rec lowercase_prev_H lowercase_w0) lowercase_w1) lowercase_w2) lowercase_w3) lowercase_w4) lowercase_w5) lowercase_w6) lowercase_w7) lowercase_w8) lowercase_w9) lowercase_w10) lowercase_w11) lowercase_w12) lowercase_w13) lowercase_w14) lowercase_w15))))

let air_processBlocks_rec =
  (Cryptol.defun_rec "spec.SHA512rec.air_processBlocks_rec" [(Cryptol.sb "lowercase_H" 512);
  (Cryptol.sb "lowercase_num" 64);
  (Cryptol.smem "lowercase_data" 64 64)] (Air.BV 512) (Cryptol.toAir (cry_processBlocks_rec (Cryptol.toCry1Dim (Cryptol.sb "lowercase_H" 512))
  (Cryptol.toCry1Dim (Cryptol.sb "lowercase_num" 64))
  (Cryptol.toCryMem (Cryptol.smem "lowercase_data" 64 64)))))

let lowercase_processBlocks_rec lowercase_H
  lowercase_num
  lowercase_data =
  (Cryptol.toCry1Dim (Cryptol.apply air_processBlocks_rec [(Cryptol.toAir lowercase_H);
  (Cryptol.toAir lowercase_num);
  (Cryptol.toAir lowercase_data)]))
