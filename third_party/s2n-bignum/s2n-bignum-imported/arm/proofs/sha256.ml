(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(** Carl Kwan: ARM SHA256 intrinsics in HOL Light **)

needs "Library/words.ml";;

(****************************************************)
(**                                                **)
(** COMMONLY USED FUNCTIONS FOR SHA256 INTRINSICS  **)
(**                                                **)
(****************************************************)

let sha_choose = new_definition
  `sha_choose (x:int32) (y:int32) (z:int32) : int32 =
          word_xor (word_and (word_xor y z) x) z`;;

let sha_maj = new_definition
  `sha_maj (x:int32) (y:int32) (z:int32) : int32 =
          word_or (word_and x y) (word_and (word_or x y) z)`;;

let sha_hash_sigma_0 = new_definition
  `sha_hash_sigma_0 (x:int32) : int32 =
          word_xor (word_ror x 2) (word_xor (word_ror x 13) (word_ror x 22))`;;

let sha_hash_sigma_1 = new_definition
  `sha_hash_sigma_1 (x:int32) : int32 =
          word_xor (word_ror x 6) (word_xor (word_ror x 11) (word_ror x 25))`;;

(**
 **  ARM pseudo code definition of elem
 **
 **    bits(size) Elem[bits(N) vector, integer e, integer size]
 **        assert e >= 0 && (e+1)*size <= N;
 **        return vector<e*size+size-1 : e*size>;
 **
 **    This just grabs some sequence of bits from the middle of the word
 **)

let elem = new_definition
  `elem (w:M word) (e:num) (size:num) : size word =
          word_subword w (e*size, size)`;;

(**
 **  ARM pseudo code definition of SHA256hash
 **
 **  bits(128) SHA256hash(bits (128) X, bits(128) Y, bits(128) W, boolean part1)
 **      bits(32) chs, maj, t;
 **
 **      for e = 0 to 3
 **          chs = SHAchoose(Y<31:0>, Y<63:32>, Y<95:64>);
 **          maj = SHAmajority(X<31:0>, X<63:32>, X<95:64>);
 **          t = Y<127:96> + SHAhashSIGMA1(Y<31:0>) + chs + Elem[W, e, 32];
 **          X<127:96> = t + X<127:96>;
 **          Y<127:96> = t + SHAhashSIGMA0(X<31:0>) + maj;
 **          <Y, X> = ROL(Y : X, 32);
 **      return (if part1 then X else Y);
 **)

let sha256hash_loop = new_definition
  `sha256hash_loop (e:num) (x:int128) (y:int128) (w:int128) : 256 word =
          let chs = sha_choose (word_subword y (0,32))
                               (word_subword y (32,32))
                               (word_subword y (64,32)) in
          let maj = sha_maj (word_subword x (0,32))
                            (word_subword x (32,32))
                            (word_subword x (64,32)) in
          let   t = word_add (word_subword y (96,32))
                             (word_add (sha_hash_sigma_1 (word_subword y (0,32)))
                                       (word_add chs (elem w e 32))) in
          let x_upper = word_add t (word_subword x (96, 32)) in
          let y_upper = word_add t (word_add (sha_hash_sigma_0 (word_subword x (0, 32))) maj) in
          let       x = (word_join : int32->96 word->int128) x_upper (word_subword x (0, 96)) in
          let       y = (word_join : int32->96 word->int128) y_upper (word_subword y (0, 96)) in
          let      xy = word_rol ((word_join : int128->int128->256 word) x y) 32 in
          xy`;;

let sha256hash = new_definition
  `sha256hash (x:int128) (y:int128) (w:int128) (part1:bool) : int128 =
          let xy:256 word = sha256hash_loop 0 x y w in
          let x:int128 = word_subword xy (128, 128) in
          let y:int128 = word_subword xy (  0, 128) in

          let xy:256 word = sha256hash_loop 1 x y w in
          let x:int128 = word_subword xy (128, 128) in
          let y:int128 = word_subword xy (  0, 128) in

          let xy:256 word = sha256hash_loop 2 x y w in
          let x:int128 = word_subword xy (128, 128) in
          let y:int128 = word_subword xy (  0, 128) in

          let xy:256 word = sha256hash_loop 3 x y w in
          let x:int128 = word_subword xy (128, 128) in
          let y:int128 = word_subword xy (  0, 128) in

          if part1 then x else y`;;


(*************************)
(**                     **)
(**  SHA256 INTRINSICS  **)
(**                     **)
(*************************)

let sha256h = define
  `sha256h (d:int128) (n:int128) (m:int128) : int128 =
          sha256hash d n m T`;;

let sha256h2 = define
  `sha256h2 (d:int128) (n:int128) (m:int128) : int128 =
          sha256hash n d m F`;;

(**
 **  ARM pseudocode of sha256su0
 **
 **    bits(128) operand1 = V[d];
 **    bits(128) operand2 = V[n];
 **    bits(128) result;
 **    bits(128) T = operand2<31:0>:operand1<127:32>;
 **    bits(32) elt;
 **
 **    for e = 0 to 3
 **        elt = Elem[T, e, 32];
 **        elt = ROR(elt, 7) EOR ROR(elt, 18) EOR LSR(elt, 3);
 **        Elem[result, e, 32] = elt + Elem[operand1, e, 32];
 **    V[d] = result;
 **
 **  See
 **    https://developer.arm.com/documentation/ddi0596/2020-12/SIMD-FP-Instructions/SHA256SU0--SHA256-schedule-update-0-
 **)

let sha256su0_loop = define
  `sha256su0_loop (e:num) (t:int128) (d:int128) : int32 =
          let elt0 = elem t e 32 in
          let elt1 = word_xor (word_ror elt0 7)
                              (word_xor (word_ror elt0 18)
                                        (word_ushr elt0 3)) in
          word_add elt1 (elem d e 32)`;;

let sha256su0 = define
  `sha256su0 (d:int128) (n:int128) : int128 =
          let t = (word_join:int32->96 word->int128)
                  (word_subword n (0, 32))
                  (word_subword d (32, 96)) in
          let seq0 = sha256su0_loop 0 t d in
          let seq1 = sha256su0_loop 1 t d in
          let seq2 = sha256su0_loop 2 t d in
          let seq3 = sha256su0_loop 3 t d in
          (word_join:32 word->96 word-> 128 word)
            seq3
            ((word_join:32 word->64 word->96 word)
               seq2
               ((word_join:32 word->32 word->64 word)
                  seq1
                  seq0))`;;

(**
 **  ARM SHA256SU1 pseudocode
 **
 **    Operation
 **
 **    AArch64.CheckFPAdvSIMDEnabled();
 **
 **    bits(128) operand1 = V[d];
 **    bits(128) operand2 = V[n];
 **    bits(128) operand3 = V[m];
 **    bits(128) result;
 **    bits(128) T0 = operand3<31:0>:operand2<127:32>;
 **    bits(64) T1;
 **    bits(32) elt;
 **
 **    T1 = operand3<127:64>;
 **    for e = 0 to 1
 **        elt = Elem[T1, e, 32];
 **        elt = ROR(elt, 17) EOR ROR(elt, 19) EOR LSR(elt, 10);
 **        elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32];
 **        Elem[result, e, 32] = elt;
 **
 **    T1 = result<63:0>;
 **    for e = 2 to 3
 **        elt = Elem[T1, e-2, 32];
 **        elt = ROR(elt, 17) EOR ROR(elt, 19) EOR LSR(elt, 10);
 **        elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32];
 **        Elem[result, e, 32] = elt;
 **
 **    V[d] = result;
 **
 **  See
 **    https://developer.arm.com/documentation/ddi0596/2020-12/SIMD-FP-Instructions/SHA256SU1--SHA256-schedule-update-1-
 **
 **)

let sha256su1_loop0 = define
  `sha256su1_loop0 (e:num) (d:128 word) (t0:128 word) (t1:64 word) : 32 word =
          let elt0 : 32 word = elem t1 e 32 in
          let elt1 : 32 word = word_xor (word_ror elt0 17)
                              (word_xor (word_ror elt0 19)
                                        (word_ushr elt0 10)) in
          let elt2 : 32 word = word_add elt1 (word_add (elem d e 32) (elem t0 e 32)) in
          elt2`;;

let sha256su1_loop1 = define
  `sha256su1_loop1 (e:num) (d:128 word) (t0:128 word) (t1:64 word) : 32 word =
          let elt0 : 32 word = elem t1 (e - 2) 32 in
          let elt1 : 32 word = word_xor (word_ror elt0 17)
                                        (word_xor (word_ror elt0 19)
                                                  (word_ushr elt0 10)) in
          let elt2 : 32 word = word_add elt1 (word_add (elem d e 32) (elem t0 e 32)) in
          elt2`;;

let sha256su1 = define
  `sha256su1 (d:128 word) (n:128 word) (m:128 word) : 128 word =
          let t0   : 128 word = (word_join:32 word->96 word->128 word)
                                (word_subword m (0, 32))
                                (word_subword n (32, 96)) in
          let t1   :  64 word = word_subword m (64, 64) in
          let seq0 :  32 word = sha256su1_loop0 0 d t0 t1 in
          let seq1 :  32 word = sha256su1_loop0 1 d t0 t1 in
          let t1   :  64 word = (word_join:32 word->32 word->64 word) seq1 seq0 in
          let seq2 :  32 word = sha256su1_loop1 2 d t0 t1 in
          let seq3 :  32 word = sha256su1_loop1 3 d t0 t1 in
          (word_join:32 word->96 word->128 word)
            seq3
            ((word_join:32 word->64 word->96 word)
               seq2
               ((word_join:32 word->32 word->64 word)
                  seq1
                  seq0))`;;

(************************************************)
(**                                            **)
(** CONVERSIONS FOR REDUCING SHA256 INTRINSICS **)
(**                                            **)
(************************************************)

(** Reduce template for common functions**)
let SHA_COMMON_REDUCE func =
        REWR_CONV func THENC
        DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let CHOOSE_REDUCE = SHA_COMMON_REDUCE sha_choose ;;
let MAJ_REDUCE    = SHA_COMMON_REDUCE sha_maj ;;
let SIGMA0_REDUCE = SHA_COMMON_REDUCE sha_hash_sigma_0 ;;
let SIGMA1_REDUCE = SHA_COMMON_REDUCE sha_hash_sigma_1 ;;
let ELEM_REDUCE   = SHA_COMMON_REDUCE elem ;;

let BASE_REDUCE =
        MAJ_REDUCE ORELSEC
        CHOOSE_REDUCE ORELSEC
        SIGMA0_REDUCE ORELSEC
        SIGMA1_REDUCE ORELSEC
        ELEM_REDUCE;;

(**
 ** Reduce "let x = e in f" by first reducing "e" via conv
 ** and then expanding the let-term (assuming not "let ... and ... in",
 ** which would need a more elaborate implementation)
 **)
let REDUCE_SUBLET_CONV conv tm =
  if is_let tm then (RAND_CONV conv THENC let_CONV) tm
  else failwith "REDUCE_SUBLET_CONV: not a toplevel let-term";;

(** Now use that to reduce the sha256_hash_loop function **)
let REDUCE_LOOP =
    REWR_CONV sha256hash_loop THENC
    DEPTH_CONV (let_CONV ORELSEC BASE_REDUCE ORELSEC NUM_RED_CONV ) THENC
    WORD_REDUCE_CONV;;

let HASH_REDUCE  =
    REWR_CONV sha256hash THENC
    REPEATC (REDUCE_SUBLET_CONV (REDUCE_LOOP ORELSEC WORD_RED_CONV ORELSEC BASE_REDUCE)) THENC
    ONCE_SIMP_CONV [];;

let REDUCE_SU0_LOOP =
    REWR_CONV sha256su0_loop THENC
    DEPTH_CONV (let_CONV ORELSEC BASE_REDUCE ) THENC
    WORD_REDUCE_CONV;;

let SHA256SU0_RED_CONV =
    REWR_CONV sha256su0 THENC
    DEPTH_CONV (let_CONV ORELSEC REDUCE_SU0_LOOP ORELSEC NUM_RED_CONV) THENC
    WORD_REDUCE_CONV;;

let SHA256SU0_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("sha256su0",_),Comb(Const("word",_),d)),
         Comb(Const("word",_),n))
    when is_numeral d && is_numeral n -> SHA256SU0_RED_CONV tm
  | _ -> failwith "SHA256SU0_CONV: inapplicable";;

let REDUCE_SU1_LOOP0 =
    REWR_CONV sha256su1_loop0 THENC
    DEPTH_CONV (let_CONV ORELSEC BASE_REDUCE ) THENC
    WORD_REDUCE_CONV;;

let REDUCE_SU1_LOOP1 =
    REWR_CONV sha256su1_loop1 THENC
    DEPTH_CONV (let_CONV ORELSEC BASE_REDUCE ) THENC
    WORD_REDUCE_CONV;;

let SHA256SU1_RED_CONV =
    REWR_CONV sha256su1 THENC
    DEPTH_CONV (let_CONV ORELSEC
                REDUCE_SU1_LOOP0 ORELSEC
                REDUCE_SU1_LOOP1) THENC
    WORD_REDUCE_CONV;;

let SHA256SU1_REDUCE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("sha256su1",_),
                  Comb(Const("word",_),d)),
                  Comb(Const("word",_),n)),
                  Comb(Const("word",_),m))
      when is_numeral d && is_numeral n && is_numeral m -> SHA256SU1_RED_CONV tm
    | _ -> failwith "SHA256SU1_CONV: inapplicable";;

let SHA256H_RED_CONV =
        REWR_CONV sha256h THENC HASH_REDUCE;;

let SHA256H_REDUCE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("sha256h",_),
                  Comb(Const("word",_),d)),
                  Comb(Const("word",_),n)),
                  Comb(Const("word",_),m))
      when is_numeral d && is_numeral n && is_numeral m -> SHA256H_RED_CONV tm
    | _ -> failwith "SHA256H_CONV: inapplicable";;

let SHA256H2_RED_CONV =
        REWR_CONV sha256h2 THENC HASH_REDUCE;;

let SHA256H2_REDUCE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("sha256h2",_),
                  Comb(Const("word",_),d)),
                  Comb(Const("word",_),n)),
                  Comb(Const("word",_),m))
      when is_numeral d && is_numeral n && is_numeral m -> SHA256H2_RED_CONV tm
    | _ -> failwith "SHA256H2_CONV: inapplicable";;

