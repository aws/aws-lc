(* ========================================================================= *)
(* Generate known-answer test cases for fixed-size P-384 functions           *)
(* ========================================================================= *)

#use "topfind";;
#require "num";;
open Num;;

let print_num n = print_string(string_of_num n);;
#install_printer print_num;;

(* ------------------------------------------------------------------------- *)
(* Misc convenient functions.                                                *)
(* ------------------------------------------------------------------------- *)

let num_0 = num 0 and num_1 = num 1 and num_2 = num 2;;

let pow2 n = power_num num_2 (num n);;

let ( ** ) = fun f g x -> f(g x);;

let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);;

let rec funpow n f x =
  if n < 1 then x else funpow (n-1) f (f x);;

let hd l =
  match l with
   h::t -> h
  | _ -> failwith "hd";;

let tl l =
  match l with
   h::t -> t
  | _ -> failwith "tl";;

let map f =
  let rec mapf l =
    match l with
      [] -> []
    | (x::t) -> let y = f x in y::(mapf t) in
  mapf;;

let rev =
  let rec rev_append acc l =
    match l with
      [] -> acc
    | h::t -> rev_append (h::acc) t in
  fun l -> rev_append [] l;;

let length =
  let rec len k l =
    if l = [] then k else len (k + 1) (tl l) in
  fun l -> len 0 l;;

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec end_itlist f l =
  match l with
        []     -> failwith "end_itlist"
      | [x]    -> x
      | (h::t) -> f h (end_itlist f t);;

let rec allpairs f l1 l2 =
  match l1 with
   h1::t1 ->  itlist (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
  | [] -> [];;

(* ------------------------------------------------------------------------- *)
(* Generate pseudo-random number < k.                                        *)
(* ------------------------------------------------------------------------- *)

let rec random_num k =
  if k <=/ pow2 29 then num(Random.int(int_of_num(floor_num k)))
  else num(Random.int(1 lsl 29)) +/ pow2 29 */ random_num (k // pow2 29);;

(* ------------------------------------------------------------------------- *)
(* The key numbers p and n, some extra mathematical functions.               *)
(* ------------------------------------------------------------------------- *)

let p = num_of_string "39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319";;

let np = num_of_string "39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643";;

let double_mod p x = mod_num (num_2 */ x) p;;

let half_mod p x =
  mod_num (quo_num (if mod_num x num_2 =/ num_0 then x else x +/ p) num_2) p;;

let bigdigit n i = mod_num (quo_num n (pow2 (64 * i))) (pow2 64);;

let byte n i = mod_num (quo_num n (pow2 (8 * i))) (pow2 8);;

let bigdigits n = map (bigdigit n) (0--5);;

let bytes n = map (byte n) (0--47);;

let fromdigits l = itlist (fun h t -> h +/ pow2 64 */ t) l num_0;;

let frombytes l = itlist (fun h t -> h +/ pow2 8 */ t) l num_0;;

let bytereverse n = frombytes (rev (map (byte n) (0--7)));;

(* ------------------------------------------------------------------------- *)
(* String conversion functions.                                              *)
(* ------------------------------------------------------------------------- *)

let string_of_num_nary =
  let digits = ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9";
                "a"; "b"; "c"; "d"; "e"; "f"] in
  let rec ell n l =
    if n =/ num_0 then hd l
    else ell(n -/ num_1) (tl l) in
  let rec string_of_num ten n =
    let n0 = mod_num n ten
    and n1 = quo_num n ten in
    let d0 = ell n0 digits in
    if n1 =/ num_0 then d0 else (string_of_num ten n1)^d0 in
  fun b n -> string_of_num (num b) n;;

let string_of_padded_hex k n =
  let s = string_of_num_nary 16 (abs_num n) in
  let p = "0x" ^ String.make (k - String.length s) '0' ^ s in
  if n </ num_0 then "-"^p else p;;

let string_of_digit n =
  if num_0 <=/ n && n </ pow2 64
  then string_of_padded_hex 16 n
  else failwith "string_of_digit";;

let string_of_digits n =
  let strs = map (string_of_digit ** bigdigit n) (0--5) in
  end_itlist (fun s t -> s ^ "," ^ t) strs;;

let string_of_directive p (x,n) =
  p ^ "(" ^ x ^ "," ^ string_of_digits n ^ ");";;

let string_of_uint64 n =
  if num_0 <=/ n && n </ pow2 64
  then "UINT64_C(" ^ string_of_padded_hex 16 n ^ ")"
  else failwith "string_of_uint64digit";;

let string_of_directive1 p (x,n) =
  p ^ "(" ^ x ^ "," ^ string_of_digit n ^ ");";;

(* ------------------------------------------------------------------------- *)
(* Generate n cases with special and random cases, < p_384 or < 2^384        *)
(* ------------------------------------------------------------------------- *)

let word n = map (fun _ -> random_num (pow2 64)) (1--n);;

let full n =
  let fixed = [num_0; p -/ num_1; p; pow2 384 -/ num_1 ] in
  fixed @ map (fun _ -> random_num (pow2 384))
              (1--(max 0 (n - length fixed)));;

let limited n =
  let fixed = [num_0; p -/ num_1] in
  fixed @ map (fun _ -> random_num p)
              (1--(max 0 (n - length fixed)));;

(* ------------------------------------------------------------------------- *)
(* Generate tests.                                                           *)
(* ------------------------------------------------------------------------- *)

let unary_test fname fmath x =
  let w = random_num (pow2 384) and z = fmath x in
  string_of_directive "ASSIGN6" ("b0",w) ^ "\n" ^
  string_of_directive "ASSIGN6" ("b1",x) ^ "\n" ^
  fname ^ "(b0,b1);" ^ "\n" ^
  string_of_directive "CHECK6" ("b0",z) ^ "\n\n";;

let unary_tests n src fname fmath =
  map (unary_test fname fmath) (src n);;

let binary_test fname fmath x y =
  let w = random_num (pow2 384) and z = fmath x y in
  string_of_directive "ASSIGN6" ("b0",w) ^ "\n" ^
  string_of_directive "ASSIGN6" ("b1",x) ^ "\n" ^
  string_of_directive "ASSIGN6" ("b2",y) ^ "\n" ^
  fname ^ "(b0,b1,b2);" ^ "\n" ^
  string_of_directive "CHECK6" ("b0",z) ^ "\n\n";;

let binary_tests n src fname fmath =
  allpairs (binary_test fname fmath) (src n) (src n);;

let binary1_test fname fmath x y =
  let w = random_num (pow2 384) and z = fmath x y in
  string_of_directive "ASSIGN6" ("b0",w) ^ "\n" ^
  string_of_directive1 "ASSIGN1" ("b1",x) ^ "\n" ^
  string_of_directive "ASSIGN6" ("b2",y) ^ "\n" ^
  fname ^ "(b0,b1[0],b2);" ^ "\n" ^
  string_of_directive "CHECK6" ("b0",z) ^ "\n\n";;

let binary1_tests n src fname fmath =
  allpairs (binary1_test fname fmath) (word n) (src n);;

let unaryp_test fname fmath x =
  let w = random_num (pow2 64) and z = fmath x in
  string_of_directive1 "ASSIGN1" ("b0",w) ^ "\n" ^
  string_of_directive "ASSIGN6" ("b1",x) ^ "\n" ^
  "b0[0] = " ^ fname ^ "(b1);" ^ "\n" ^
  string_of_directive1 "CHECK1" ("b0",z) ^ "\n\n";;

let unaryp_tests n src fname fmath =
  map (unaryp_test fname fmath) (src n);;

let ternary1_test fname fmath p x y =
  let w = random_num (pow2 384) and z = fmath p x y in
  string_of_directive "ASSIGN6" ("b0",w) ^ "\n" ^
  string_of_directive1 "ASSIGN1" ("b1",p) ^ "\n" ^
  string_of_directive "ASSIGN6" ("b2",x) ^ "\n" ^
  string_of_directive "ASSIGN6" ("b3",y) ^ "\n" ^
  fname ^ "(b1[0],b0,b2,b3);" ^ "\n" ^
  string_of_directive "CHECK6" ("b0",z) ^ "\n\n";;

let ternary1_tests n src fname fmath =
  allpairs (ternary1_test fname fmath num_0) (word n) (src n) @
  allpairs (ternary1_test fname fmath num_1) (word n) (src n) @
  allpairs (ternary1_test fname fmath (random_num (pow2 64))) (word n) (src n) @
  allpairs (ternary1_test fname fmath (pow2 64 -/ num_1)) (word n) (src n);;

(* ------------------------------------------------------------------------- *)
(* The current list of tests                                                 *)
(* ------------------------------------------------------------------------- *)

let file_of_string filename s =
  let fd = Pervasives.open_out filename in
  output_string fd s; close_out fd;;

let alltests = (end_itlist (^) ** end_itlist (@))
 [binary_tests 10 limited "bignum_add_p384"
   (fun x y -> mod_num (x +/ y) p);

  binary1_tests 10 limited "bignum_cmul_p384"
   (fun x y -> mod_num (x */ y) p);

  unary_tests 100 full "bignum_deamont_p384"
   (fun x -> funpow 384 (half_mod p) (mod_num x p));

  unary_tests 100 limited "bignum_demont_p384"
   (fun x -> funpow 384 (half_mod p) (mod_num x p));

  unary_tests 100 limited "bignum_double_p384"
   (fun x -> mod_num (num_2 */ x) p);

  unary_tests 100 limited "bignum_half_p384"
   (fun x -> half_mod p x);

  unary_tests 100 full "bignum_mod_n384_6"
   (fun x -> mod_num x np);

  unary_tests 100 full "bignum_mod_p384_6"
   (fun x -> mod_num x p);

  ternary1_tests 5 full "bignum_mux_6"
   (fun p x y -> if p =/ num_0 then y else x);

  binary_tests 10 limited "bignum_montmul_p384"
   (fun x y -> funpow 384 (half_mod p) (x */ y));

  unary_tests 100 limited "bignum_montsqr_p384"
   (fun x -> funpow 384 (half_mod p) (x */ x));

  unary_tests 100 limited "bignum_neg_p384"
   (fun x -> mod_num (p -/ x) p);

  unaryp_tests 100 full "bignum_nonzero_6"
   (fun x -> if x =/ num_0 then num_0 else num_1);

  binary1_tests 10 limited "bignum_optneg_p384"
   (fun x y -> mod_num (if x =/ num_0 then y else p -/ y) p);

  binary_tests 10 limited "bignum_sub_p384"
   (fun x y -> mod_num (x -/ y) p);

  unary_tests 100 full "bignum_tomont_p384"
   (fun x -> mod_num (pow2 384 */ x) p);

  unary_tests 100 full "bignum_triple_p384"
   (fun x -> mod_num (num 3 */ x) p);

(*** These two are endian-specific. All s2n-bignum numbers are
 *** stored with the words in little-endian order, but the byte
 *** order within the words depends on the architecture.
 *** The bytes of n = sum_i (256^i * b_i) in the s2n-bignum format are
 ***
 *** n0, n1, ..., n7, n8, n9, ...., n47 [little-endian machine]
 *** n7, n6, ..., n0, n15, n14, ..., n40 [big-endian machine]
 ***
 *** The "littlendian" function transforms to pure little-endian bytes,
 *** just as the number already is on a little-endian machine, while
 *** "bigendian"gives a pure big-endian byte sequence
 ***
 *** n47, n46, ...., n2, n1, n0
 ***
 *** So:
 ***  - on a *little-endian* machine "littlendian" is the identity
 ***    and "bigendian" reverses bytes completely.
 ***  - on a *big-endian* machine "littlendian" keeps word order but
 ***    reverses the bytes within each word, "bigendian" reverses words.
 *** and all four operations are involutions (f o f = identity).
 ***)

  ["if ((*(uint16_t *)\"\\0\\xff\" < 0x100)) {\n"];

  unary_tests 100 full "bignum_bigendian_6"
   (fun x -> fromdigits (map bytereverse (bigdigits x)));

  unary_tests 100 full "bignum_littleendian_6"
   (fun x -> fromdigits (rev (bigdigits x)));

  ["} else {\n"];

  unary_tests 100 full "bignum_bigendian_6"
   (fun x -> frombytes (rev (bytes x)));

  unary_tests 100 full "bignum_littleendian_6"
   (fun x -> x);

 ["}"]
 ] in

file_of_string "/tmp/known_value_tests_p384.h" alltests;;
