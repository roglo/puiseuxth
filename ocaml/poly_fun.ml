(* $Id: poly_fun.ml,v 1.1 2013-03-28 13:24:20 deraugla Exp $ *)

open Printf;
open Pnums;

value prod_int_poly_rat_monom a (c, p) =
  if p < 0 then invalid_arg "prod_int_poly_rat_monom"
  else
    let b = List.map (Q.muli c) a in
    loop b p where rec loop b p =
      if p = 0 then b
      else loop [Q.zero :: b] (p - 1)
;

value int_poly_of_rat_poly a =
  let a = List.map Q.norm a in
  let l = List.fold_left (fun l q → I.lcm l (Q.rden q)) I.one a in
  List.map (fun q → I.mul (Q.rnum q) (I.div l (Q.rden q))) a
;

value diff_rat_poly a b =
  let alen = List.length a in
  let blen = List.length b in
  if alen < blen then
    failwith (sprintf "diff_rat_poly alen %d < blen %d" alen blen)
  else if alen = blen then
    let r = List.map2 (fun ca cb → Q.sub ca cb) a b in
    loop (List.rev r) where rec loop =
      fun
      [ [r :: rl] when I.eq (Q.rnum r) I.zero → loop rl
      | rev_rl → List.rev rev_rl ]
  else
    failwith (sprintf "diff_rat_poly alen %d > blen %d" alen blen)
;

value poly_of_poly_pow =
  loop 0 where rec loop deg =
    fun
    [ [(c, n) :: cnl] →
        if n > deg then [Q.zero :: loop (deg + 1) [(c, n) :: cnl]]
        else if n = deg then [c :: loop (deg + 1) cnl]
        else invalid_arg "poly_of_poly_pow"
    | [] -> [] ]
;

value poly_eucl_div a b =
  let blen = List.length b in
  if blen = 0 then invalid_arg "poly_eucl_div"
  else
    let a = List.map Q.of_i a in
    let bm = List.nth b (blen - 1) in
    loop [] a where rec loop ql a =
      let alen = List.length a in
      if alen < blen then
        let ql = poly_of_poly_pow ql in
        (int_poly_of_rat_poly ql, int_poly_of_rat_poly a)
      else
        let an = List.nth a (alen - 1) in
        let q = (Q.norm (Q.divi an bm), alen - blen) in
        let bq = prod_int_poly_rat_monom b q in
        let r = diff_rat_poly a bq in
        loop [q :: ql] r
;

value rec poly_gcd a b =
  if b = [] then
    let g = List.fold_left I.gcd I.zero a in
    List.map (fun c → I.div c g) a
  else
    let (q, r) = poly_eucl_div a b in
    poly_gcd b r
;
