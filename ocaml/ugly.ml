(* $Id: ugly.ml,v 1.46 2013-06-27 09:04:34 deraugla Exp $ *)

(* program for François Delebecque *)

open Pnums;
open Field;
open Poly_parse;
open Poly_print;
open Poly_tree;
open Poly;
open Puiseux_series;
open Printf;
open Series;

(*
./ugly '(-x³+x⁴)-2x²y-xy²+2xy⁴+y⁵'
./ugly '(-x^3+x^4) - (2 *x^2 * y) - x*y^2 + 2*x*y^4 +y^5'

a0=mlist(['fracp','varn','dgs','coeffs'],'z',[3 4;1 1],[-1 1])  //s0
a1=mlist(['fracp','varn','dgs','coeffs'],'z',[2;1],[-2])  //s1
a2=mlist(['fracp','varn','dgs','coeffs'],'z',[1;1],[-1])  //s2
a3=mlist(['fracp','varn','dgs','coeffs'],'z',[0;1],[0])  //s3
a4=mlist(['fracp','varn','dgs','coeffs'],'z',[1;1],[2])  //s4
a5=mlist(['fracp','varn','dgs','coeffs'],'z',[0;1],[1])  //s5

Walker=mlist(['psfz','dg','cofs'],5,list(a0,a1,a2,a3,a4,a5));
*)

value iter_with_sep s f l =
  let _ = List.fold_left (fun s x → do { f s x; " " }) "" l in ()
;

value ps2ops ps =
  let rec loop lim ms =
    if lim = 0 then []
    else
      match ms with
      | Term m₁ ms₁ → [m₁ :: loop (lim - 1) (Lazy.force ms₁)]
      | End → []
      end
  in
  loop (-1) ps.ps_terms
;

value print_term deg m = do {
  let m = ps_of_ms m in
  printf "a%d=mlist(['fracp','varn','dgs','coeffs'],'z'," deg;
  let ml =
    let m = ps2ops m in
    if m = [] then [{coeff = C.zero; power = Q.zero}] else m
  in
  printf "[";
  iter_with_sep " " (fun s mx → printf "%s%s" s (I.ts (Q.rnum mx.power))) ml;
  printf ";";
  iter_with_sep " " (fun s mx → printf "%s%s" s (I.ts (Q.rden mx.power))) ml;
  printf "],[";
  iter_with_sep " " (fun s mx → printf "%s%s" s (C.to_string False mx.coeff))
    ml;
  printf "]";
  printf ")  //s%d\n" deg;
};

value kc () =
  let ext =
    {minus_one = C.minus_one; equal = C.eq; compare _ = failwith "kc.compare";
     gcd = C.gcd; normalise = C.normalise; nth_root = C.nth_root;
     neg_factor = C.neg_factor; of_i = C.of_i;
     of_q = C.of_q; of_a = C.of_a; of_complex = C.of_complex;
     of_float_string = C.of_float_string; to_q = C.to_q; to_a = C.to_a;
     to_complex = C.to_complex; to_string = C.to_string False;
     float_round_zero = C.float_round_zero;
     complex_round_zero = C.complex_round_zero; complex_mul = C.complex_mul;
     cpoly_roots = C.cpoly_roots; complex_to_string = C.complex_to_string}
   in
  {zero = C.zero; one = C.one; add = C.add; sub = C.sub; neg = C.neg;
   mul = C.mul; div = C.div; is_zero = C.eq C.zero; ext = ext}
;

value main () = do {
  let s = Sys.argv.(1) in
  let vx = "x" in
  let vy = "y" in
  let k = kc () in
  let p = parse_poly s in
  let t = tree_of_ast k vx vy p in
  let si = string_of_tree k False vx vy t in
  let t = normalise k t in
  let sn = string_of_tree k False vx vy t in
  eprintf "%s\n%!" si;
  if sn <> si then eprintf "%s\n%!" sn else ();
  eprintf "\n%!";
  let pol = ps_polyn_of_tree k t in
  List.iteri print_term (pol.al @ [pol.an]);
  printf "\n";
  let deg = List.length pol.al in
  printf "Walker=mlist(['psfz','dg','cofs'],%d," deg;
  printf "list(";
  let s = ref "" in
  loop 0 where rec loop i =
    if i ≤ deg then do {
      printf "%sa%d" s.val i;
      s.val := ",";
      loop (succ i);
    }
    else ();
  printf "));\n";
};

main ();
