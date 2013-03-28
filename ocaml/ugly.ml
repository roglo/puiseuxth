(* $Id: ugly.ml,v 1.6 2013-03-28 20:01:35 deraugla Exp $ *)

(* program for François Delebecque *)

open Pnums;
open Field;
open Poly_parse;
open Poly_print;
open Poly_tree;
open Printf;

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

value print_term n (cpl, py) = do {
  while n.val < py do {
    printf "a%d=mlist(['fracp','varn','dgs','coeffs'],'z',[0;1],[0])  //s%d\n"
      n.val n.val;
    incr n;
  };
  printf "a%d=mlist(['fracp','varn','dgs','coeffs'],'z'," n.val;
  printf "[";
  iter_with_sep " " (fun s (c, px) → printf "%s%s" s (I.ts (Q.rnum px))) cpl;
  printf ";";
  iter_with_sep " " (fun s (c, px) → printf "%s%s" s (I.ts (Q.rden px))) cpl;
  printf "],[";
  iter_with_sep " " (fun s (c, px) → printf "%s%s" s (C.to_string False c))
    cpl;
  printf "]";
  printf ")  //s%d\n" n.val;
  incr n
};

value main () = do {
  let s = Sys.argv.(1) in
  let vx = "x" in
  let vy = "y" in
  let k =
    let imul i a = C.muli a (I.of_int i) in
    {zero = C.zero; one = C.one; add = C.add; sub = C.sub; neg = C.neg;
     mul = C.mul; div = C.div; minus_one = C.minus_one; eq = C.eq;
     imul = imul; norm = C.norm; neg_factor = C.neg_factor;
     to_string = C.to_string False}
  in
  let p = parse_poly s in
  let t = tree_of_ast k vx vy p in
  let si = string_of_tree k False vx vy t in
  let t = normalize k t in
  let sn = string_of_tree k False vx vy t in
  eprintf "%s\n%!" si;
  if sn <> si then eprintf "%s\n%!" sn else ();
  eprintf "\n%!";
  let cplpl = group k t in
  let n = ref 0 in
  List.iter (print_term n) cplpl;
  printf "\n";
  printf "Walker=mlist(['psfz','dg','cofs'],%d," (pred n.val);
  printf "list(";
  let s = ref "" in
  loop 0 where rec loop i =
    if i < n.val then do {
      printf "%sa%d" s.val i;
      s.val := ",";
      loop (succ i);
    }
    else ();
  printf "));\n";
};

main ();
