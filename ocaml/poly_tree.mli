(* $Id: poly_tree.mli,v 1.2 2013-03-28 16:16:42 deraugla Exp $ *)

open Pnums;
open Pnums_sig;

type tree α =
  [ Plus of tree α and tree α
  | Minus of tree α and tree α
  | Neg of tree α
  | Mult of tree α and tree α
  | Xpower of int and int
  | Ypower of int
  | Const of α ]
;

type term_descr α = { const : α; xpow : Q.t; ypow : int };

value tree_of_ast : field C.t → string → string → MLast.expr → tree C.t;
value string_of_tree : field α → bool → string → string → tree α → string;
value airy_string_of_tree : field α → bool → string → string → tree α → string;
value flatten : tree α → list (tree α) → list (tree α);
value term_descr_of_term : field α → tree α → term_descr α;
value without_initial_neg : tree C.t → option (tree C.t);
value group : field C.t → tree C.t → list (list (C.t * Q.t) * int);
value substitute_y : field C.t → tree C.t → tree C.t → tree C.t;
value tree_pow_list_y : field α → tree α → list (tree α * int);
value const_pow_list_x : field α → tree α → list (α * Q.t);

value normalize : field C.t → tree C.t → tree C.t;
