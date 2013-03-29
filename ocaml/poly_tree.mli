(* $Id: poly_tree.mli,v 1.12 2013-03-29 19:46:40 deraugla Exp $ *)

open Pnums;
open Field;

type tree α =
  [ Plus of tree α and tree α
  | Minus of tree α and tree α
  | Neg of tree α
  | Mult of tree α and tree α
  | Xpower of int and int
  | Ypower of int
  | Const of α ]
;

type monomial α β = { coeff : α; power : β };
type term_descr α = { const : α; xpow : Q.t; ypow : int };

value tree_map : (α → β) → tree α → tree β;

value string_of_tree :
  field α → bool → string → string → tree α → string;
value airy_string_of_tree :
  field α → bool → string → string → tree α → string;

value tree_of_ast : field α → string → string → MLast.expr → tree α;
value flatten : tree α → list (tree α) → list (tree α);
value term_descr_of_term : field α → tree α → term_descr α;
value without_initial_neg : field α → tree α → option (tree α);
value substitute_y : field α → tree α → tree α → tree α;

value tree_pow_list_y : field α → tree α → list (monomial (tree α) int);
value const_pow_list_x : field α → tree α → list (monomial α Q.t);

value group : field α → tree α → list (monomial (list (monomial α Q.t)) int);
value normalize : field α → tree α → tree α;
