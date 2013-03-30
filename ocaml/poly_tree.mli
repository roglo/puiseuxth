(* $Id: poly_tree.mli,v 1.20 2013-03-30 08:56:54 deraugla Exp $ *)

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

type polynomial α β = { monoms : list (monomial α β) }
and monomial α β = { coeff : α; power : β };

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
value xpower : Q.t → tree α;

value y_polyn_of_tree : field α → tree α → polynomial (tree α) int;
value x_polyn_of_tree : field α → tree α → polynomial α Q.t;

value xy_polyn_of_tree :
  field α → tree α → polynomial (polynomial α Q.t) int;

value tree_of_x_polyn : field α → polynomial α Q.t → tree α;
value tree_of_y_polyn : field α → polynomial α int → tree α;

value tree_of_xy_polyn :
  field α → polynomial (polynomial α Q.t) int → tree α;

value normalise : field α → tree α → tree α;
