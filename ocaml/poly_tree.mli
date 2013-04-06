(* $Id: poly_tree.mli,v 1.28 2013-04-06 11:07:28 deraugla Exp $ *)

open Pnums;
open Field;
open Poly;
open Puiseux_series;

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

value tree_map : (α → β) → tree α → tree β;

value string_of_tree :
  field α _ → bool → string → string → tree α → string;
value airy_string_of_tree :
  field α _ → bool → string → string → tree α → string;

value tree_of_ast : field α _ → string → string → MLast.expr → tree α;
value flatten : tree α → list (tree α) → list (tree α);
value term_descr_of_term : field α _ → tree α → term_descr α;
value without_initial_neg : field α _ → tree α → option (tree α);
value substitute_y : field α _ → tree α → tree α → tree α;
value xpower : Q.t → tree α;
value merge_expr_pow₂ :
  field α β → (Q.t → Q.t → bool) →
    (field α β → δ → δ → Q.t → list (monomial₂ δ) → list (monomial₂ δ)) →
    list (monomial₂ δ) → list (monomial₂ δ);

value tree_polyn_of_tree : field α _ → tree α → old_polynomial (tree α);
value puiseux_series_of_tree : field α _ → tree α → puiseux_series α;

value ps_polyn_of_tree :
  field α _ → tree α → old_polynomial (puiseux_series α);

value tree_of_puiseux_series : field α _ → puiseux_series α → tree α;
value tree_of_polyn : field α _ → old_polynomial α → tree α;
value tree_of_ps_polyn : field α _ → old_polynomial (puiseux_series α) → tree α;

value normalise : field α _ → tree α → tree α;
