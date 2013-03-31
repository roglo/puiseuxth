(* $Id: poly_tree.mli,v 1.23 2013-03-31 22:09:23 deraugla Exp $ *)

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
type polynomial α β = { monoms : list (monomial α β) };

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
value merge_expr_pow :
  field α β → (γ → γ → bool) →
    (field α β → δ → δ → γ → list (monomial δ γ) → list (monomial δ γ)) →
    list (monomial δ γ) → list (monomial δ γ);

value y_polyn_of_tree : field α _ → tree α → polynomial (tree α) int;
value x_polyn_of_tree : field α _ → tree α → polynomial α Q.t;

value xy_polyn_of_tree :
  field α _ → tree α → polynomial (polynomial α Q.t) int;

value tree_of_x_polyn : field α _ → polynomial α Q.t → tree α;
value tree_of_y_polyn : field α _ → polynomial α int → tree α;

value tree_of_xy_polyn :
  field α _ → polynomial (polynomial α Q.t) int → tree α;

value normalise : field α _ → tree α → tree α;
