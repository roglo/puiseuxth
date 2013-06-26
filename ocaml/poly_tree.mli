(* $Id: poly_tree.mli,v 1.40 2013-06-26 16:27:49 deraugla Exp $ *)

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

(* *)

type old_ps α = { old_ps_mon : list (term α) };

value ps2ops : old_puiseux_series α → old_ps α;
value ops2ps : old_ps α → old_puiseux_series α;

(* *)

value string_of_tree :
  field α (ext α _) → bool → string → string → tree α → string;
value airy_string_of_tree :
  field α (ext α _) → bool → string → string → tree α → string;

value tree_of_ast : field α (ext α _) → string → string → MLast.expr → tree α;
value xpower : Q.t → tree α;

value tree_polyn_of_tree : field α (ext α _) → tree α → old_poly (tree α);
value puiseux_series_of_tree : field α (ext α _) → tree α → old_ps α;

value ps_polyn_of_tree :
  field α (ext α _) → tree α → old_poly (old_ps α);

value tree_of_old_puiseux_series : field α (ext α _) → bool → old_ps α → tree α;
value rev_tree_of_polyn : field α (ext α _) → old_poly α → tree α;
value tree_of_ps_polyn : field α (ext α _) → bool → old_poly (old_ps α) → tree α;

value normalise : field α (ext α _) → tree α → tree α;
