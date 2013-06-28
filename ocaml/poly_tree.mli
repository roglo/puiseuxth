(* $Id: poly_tree.mli,v 1.49 2013-06-28 09:01:21 deraugla Exp $ *)

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

value string_of_tree :
  field α (ext α _) → bool → string → string → tree α → string;
value airy_string_of_tree :
  field α (ext α _) → bool → string → string → tree α → string;

value tree_of_ast : field α (ext α _) → string → string → MLast.expr → tree α;
value xpower : Q.t → tree α;

value tree_polyn_of_tree : field α (ext α _) → tree α → polynomial (tree α);
value puiseux_series_of_tree : field α (ext α _) → tree α → puiseux_series α;

value ps_polyn_of_tree :
  field α (ext α _) → tree α → polynomial (puiseux_series α);

value tree_of_puiseux_series :
  field α (ext α _) → bool → puiseux_series α → tree α;
value rev_tree_of_polyn :
  field α (ext α _) → polynomial α → tree α;
value tree_of_ps_polyn :
  field α (ext α _) → bool → polynomial (puiseux_series α) → tree α;

value normalise : field α (ext α _) → tree α → tree α;
