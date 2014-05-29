(* Newton.v *)

Require Import Utf8.
Require Import QArith.

Require Import ConvexHull.

Set Implicit Arguments.

Definition γ ns :=
  (snd (ini_pt ns) - snd (fin_pt ns)) / (fst (fin_pt ns) - fst (ini_pt ns)).

Definition β ns :=
  snd (ini_pt ns) + fst (ini_pt ns) * γ ns.
