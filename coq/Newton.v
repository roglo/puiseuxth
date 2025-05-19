(* Newton.v *)

From Stdlib Require Import Utf8.

Require Import QGArith.
Require Import ConvexHull.

Set Implicit Arguments.

Definition γ ns :=
  (snd (ini_pt ns) - snd (fin_pt ns)) /
    (QG_of_nat (fst (fin_pt ns)) - QG_of_nat (fst (ini_pt ns))).

Definition β ns :=
  snd (ini_pt ns) + QG_of_nat (fst (ini_pt ns)) * γ ns.
