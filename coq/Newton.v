(* Newton.v *)

From Stdlib Require Import Utf8.
From Stdlib Require Import QArith.

Require Import Misc ConvexHull.

Set Implicit Arguments.

Definition γ ns :=
  (snd (ini_pt ns) - snd (fin_pt ns)) /
    (Qnat (fst (fin_pt ns)) - Qnat (fst (ini_pt ns))).

Definition β ns :=
  snd (ini_pt ns) + Qnat (fst (ini_pt ns)) * γ ns.
