(* $Id: Newton.v,v 1.1 2013-06-19 09:34:35 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Require Import ConvexHull.

Set Implicit Arguments.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Record newton_segment := mkns
  { γ : Q;
    β : Q;
    ini_pt : (Q * Q);
    fin_pt : (Q * Q);
    oth_pts : list (Q * Q) }.

Fixpoint list_map_pairs α β (f : α → α → β) l :=
  match l with
  | [] => []
  | [x₁] => []
  | [x₁ … ([x₂ … l₂] as l₁)] => [f x₁ x₂ … list_map_pairs f l₁]
  end.

Definition newton_segment_of_pair hsj hsk :=
  let αj := snd (pt hsj) in
  let αk := snd (pt hsk) in
  let γ := (αj - αk) / (fst (pt hsk) - fst (pt hsj)) in
  let β := αj + fst (pt hsj) * γ in
  mkns γ β (pt hsj) (pt hsk) (oth hsj).
