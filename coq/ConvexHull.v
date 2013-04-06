(* $Id: ConvexHull.v,v 1.9 2013-04-06 02:56:53 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Notation "[ ]" := nil.
Notation "[ x , .. , y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Fixpoint minimise_slope xy₁ xy_min sl_min sk_min skip₁ xyl :=
  let (x₁, y₁) := (xy₁ : Q * Q) in
  match xyl with
  | [(x₂, y₂) … xyl₂] =>
      let sl₁₂ := (y₂ - y₁) / (x₂ - x₁) in
      if Qle_bool sl₁₂ sl_min then
        minimise_slope xy₁ (x₂, y₂) sl₁₂ skip₁ (S skip₁) xyl₂
      else
        minimise_slope xy₁ xy_min sl_min sk_min (S skip₁) xyl₂
  | [] =>
      (xy_min, sk_min)
  end.

Fixpoint next_points rev_list nb_pts_to_skip xy₁ xyl₁ :=
  let (x₁, y₁) := (xy₁ : Q * Q) in
  match xyl₁ with
  | [(x₂, y₂) … xyl₂] =>
      match nb_pts_to_skip with
      | 0%nat =>
          let (xy, skip) :=
            let sl₁₂ := (y₂ - y₁) / (x₂ - x₁) in
            minimise_slope xy₁ (x₂, y₂) sl₁₂ 0%nat 1%nat xyl₂
          in
          next_points [xy … rev_list] skip xy xyl₂
      | S n =>
          next_points rev_list n xy₁ xyl₂
      end
  | [] =>
      List.rev rev_list
  end.

Definition lower_convex_hull xyl :=
  match xyl with
  | [xy₁ … xyl₁] => [xy₁ … next_points [] 0%nat xy₁ xyl₁]
  | [] => []
  end.
