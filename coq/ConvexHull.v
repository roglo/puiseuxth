(* $Id: ConvexHull.v,v 1.10 2013-04-09 09:13:52 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Notation "[ ]" := nil.
Notation "[ x , .. , y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Fixpoint minimise_slope x₁ y₁ x_min y_min sl_min sk_min skip₁ xyl :=
  match xyl with
  | [(x₂, y₂) … xyl₂] =>
      let sl₁₂ := (y₂ - y₁) / (x₂ - x₁) in
      if Qle_bool sl₁₂ sl_min then
        minimise_slope x₁ y₁ x₂ y₂ sl₁₂ skip₁ (S skip₁) xyl₂
      else
        minimise_slope x₁ y₁ x_min y_min sl_min sk_min (S skip₁) xyl₂
  | [] =>
      ((x_min, y_min), sk_min)
  end.

Fixpoint next_points rev_list nb_pts_to_skip x₁ y₁ xyl₁ :=
  match xyl₁ with
  | [(x₂, y₂) … xyl₂] =>
      match nb_pts_to_skip with
      | 0%nat =>
          let (xy₃, skip) :=
            let sl₁₂ := (y₂ - y₁) / (x₂ - x₁) in
            minimise_slope x₁ y₁ x₂ y₂ sl₁₂ 0%nat 1%nat xyl₂
          in
          next_points [xy₃ … rev_list] skip (fst xy₃) (snd xy₃) xyl₂
      | S n =>
          next_points rev_list n x₁ y₁ xyl₂
      end
  | [] =>
      List.rev rev_list
  end.

Definition lower_convex_hull xyl :=
  match xyl with
  | [(x₁, y₁) … xyl₁] => [(x₁, y₁) … next_points [] 0%nat x₁ y₁ xyl₁]
  | [] => []
  end.
