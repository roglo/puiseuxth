(* $Id: ConvexHull.v,v 1.5 2013-04-04 16:21:09 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Notation "[ ]" := nil.
Notation "[ x , .. , y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Record slope_to (α : Set) := { xy₂ : (α * α); slope : α; skip : nat }.
Arguments xy₂ : default implicits.
Arguments slope : default implicits.
Arguments skip : default implicits.

Record monomial α β := { coeff : α; power : β }.
Arguments coeff : default implicits.
Arguments power : default implicits.

Record polynomial α β := { monoms : list (monomial α β) }.
Arguments monoms : default implicits.

Record alg_cl_field α :=
  { zero : α;
    sub : α → α → α;
    div : α → α → α;
    roots : polynomial α nat → list (α * nat) }.
Arguments zero : default implicits.
Arguments sub : default implicits.
Arguments div : default implicits. 
Arguments roots : default implicits. 

Fixpoint minimise_slope xy₁ slt_min₁ skip₁ xyl :=
  let (x₁, y₁) := (xy₁ : Q * Q) in
  match xyl with
  | [(x₂, y₂) … xyl₂] =>
      let sl₁₂ := (y₂ - y₁) / (x₂ - x₁) in
      let slt_min :=
        if Qle_bool sl₁₂ (slope slt_min₁) then
          {| xy₂ := (x₂, y₂); slope := sl₁₂; skip := skip₁ |}
        else
          slt_min₁
      in
      minimise_slope xy₁ slt_min (S skip₁) xyl₂
  | [] =>
      slt_min₁
  end.

Fixpoint next_points rev_list nb_pts_to_skip xy₁ xyl₁ :=
  let (x₁, y₁) := (xy₁ : Q * Q) in
  match xyl₁ with
  | [(x₂, y₂) … xyl₂] =>
      match nb_pts_to_skip with
      | 0%nat =>
          let slt_min :=
            let sl₁₂ := (y₂ - y₁) / (x₂ - x₁) in
            let slt_min :=
              {| xy₂ := (x₂, y₂); slope := sl₁₂; skip := 0%nat |}
            in
            minimise_slope xy₁ slt_min 1%nat xyl₂
          in
          next_points [xy₂ slt_min … rev_list] (skip slt_min) (xy₂ slt_min)
            xyl₂
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
