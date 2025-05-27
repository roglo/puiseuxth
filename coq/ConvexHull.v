(* ConvexHull.v *)

From Stdlib Require Import Utf8 ZArith List.
Import ListNotations.

Require Import Slope_base.

Record newton_segment := mkns
  { ini_pt : (nat * Z);
    fin_pt : (nat * Z);
    oth_pts : list (nat * Z);
    pts_comm_den : positive }.

Definition slope ns := slope_expr (ini_pt ns) (fin_pt ns) (pts_comm_den ns).

Definition ZPcompare (zp1 zp2 : Z * positive) :=
  let (n1, d1) := zp1 in
  let (n2, d2) := zp2 in
  (n1 * Z.pos d2 ?= n2 * Z.pos d1)%Z.

Fixpoint minimise_slope pt₁ pt₂ pts₂ den :=
  match pts₂ with
  | [] =>
      {| ini_pt := pt₁; fin_pt := pt₂; oth_pts := []; pts_comm_den := den |}
  | pt₃ :: pts₃ =>
      let ns := minimise_slope pt₁ pt₃ pts₃ den in
      match ZPcompare (slope_expr pt₁ pt₂ den) (slope ns) with
      | Eq =>
          {| ini_pt := pt₁; fin_pt := fin_pt ns;
             oth_pts := pt₂ :: oth_pts ns;
             pts_comm_den := den |}
      | Lt =>
          {| ini_pt := pt₁; fin_pt := pt₂; oth_pts := [];
             pts_comm_den := den |}
      | Gt =>
          ns
      end
  end.

Definition lower_convex_hull_points pts den :=
  match pts with
  | [] => None
  | [pt₁] => None
  | pt₁ :: pt₂ :: pts₂ =>
      let ms := minimise_slope pt₁ pt₂ pts₂ den in
      Some
        {| ini_pt := ini_pt ms; fin_pt := fin_pt ms;
           oth_pts := oth_pts ms; pts_comm_den := den |}
  end.

...

Theorem minimised_slope_beg_pt : ∀ pt₁ pt₂ pts den,
  ini_pt (minimise_slope pt₁ pt₂ pts den) = pt₁.
Proof.
intros pt₁ pt₂ pts.
revert pt₁ pt₂.
induction pts as [| pt]; intros; [ reflexivity | simpl ].
remember (minimise_slope pt₁ pt pts den) as ms.
remember (slope_expr pt₁ pt₂ den ?= slope ms)%Z as c.
symmetry in Heqc.
destruct c; simpl; [ reflexivity | reflexivity | idtac ].
subst ms; apply IHpts.
Qed.

Theorem slope_slope_expr : ∀ ms pt₁ pt₂ pts,
  minimise_slope pt₁ pt₂ pts = ms
  → slope ms == slope_expr pt₁ (fin_pt ms).
Proof.
intros ms pt₁ pt₂ pts Hms.
unfold slope.
rewrite <- Hms at 1.
rewrite minimised_slope_beg_pt.
reflexivity.
Qed.
