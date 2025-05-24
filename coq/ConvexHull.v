(* ConvexHull.v *)

From Stdlib Require Import Utf8 ZArith List.
Import ListNotations.

Require Import QGArith.
Require Import Slope_base.
Open Scope QG.

Record newton_segment := mkns
  { ini_pt : (nat * QG);
    fin_pt : (nat * QG);
    oth_pts : list (nat * QG);
    pts_comm_den : positive }.

Definition slope ms := slope_expr (ini_pt ms) (fin_pt ms).

Definition Pos_lcm (a b : positive) : positive :=
  let na := Npos a in
  let nb := Npos b in
  match ((na * nb) / N.gcd na nb)%N with
  | N0 => 1%positive (* fallback; shouldn't happen since a,b > 0 *)
  | Npos p => p
  end.

Definition pt_comm_den (a b : nat * QG) :=
  Pos_lcm (QG_den (snd a)) (QG_den (snd b)).

Fixpoint minimise_slope pt₁ pt₂ pts₂ :=
  match pts₂ with
  | [] =>
      {| ini_pt := pt₁; fin_pt := pt₂; oth_pts := [];
         pts_comm_den := pt_comm_den pt₁ pt₂ |}
  | pt₃ :: pts₃ =>
      let ms := minimise_slope pt₁ pt₃ pts₃ in
      match QG_compare (slope_expr pt₁ pt₂) (slope ms) with
      | Eq =>
          {| ini_pt := pt₁; fin_pt := fin_pt ms;
             oth_pts := pt₂ :: oth_pts ms;
             pts_comm_den := pt_comm_den pt₁ pt₂ |}
      | Lt =>
          {| ini_pt := pt₁; fin_pt := pt₂; oth_pts := [];
             pts_comm_den := pt_comm_den pt₁ pt₂ |}
      | Gt =>
          ms
      end
  end.

Definition lower_convex_hull_points pts :=
  match pts with
  | [] => None
  | [pt₁] => None
  | pt₁ :: pt₂ :: pts₂ =>
      let ms := minimise_slope pt₁ pt₂ pts₂ in
      Some
        {| ini_pt := ini_pt ms; fin_pt := fin_pt ms; oth_pts := oth_pts ms;
           pts_comm_den := pts_comm_den ms |}
  end.

Theorem minimised_slope_beg_pt : ∀ pt₁ pt₂ pts,
  ini_pt (minimise_slope pt₁ pt₂ pts) = pt₁.
Proof.
intros pt₁ pt₂ pts.
revert pt₁ pt₂.
induction pts as [| pt]; intros; [ reflexivity | simpl ].
remember (minimise_slope pt₁ pt pts) as ms.
remember (slope_expr pt₁ pt₂ ?= slope ms) as c.
symmetry in Heqc.
destruct c; simpl; [ reflexivity | reflexivity | idtac ].
subst ms; apply IHpts.
Qed.

Theorem slope_slope_expr : ∀ ms pt₁ pt₂ pts,
  minimise_slope pt₁ pt₂ pts = ms
  → slope ms = slope_expr pt₁ (fin_pt ms).
Proof.
intros ms pt₁ pt₂ pts Hms.
unfold slope.
rewrite <- Hms at 1.
rewrite minimised_slope_beg_pt.
reflexivity.
Qed.
