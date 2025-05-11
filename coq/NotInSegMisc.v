(* NotInSegMisc.v *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Sorting.
From Stdlib Require Import QArith.

Require Import QGArith.
Require Import Misc.
Require Import Slope_base.
Require Import ConvexHull.
Require Import ConvexHullMisc.

Theorem QG_lt_shift_mul_l : ∀ x y z, 0 < z → x / z < y → x < y * z.
Proof.
intros x y z Hc H.
apply QG_compare_lt_iff in H.
apply QG_compare_lt_iff.
now rewrite <- H; symmetry; apply QG_cmp_shift_mul_l.
Qed.

Theorem QG_lt_shift_mul_r : ∀ x y z, 0 < z → x < y / z → x * z < y.
Proof.
intros x y z Hc H.
apply QG_compare_lt_iff in H.
apply QG_compare_lt_iff.
now rewrite <- H; symmetry; apply QG_cmp_shift_mul_r.
Qed.

Theorem QG_add_lt_mono_r : ∀ a b c, a < b ↔ a + c < b + c.
Proof.
intros.
destruct a as ((an, ad), Ha).
destruct b as ((bn, bd), Hb).
move bn before an.
move bd before ad.
cbn in Ha, Hb.
split; intros Hab. {
  apply qlt_QG_lt in Hab.
  apply qlt_QG_lt.
  cbn - [ Qred ] in Hab |-*.
  apply Z_pos_gcd_eq_1 in Ha, Hb.
  apply Qred_lt.
  now apply Qplus_lt_compat_r.
} {
  apply qlt_QG_lt in Hab.
  apply qlt_QG_lt.
  cbn - [ Qred ] in Hab |-*.
  apply Z_pos_gcd_eq_1 in Ha, Hb.
  apply -> Qred_lt in Hab.
  now apply Qplus_lt_l in Hab.
}
Qed.

Theorem QG_div_add_distr_r : ∀ a b c, (a + b) / c = a / c + b / c.
Proof.
intros.
apply eq_QG_eq.
cbn - [ Qred ].
rewrite Qred_mul_idemp_l.
do 3 rewrite Qred_mul_idemp_r.
rewrite Qred_add_idemp_l.
rewrite Qred_add_idemp_r.
apply Qred_complete.
apply Qmult_plus_distr_l.
Qed.

Theorem QG_add_div : ∀ a b c, c ≠ 0 → a + b / c = (a * c + b) / c.
Proof.
intros.
rewrite QG_div_add_distr_r.
now rewrite QG_mul_div.
Qed.

Theorem QG_mul_0_l : ∀ a, 0 * a = 0.
Proof. now intros; now apply eq_QG_eq. Qed.

Theorem QG_0_lt_inv_compat : ∀ a, 0 < a → 0 < a⁻¹.
Proof.
intros * Hza.
apply (QG_mul_lt_mono_pos_r _ _ Hza).
rewrite QG_mul_inv_diag_l. 2: {
  now intros H; subst a; apply QG_lt_irrefl in Hza.
}
now rewrite QG_mul_0_l.
Qed.

Theorem QG_div_lt_mono_pos_r : ∀ a b c, 0 < a → b < c ↔ b / a < c / a.
Proof.
intros * Hza.
progress unfold QG_div.
apply QG_mul_lt_mono_pos_r.
now apply QG_0_lt_inv_compat.
Qed.

Theorem ad_hoc_lt_lt : ∀ i j k x y z,
  i < j ∧ i < k
  → (y - x) / (k - i) < (z - x) / (j - i)
    → x + i * ((x - y) / (k - i)) < z + j * ((x - y) / (k - i)).
Proof.
intros i j k x y z (Hij, Hjk) H.
apply QG_lt_shift_mul_r in H; [ | now apply QG_lt_0_sub ].
rewrite QG_mul_comm, QG_mul_div_assoc in H.
apply QG_lt_shift_mul_l in H; [ | now apply QG_lt_0_sub ].
rewrite QG_mul_comm in H.
do 2 rewrite QG_mul_sub_distr_l in H.
do 4 rewrite QG_mul_sub_distr_r in H.
do 2 rewrite QG_sub_sub_distr in H.
apply QG_add_lt_mono_r in H.
do 2 apply -> QG_lt_sub_lt_add_r in H.
do 2 rewrite <- QG_add_sub_swap in H.
apply QG_lt_add_lt_sub_r in H.
do 2 rewrite <- QG_add_sub_swap in H.
apply QG_lt_add_lt_sub_r in H.
do 2 rewrite QG_mul_div_assoc.
rewrite QG_add_div. 2: {
  intros H1.
  apply -> QG_sub_move_0_r in H1.
  subst k.
  now apply QG_lt_irrefl in Hjk.
}
rewrite QG_add_div. 2: {
  intros H1.
  apply -> QG_sub_move_0_r in H1.
  subst k.
  now apply QG_lt_irrefl in Hjk.
}
apply QG_div_lt_mono_pos_r; [ now apply QG_lt_0_sub | ].
do 4 rewrite QG_mul_sub_distr_l.
do 2 rewrite QG_add_sub_assoc.
rewrite (QG_mul_comm x i).
rewrite QG_sub_add.
apply QG_lt_sub_lt_add_r.
rewrite <- QG_add_sub_swap.
apply QG_lt_add_lt_sub_r.
do 2 rewrite <- QG_add_sub_swap.
apply -> QG_lt_add_lt_sub_r.
rewrite <- QG_add_assoc, QG_add_comm.
rewrite (QG_mul_comm j y).
rewrite <- (QG_add_assoc (z * k)).
rewrite (QG_add_comm (j * x)).
rewrite QG_add_assoc.
rewrite (QG_mul_comm i y).
rewrite (QG_mul_comm j x).
easy.
Qed.

Theorem minimised_slope_le : ∀ pt₁ pt₂ pts ms,
  minimise_slope pt₁ pt₂ pts = ms
  → slope ms ≤ slope_expr pt₁ pt₂.
Proof.
intros pt₁ pt₂ pts ms Hms.
revert ms Hms.
induction pts as [| pt]; intros. {
  simpl in Hms.
  subst ms; simpl.
  apply QG_le_refl.
}
simpl in Hms.
remember (minimise_slope pt₁ pt pts) as ms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
destruct c; subst ms. {
  symmetry in Heqc; apply QG_compare_eq_iff in Heqc.
  rewrite Heqc.
  progress unfold slope at 1; simpl.
  rewrite (slope_slope_expr _ pt₁ pt pts); [ | easy ].
  apply QG_le_refl.
} {
  simpl.
  apply QG_le_refl.
} {
  symmetry in Heqc; apply QG_compare_gt_iff in Heqc.
  now apply QG_lt_le_incl.
}
Qed.

Theorem minimise_slope_pts_le : ∀ j αj pt pts ms,
  minimise_slope (j, αj) pt pts = ms
  → ∀ h αh, (h, αh) ∈ pts
  → slope ms ≤ slope_expr (j, αj) (h, αh).
Proof.
intros j αj pt pts ms Hms h αh Hαh.
revert pt ms Hms h αh Hαh.
induction pts as [| pt₁]; [ contradiction | intros ].
destruct Hαh as [Hαh| Hαh]. {
  subst pt₁.
  simpl in Hms.
  remember (minimise_slope (j, αj) (h, αh) pts) as ms₁.
  symmetry in Heqms₁.
  remember (slope_expr (j, αj) pt ?= slope ms₁) as c.
  destruct c; subst ms. {
    progress unfold slope; simpl.
    rewrite <- (minimised_slope _ _ (h, αh) pts ms₁); [ | easy | easy ].
    eapply minimised_slope_le.
    apply Heqms₁.
  } {
    simpl.
    eapply minimised_slope_le in Heqms₁.
    symmetry in Heqc; apply Qlt_alt in Heqc.
    apply QG_lt_le_incl.
    eapply QG_lt_le_trans; [ | apply Heqms₁ ].
    now apply qlt_QG_lt.
  } {
    now eapply minimised_slope_le in Heqms₁.
  }
}
simpl in Hms.
remember (minimise_slope (j, αj) pt₁ pts) as ms₁.
symmetry in Heqms₁.
remember (slope_expr (j, αj) pt ?= slope ms₁) as c.
symmetry in Heqc.
destruct c; subst ms. {
  progress unfold slope; simpl.
  erewrite <- minimised_slope; [ | apply Heqms₁ | easy ].
  eapply IHpts; [ eassumption | easy ].
} {
  simpl.
  apply QG_compare_lt_iff in Heqc.
  apply QG_lt_le_incl.
  eapply QG_lt_le_trans; [ eassumption | ].
  eapply IHpts; eassumption.
} {
  eapply IHpts; eassumption.
}
Qed.

Theorem min_slope_lt_after_k : ∀ j αj k αk pt pts ms,
  Sorted fst_lt pts
  → minimise_slope (j, αj) pt pts = ms
  → fin_pt ms = (k, αk)
  → ∀ h αh, (h, αh) ∈ pts
  → k < h
  → slope ms < slope_expr (j, αj) (h, αh).
Proof.
intros j αj k αk pt pts ms Hsort Hms Hep h αh Hαh Hkh.
revert pt ms Hms Hep h Hαh Hkh.
induction pts as [| pt₁]; [ contradiction | intros ].
destruct Hαh as [Hαh| Hαh]. {
  subst pt₁.
  remember Hms as H; clear HeqH.
  apply end_pt_in in Hms.
  rewrite Hep in Hms.
  destruct Hms as [Hms| Hms]. {
    subst pt.
    simpl in H.
    remember (minimise_slope (j, αj) (h, αh) pts) as ms₁.
    symmetry in Heqms₁.
    remember (slope_expr (j, αj) (k, αk) ?= slope ms₁) as c.
    destruct c; subst ms. {
      simpl in Hep |- *.
      apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
      rewrite Hep in Heqms₁.
      now apply QG_nlt_ge in Heqms₁.
    } {
      simpl in Hep |- *; clear Hep.
      symmetry in Heqc; apply QG_compare_lt_iff in Heqc.
      eapply QG_lt_le_trans; [ eassumption | ].
      eapply minimised_slope_le; eassumption.
    } {
      symmetry in Heqc; apply QG_compare_gt_iff in Heqc.
      apply minimise_slope_le in Heqms₁; [ | easy ].
      rewrite Hep in Heqms₁; simpl in Heqms₁.
      now apply QG_nlt_ge in Heqms₁.
    }
  }
  destruct Hms as [Hms| Hms]. {
    injection Hms; clear Hms; intros; subst h αh.
    apply QG_lt_irrefl in Hkh; contradiction.
  }
  eapply Sorted_hd in Hsort; [ idtac | eassumption ].
  simpl in Hsort.
  eapply QG_lt_trans in Hsort; [ idtac | eassumption ].
  apply QG_lt_irrefl in Hsort; contradiction.
}
simpl in Hms.
remember (minimise_slope (j, αj) pt₁ pts) as ms₁.
symmetry in Heqms₁.
remember (slope_expr (j, αj) pt ?= slope ms₁) as c.
destruct c; subst ms. {
  simpl in Hep |- *.
  progress unfold slope; simpl.
  erewrite <- minimised_slope; [ | eassumption | easy ].
  eapply IHpts; try eassumption.
  destruct pts as [| pts₁]; [ constructor | idtac ].
  apply Sorted_inv_2 in Hsort; destruct Hsort; assumption.
} {
  simpl in Hep |- *.
  subst pt.
  symmetry in Heqc; apply QG_compare_lt_iff in Heqc.
  eapply QG_lt_le_trans; [ eassumption | idtac ].
  eapply minimise_slope_pts_le; eassumption.
} {
  eapply IHpts; try eassumption.
  destruct pts as [| pts₁]; [ constructor | idtac ].
  apply Sorted_inv_2 in Hsort; destruct Hsort; assumption.
}
Qed.

Theorem points_after_k : ∀ pts j αj k αk seg γ β,
  Sorted fst_lt pts
  → j < k
  → γ = (αj - αk) / (k - j)
  → β = αj + j * γ
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) seg)
  → ∀ h αh, k < h
  → (h, αh) ∈ pts
  → β < αh + h * γ.
Proof.
intros pts j αj k αk seg γ β.
intros Hsort Hjk Hγ Hβ Hnp h αh Hkh Hαh.
destruct pts as [| pt₁]; [ easy | ].
destruct pts as [| pt₂]; [ easy | ].
simpl in Hnp.
rewrite minimised_slope_beg_pt in Hnp.
injection Hnp; clear Hnp; intros Hseg Hep₁ Hp₁; subst seg pt₁.
remember (minimise_slope (j, αj) pt₂ pts) as ms₁.
destruct Hαh as [Hαh| Hαh]. {
  injection Hαh; clear Hαh; intros; subst h αh.
  eapply QG_lt_trans in Hkh; [ | eassumption ].
  apply QG_lt_irrefl in Hkh; contradiction.
}
destruct Hαh as [Hαh| Hαh]; [ exfalso | idtac ]. {
  subst pt₂.
  symmetry in Heqms₁.
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
  rewrite Hep₁ in Heqms₁.
  apply QG_nlt_ge in Heqms₁.
  contradiction.
}
symmetry in Heqms₁.
symmetry in Hep₁.
remember Heqms₁ as H; clear HeqH.
eapply minimised_slope in H; [ idtac | eassumption ].
symmetry in Hep₁.
eapply min_slope_lt_after_k in Heqms₁; try eassumption. {
  rewrite H in Heqms₁.
  subst β γ.
  apply ad_hoc_lt_lt. {
    split; [ idtac | assumption ].
    eapply QG_lt_trans; eassumption.
  }
  progress unfold slope_expr in Heqms₁; simpl in Heqms₁.
  assumption.
}
apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, Hsort).
apply Sorted_inv_1 in Hsort; assumption.
Qed.

Theorem not_seg_min_sl_lt : ∀ j αj k αk pt pts ms h αh,
  Sorted fst_lt [(j, αj); pt; (h, αh) … pts]
  → minimise_slope (j, αj) pt [(h, αh) … pts] = ms
  → j < h < k
  → (h, αh) ∉ oth_pts ms
  → fin_pt ms = (k, αk)
  → slope ms < slope_expr (j, αj) (h, αh).
Proof.
intros j αj k αk pt pts ms h αh Hsort Hms (Hjh, Hhk) Hseg Hep.
erewrite slope_slope_expr; [ idtac | eassumption ].
revert ms Hms Hseg Hep.
induction pts as [| pt₁]; intros. {
  simpl in Hms.
  progress unfold slope in Hms; simpl in Hms.
  remember (slope_expr (j, αj) pt ?= slope_expr (j, αj) (h, αh)) as c.
  symmetry in Heqc.
  destruct c; subst ms; simpl. {
    simpl in Hseg, Hep.
    injection Hep; clear Hep; intros; subst h αh.
    apply QG_lt_irrefl in Hhk; contradiction.
  } {
    simpl in Hseg, Hep.
    subst pt.
    apply QG_compare_lt_iff in Heqc.
    assumption.
  } {
    simpl in Hseg, Hep.
    injection Hep; clear Hep; intros; subst h αh.
    apply QG_lt_irrefl in Hhk; contradiction.
  }
}
remember [pt₁ … pts] as pts₁.
simpl in Hms.
remember (minimise_slope (j, αj) (h, αh) pts₁) as ms₁.
symmetry in Heqms₁.
remember (slope_expr (j, αj) pt ?= slope ms₁) as c₁.
symmetry in Heqc₁.
destruct c₁; subst ms; simpl. {
  simpl in Hseg, Hep.
  apply Decidable.not_or in Hseg.
  destruct Hseg as (Hne, Hseg).
  subst pts₁.
  simpl in Heqms₁.
  remember (minimise_slope (j, αj) pt₁ pts) as ms₂.
  symmetry in Heqms₂.
  remember (slope_expr (j, αj) (h, αh) ?= slope ms₂) as c.
  symmetry in Heqc.
  destruct c; subst ms₁; simpl. {
    simpl in Heqc₁, Hseg, Hep.
    apply Decidable.not_or in Hseg.
    destruct Hseg as (Hne₂, Hseg).
    negation Hne₂.
  } {
    simpl in Heqc₁, Hseg, Hep.
    injection Hep; clear Hep; intros; subst h αh.
    apply QG_lt_irrefl in Hhk; contradiction.
  } {
    apply QG_compare_gt_iff in Heqc.
    erewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
    assumption.
  }
} {
  simpl in Hseg, Hep.
  subst pt.
  apply QG_compare_lt_iff in Heqc₁.
  eapply QG_lt_le_trans; [ eassumption | idtac ].
  eapply minimised_slope_le; eassumption.
} {
  subst pts₁.
  apply Qgt_alt in Heqc₁.
  simpl in Heqms₁.
  remember (minimise_slope (j, αj) pt₁ pts) as ms₂.
  symmetry in Heqms₂.
  remember (slope_expr (j, αj) (h, αh) ?= slope ms₂) as c.
  symmetry in Heqc.
  destruct c; subst ms₁; simpl. {
    simpl in Heqc₁, Hseg, Hep.
    apply Decidable.not_or in Hseg.
    destruct Hseg as (Hne₂, Hseg).
    negation Hne₂.
  } {
    simpl in Heqc₁, Hseg, Hep.
    injection Hep; clear Hep; intros; subst h αh.
    apply QG_lt_irrefl in Hhk; contradiction.
  } {
    apply QG_compare_gt_iff in Heqc.
    erewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
    assumption.
  }
}
Qed.

Theorem points_between_j_and_k : ∀ pts j αj k αk oth γ β,
  Sorted fst_lt pts
  → γ = (αj - αk) / (k - j)
  → β = αj + j * γ
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) oth)
  → ∀ h αh, j < h < k
  → (h, αh) ∈ pts
  → (h, αh) ∉ oth
  → β < αh + h * γ.
Proof.
intros pts j αj k αk oth γ β.
intros Hsort Hγ Hβ Hnp h αh (Hjh, Hhk) Hαh Hseg.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember Hnp as H; clear HeqH.
apply next_ch_points_hd in H.
subst pt₁; simpl in Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
remember (minimise_slope (j, αj) pt₁ pts) as ms₁.
injection Hnp; clear Hnp; intros Hop₁ Hep₁ Hbp₁; subst oth.
destruct Hαh as [Hαh| Hαh]. {
  injection Hαh; clear Hαh; intros; subst h αh.
  apply QG_lt_irrefl in Hjh; contradiction.
}
destruct Hαh as [Hαh| Hαh]. {
  subst pt₁.
  symmetry in Heqms₁.
  destruct pts as [| pt₁]. {
    simpl in Heqms₁.
    subst ms₁.
    simpl in Hep₁, Hseg, Hbp₁.
    injection Hep₁; clear Hep₁; intros; subst h αh.
    apply QG_lt_irrefl in Hhk; contradiction.
  }
  simpl in Heqms₁.
  remember (minimise_slope (j, αj) pt₁ pts) as ms₂.
  symmetry in Heqms₂.
  remember (slope_expr (j, αj) (h, αh) ?= slope ms₂) as c.
  destruct c; subst ms₁. {
    simpl in Hep₁, Hseg, Hbp₁.
    apply Decidable.not_or in Hseg.
    destruct Hseg as (H, _); negation H.
  } {
    simpl in Hep₁, Hseg, Hbp₁.
    injection Hep₁; clear Hep₁; intros; subst h αh.
    apply QG_lt_irrefl in Hhk; contradiction.
  } {
    symmetry in Hep₁.
    remember Heqms₂ as H; clear HeqH.
    eapply minimised_slope in H; [ idtac | eassumption ].
    symmetry in Heqc; apply QG_compare_gt_iff in Heqc.
    rewrite H in Heqc.
    subst β γ.
    apply ad_hoc_lt_lt. {
      split; [ assumption | idtac ].
      eapply QG_lt_trans; eassumption.
    } {
      progress unfold slope_expr in Heqc; simpl in Heqc.
      assumption.
    }
  }
}
symmetry in Heqms₁.
revert pt₁ ms₁ Hsort Heqms₁ Hep₁ Hseg Hbp₁.
induction pts as [| pt₂]; intros. {
  simpl in Heqms₁.
  subst ms₁.
  simpl in Hep₁, Hseg, Hbp₁.
  contradiction.
}
destruct Hαh as [Hαh| Hαh]. {
  subst pt₂.
  symmetry in Hep₁.
  remember Heqms₁ as H; clear HeqH.
  eapply minimised_slope in H; [ idtac | eassumption ].
  symmetry in Hep₁.
  eapply not_seg_min_sl_lt in Heqms₁; try eassumption. {
    rewrite H in Heqms₁.
    subst β γ.
    apply ad_hoc_lt_lt. {
      split; [ assumption | idtac ].
      eapply QG_lt_trans; eassumption.
    }
    progress unfold slope_expr in Heqms₁; simpl in Heqms₁.
    assumption.
  }
  split; assumption.
}
simpl in Heqms₁.
remember (minimise_slope (j, αj) pt₂ pts) as ms₂.
symmetry in Heqms₂.
remember (slope_expr (j, αj) pt₁ ?= slope ms₂) as c.
symmetry in Heqc.
destruct c; subst ms₁. {
  simpl in Hep₁, Hseg, Hbp₁.
  apply Decidable.not_or in Hseg.
  destruct Hseg as (Hlt₁, Hseg).
  eapply IHpts; try eassumption. {
    eapply Sorted_minus_2nd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply QG_lt_trans; eassumption.
  }
  rewrite <- Heqms₂, minimised_slope_beg_pt; reflexivity.
} {
  simpl in Hep₁, Hseg, Hbp₁.
  subst pt₁.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort as (Hlt₂, Hsort).
  apply Sorted_inv_2 in Hsort.
  destruct Hsort as (Hlt₃, Hsort).
  eapply Sorted_hd in Hsort; [ idtac | eassumption ].
  progress unfold fst_lt in Hlt₃.
  simpl in Hlt₃, Hsort.
  clear Hlt₂.
  eapply QG_lt_trans in Hlt₃; [ idtac | eassumption ].
  eapply QG_lt_trans in Hlt₃; [ idtac | eassumption ].
  apply QG_lt_irrefl in Hlt₃; contradiction.
} {
  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply QG_lt_trans; eassumption.
}
Qed.

Theorem in_ch_in_pts : ∀ pts pt₁ pt₂ s,
  lower_convex_hull_points pts = Some (mkns pt₁ pt₂ s)
  → pt₁ ∈ pts ∧ pt₂ ∈ pts.
Proof.
intros pts pt₁ pt₂ s Hhs.
progress unfold lower_convex_hull_points in Hhs.
destruct pts as [| pt₃]; [ discriminate Hhs | idtac ].
destruct pts as [| pt₄]; [ discriminate Hhs | idtac ].
injection Hhs; clear Hhs; intros; subst pt₁ pt₂ s.
split; [ now rewrite minimised_slope_beg_pt; left | ].
remember (minimise_slope pt₃ pt₄ pts) as ms₁.
symmetry in Heqms₁.
apply end_pt_in in Heqms₁.
right; assumption.
Qed.

(* it was j == k before; perhaps the interface of this
   theorem could be simplified since we can use j = k now *)
Theorem sorted_qeq_eq : ∀ pts j αj k αk,
  Sorted fst_lt pts
  → (j, αj) ∈ pts
  → (k, αk) ∈ pts
  → j = k
  → (j, αj) = (k, αk).
Proof.
intros pts j αj k αk Hsort Hj Hk Hjk.
induction pts as [| (l, αl)]; [ contradiction | idtac ].
destruct Hj as [Hj| Hj]. {
  destruct Hk as [Hk| Hk]. {
    rewrite Hj in Hk; assumption.
  }
  injection Hj; clear Hj; intros; subst l αl.
  clear IHpts.
  exfalso.
  induction pts as [| (l, αl)]; [ contradiction | idtac ].
  destruct Hk as [Hk| Hk]. {
    injection Hk; clear Hk; intros; subst l αl.
    apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
    progress unfold fst_lt in Hlt; simpl in Hlt; rewrite Hjk in Hlt.
    apply QG_lt_irrefl in Hlt; contradiction.
  }
  apply IHpts; [ idtac | assumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply QG_lt_trans; eassumption.
}
destruct Hk as [Hk| Hk]. {
  injection Hk; clear Hk; intros; subst l αl.
  clear IHpts.
  exfalso.
  induction pts as [| (l, αl)]; [ contradiction | idtac ].
  destruct Hj as [Hj| Hj]. {
    injection Hj; clear Hj; intros; subst l αl.
    apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
    progress unfold fst_lt in Hlt; simpl in Hlt; rewrite Hjk in Hlt.
    apply QG_lt_irrefl in Hlt; contradiction.
  }
  apply IHpts; [ idtac | assumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply QG_lt_trans; eassumption.
}
apply Sorted_inv_1 in Hsort.
apply IHpts; assumption.
Qed.

(*
Theorem qeq_eq_ini : ∀ pts h αh j αj ptj s,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some (mkns (j, αj) ptj s)
  → (h, αh) ∈ pts
  → h == j
  → h = j.
Proof.
intros pts h αh j αj ptj s Hpts Hhsl Hαh Hhk.
eapply sorted_qeq_eq with (αk := αj) in Hhk; try eassumption. {
  injection Hhk; intros; subst; reflexivity.
}
now apply in_ch_in_pts with (s := s) (pt₂ := ptj).
Qed.

Theorem qeq_eq_fin : ∀ pts h αh k αk ptk s,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some (mkns ptk (k, αk) s)
  → (h, αh) ∈ pts
  → h == k
  → h = k.
Proof.
intros pts h αh k αk ptk s Hpts Hhsl Hαh Hhk.
eapply sorted_qeq_eq with (αk := αk) in Hhk; try eassumption. {
  injection Hhk; intros; subst; reflexivity.
}
now apply in_ch_in_pts with (s := s) (pt₁ := ptk).
Qed.
*)
