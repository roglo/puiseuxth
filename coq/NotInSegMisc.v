(* NotInSegMisc.v *)

From Stdlib Require Import Utf8 Arith Sorting.

Require Import A_QArith.
Require Import Misc.
Require Import Slope_base.
Require Import ConvexHull.
Require Import ConvexHullMisc.

Theorem ad_hoc_lt_lt : ∀ i j k x y z,
  i < j ∧ i < k
  → (y - x) / (k - i) < (z - x) / (j - i)
    → x + i * ((x - y) / (k - i)) < z + j * ((x - y) / (k - i)).
Proof.
intros i j k x y z (Hij, Hjk) H.
apply Qlt_shift_mult_r in H; [ idtac | apply Q.lt_0_sub; assumption ].
rewrite Q.mul_comm, Q.mul_div_assoc in H.
apply Qlt_shift_mult_l in H; [ idtac | apply Q.lt_0_sub; assumption ].
rewrite Q.mul_comm in H.
do 2 rewrite Q.mul_sub_distr_r in H.
do 4 rewrite Q.mul_sub_distr_l in H.
do 2 rewrite Q.sub_sub_distr in H.
rewrite <- Q.add_sub_swap in H.
apply -> Q.lt_sub_lt_add_r in H.
rewrite <- Q.add_sub_swap in H.
apply -> Q.lt_sub_lt_add_r in H.
do 2 rewrite <- Q.add_assoc in H.
rewrite <- Q.add_sub_swap in H.
apply Q.lt_add_lt_sub_r in H.
rewrite <- Q.add_sub_swap in H.
apply Q.lt_add_lt_sub_r in H.
do 2 rewrite Q.add_assoc in H.
do 2 rewrite Q.mul_div_assoc.
rewrite Qplus_div; [ idtac | apply Qlt_not_0; assumption ].
rewrite Qplus_div; [ idtac | apply Qlt_not_0; assumption ].
apply Qdiv_lt_compat_r; [ apply Q.lt_0_sub; assumption | idtac ].
rewrite Q.mul_sub_distr_l.
rewrite Q.add_comm, Q.mul_comm; apply Q.nle_gt.
rewrite Q.add_comm, Q.mul_comm; apply Q.nle_gt.
do 2 rewrite Q.mul_sub_distr_r.
rewrite Q.mul_sub_distr_l.
do 2 rewrite Q.add_sub_assoc.
apply Q.lt_sub_lt_add_r; rewrite <- Q.add_sub_swap.
apply Q.lt_sub_lt_add_r; rewrite Q.add_sub_swap.
do 2 rewrite <- Q.add_assoc; rewrite <- Q.add_sub_swap.
apply -> Q.lt_add_lt_sub_r; rewrite <- Q.add_sub_swap.
apply -> Q.lt_add_lt_sub_r; do 2 rewrite Q.add_assoc.
rewrite Q.add_comm; do 2 rewrite Q.add_assoc.
rewrite (Q.add_comm (x * j)).
rewrite (Q.add_add_swap (z * k)).
easy.
Qed.

Theorem minimised_slope_le : ∀ pt₁ pt₂ pts ms,
  minimise_slope pt₁ pt₂ pts = ms
  → slope ms <= slope_expr pt₁ pt₂.
Proof.
intros pt₁ pt₂ pts ms Hms.
revert ms Hms.
induction pts as [| pt]; intros. {
  simpl in Hms.
  subst ms; simpl.
  apply Q.le_refl.
}
simpl in Hms.
remember (minimise_slope pt₁ pt pts) as ms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
destruct c; subst ms; [ | easy | ]. {
  simpl.
  symmetry in Heqc; apply -> Q.compare_eq_iff in Heqc.
  rewrite Heqc.
  progress unfold slope at 1; simpl.
  erewrite slope_slope_expr; [ easy | symmetry; eassumption ].
} {
  symmetry in Heqc; apply -> Q.compare_gt_iff in Heqc.
  apply Q.lt_le_incl; eassumption.
}
Qed.

Theorem minimise_slope_pts_le : ∀ j αj pt pts ms,
  minimise_slope (j, αj) pt pts = ms
  → ∀ h αh, (h, αh) ∈ pts
  → slope ms <= slope_expr (j, αj) (h, αh).
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
    erewrite <- minimised_slope; [ idtac | eassumption | reflexivity ].
    eapply minimised_slope_le; eassumption.
  } {
    simpl.
    eapply minimised_slope_le in Heqms₁.
    symmetry in Heqc; apply -> Q.compare_lt_iff in Heqc.
    apply Q.lt_le_incl.
    eapply Q.lt_le_trans; eassumption.
  } {
    eapply minimised_slope_le in Heqms₁.
    assumption.
  }
}
simpl in Hms.
remember (minimise_slope (j, αj) pt₁ pts) as ms₁.
symmetry in Heqms₁.
remember (slope_expr (j, αj) pt ?= slope ms₁) as c.
symmetry in Heqc.
destruct c; subst ms. {
  progress unfold slope; simpl.
  erewrite <- minimised_slope; [ idtac | eassumption | reflexivity ].
  eapply IHpts; eassumption.
} {
  simpl.
  apply -> Q.compare_lt_iff in Heqc.
  apply Q.lt_le_incl.
  eapply Q.lt_le_trans; [ eassumption | idtac ].
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
  → (k < h)%nat
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
      apply <- Nat.nlt_ge in Heqms₁; contradiction.
    } {
      simpl in Hep |- *; clear Hep.
      symmetry in Heqc; apply -> Q.compare_lt_iff in Heqc.
      eapply Q.lt_le_trans; [ eassumption | idtac ].
      eapply minimised_slope_le; eassumption.
    } {
      symmetry in Heqc; apply -> Q.compare_gt_iff in Heqc.
      apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
      rewrite Hep in Heqms₁; simpl in Heqms₁.
      apply Nat.nlt_ge in Heqms₁.
      contradiction.
    }
  }
  destruct Hms as [Hms| Hms]. {
    injection Hms; clear Hms; intros; subst h αh.
    apply Nat.lt_irrefl in Hkh; contradiction.
  }
  eapply Sorted_hd in Hsort; [ idtac | eassumption ].
  simpl in Hsort.
  eapply Nat.lt_trans in Hsort; [ idtac | eassumption ].
  apply Nat.lt_irrefl in Hsort; contradiction.
}
simpl in Hms.
remember (minimise_slope (j, αj) pt₁ pts) as ms₁.
symmetry in Heqms₁.
remember (slope_expr (j, αj) pt ?= slope ms₁) as c.
destruct c; subst ms. {
  simpl in Hep |- *.
  progress unfold slope; simpl.
  erewrite <- minimised_slope; [ idtac | eassumption | reflexivity ].
  eapply IHpts; try eassumption.
  destruct pts as [| pts₁]; [ constructor | idtac ].
  apply Sorted_inv_2 in Hsort; destruct Hsort; assumption.
} {
  simpl in Hep |- *.
  subst pt.
  symmetry in Heqc; apply -> Q.compare_lt_iff in Heqc.
  eapply Q.lt_le_trans; [ eassumption | idtac ].
  eapply minimise_slope_pts_le; eassumption.
} {
  eapply IHpts; try eassumption.
  destruct pts as [| pts₁]; [ constructor | idtac ].
  apply Sorted_inv_2 in Hsort; destruct Hsort; assumption.
}
Qed.

Theorem points_after_k : ∀ pts j αj k αk seg γ β,
  Sorted fst_lt pts
  → (j < k)%nat
  → γ = (αj - αk) / (Qnat k - Qnat j)
  → β = αj + Qnat j * γ
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) seg)
  → ∀ h αh, (k < h)%nat
  → (h, αh) ∈ pts
  → β < αh + Qnat h * γ.
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
  eapply Nat.lt_trans in Hkh; [ idtac | eassumption ].
  apply Nat.lt_irrefl in Hkh; contradiction.
}
destruct Hαh as [Hαh| Hαh]; [ exfalso | idtac ]. {
  subst pt₂.
  symmetry in Heqms₁.
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt₁, Hsort).
  apply minimise_slope_le in Heqms₁; [ idtac | assumption ].
  rewrite Hep₁ in Heqms₁.
  apply Nat.nlt_ge in Heqms₁.
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
    apply Qnat_lt in Hjk, Hkh.
    split; [ idtac | assumption ].
    now transitivity (Qnat k).
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
  → (j < h < k)%nat
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
    apply Nat.lt_irrefl in Hhk; contradiction.
  } {
    simpl in Hseg, Hep.
    subst pt.
    apply -> Q.compare_lt_iff in Heqc.
    assumption.
  } {
    simpl in Hseg, Hep.
    injection Hep; clear Hep; intros; subst h αh.
    apply Nat.lt_irrefl in Hhk; contradiction.
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
    apply Nat.lt_irrefl in Hhk; contradiction.
  } {
    apply -> Q.compare_gt_iff in Heqc.
    erewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
    assumption.
  }
} {
  simpl in Hseg, Hep.
  subst pt.
  apply -> Q.compare_lt_iff in Heqc₁.
  eapply Q.lt_le_trans; [ eassumption | idtac ].
  eapply minimised_slope_le; eassumption.
} {
  subst pts₁.
  apply -> Q.compare_gt_iff in Heqc₁.
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
    apply Nat.lt_irrefl in Hhk; contradiction.
  } {
    apply -> Q.compare_gt_iff in Heqc.
    erewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
    assumption.
  }
}
Qed.

Theorem points_between_j_and_k : ∀ pts j αj k αk oth γ β,
  Sorted fst_lt pts
  → γ = (αj - αk) / (Qnat k - Qnat j)
  → β = αj + Qnat j * γ
  → lower_convex_hull_points pts = Some (mkns (j, αj) (k, αk) oth)
  → ∀ h αh, (j < h < k)%nat
  → (h, αh) ∈ pts
  → (h, αh) ∉ oth
  → β < αh + Qnat h * γ.
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
  apply Nat.lt_irrefl in Hjh; contradiction.
}
destruct Hαh as [Hαh| Hαh]. {
  subst pt₁.
  symmetry in Heqms₁.
  destruct pts as [| pt₁]. {
    simpl in Heqms₁.
    subst ms₁.
    simpl in Hep₁, Hseg, Hbp₁.
    injection Hep₁; clear Hep₁; intros; subst h αh.
    apply Nat.lt_irrefl in Hhk; contradiction.
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
    apply Nat.lt_irrefl in Hhk; contradiction.
  } {
    symmetry in Hep₁.
    remember Heqms₂ as H; clear HeqH.
    eapply minimised_slope in H; [ idtac | eassumption ].
    symmetry in Heqc; apply -> Q.compare_gt_iff in Heqc.
    rewrite H in Heqc.
    subst β γ.
    apply ad_hoc_lt_lt. {
      apply Qnat_lt in Hjh, Hhk.
      split; [ assumption | idtac ].
      now transitivity (Qnat h).
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
      apply Qnat_lt in Hjh, Hhk.
      split; [ assumption | idtac ].
      now transitivity (Qnat h).
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
    intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
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
  eapply Nat.lt_trans in Hlt₃; [ idtac | eassumption ].
  eapply Nat.lt_trans in Hlt₃; [ idtac | eassumption ].
  apply Nat.lt_irrefl in Hlt₃; contradiction.
} {
  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
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
    apply Nat.lt_irrefl in Hlt; contradiction.
  }
  apply IHpts; [ idtac | assumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
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
    apply Nat.lt_irrefl in Hlt; contradiction.
  }
  apply IHpts; [ idtac | assumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
}
apply Sorted_inv_1 in Hsort.
apply IHpts; assumption.
Qed.
