(* ConvexHullMisc.v *)

From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Sorting.

Require Import Misc.
Require Import ConvexHull.
Require Import Slope_base.

Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).
Notation "x ++ y" := (List.app x y) (right associativity, at level 60).

Definition fst_lt (x y : nat * Q) := (fst x < fst y)%nat.

Theorem Sorted_app {A} : ∀ (f : A → A → Prop) l₁ l₂,
  Sorted f (l₁ ++ l₂) → Sorted f l₁ ∧ Sorted f l₂.
Proof.
intros f l₁ l₂ H.
split. {
  induction l₁ as [| x]; [ constructor | simpl in H ].
  destruct l₁ as [| y]; [ constructor; constructor | idtac ].
  constructor; [ eapply IHl₁, Sorted_inv_1; eassumption | idtac ].
  constructor; apply Sorted_inv_2 in H; destruct H; assumption.
}
induction l₁ as [| x]; [ assumption | apply IHl₁ ].
eapply Sorted_inv_1; eassumption.
Qed.

Theorem Sorted_app_at_r : ∀ α f l (x : α),
  Sorted f l
  → (∀ y, y ∈ l → f y x)
    → Sorted f (l ++ [x]).
Proof.
clear; intros α f l x Hs Hf.
induction l as [| z]; [ constructor; constructor | simpl ].
apply Sorted_inv in Hs.
destruct Hs as (Hs, Hr).
apply IHl in Hs. {
  constructor; [ assumption | idtac ].
  destruct l as [| t]. {
    constructor; apply Hf; left; reflexivity.
  } {
    constructor; apply HdRel_inv in Hr; assumption.
  }
}
intros y Hy.
apply Hf; right; assumption.
Qed.

Theorem Sorted_hd : ∀ (pt₁ pt₂ : nat * Q) pts,
  Sorted fst_lt [pt₁ … pts]
  → pt₂ ∈ pts
    → (fst pt₁ < fst pt₂)%nat.
Proof.
intros pt₁ pt₂ pts Hsort Hpt.
revert pt₁ pt₂ Hsort Hpt.
induction pts as [| pt]; intros; [ contradiction | idtac ].
apply Sorted_inv_2 in Hsort.
destruct Hsort as (Hlt, Hsort).
destruct Hpt as [Hpt| Hpt]; [ subst pt; assumption | idtac ].
eapply Nat.lt_trans; [ eassumption | idtac ].
apply IHpts; assumption.
Qed.

Theorem Sorted_not_in {A} : ∀ (f : A → A → Prop) a b l,
  (∀ x, ¬f x x)
  → (∀ x y z, f x y → f y z → f x z)
    → Sorted f [b … l]
      → f a b
        → a ∉ [b … l].
Proof.
intros f a b l Hirr Htran Hsort Hab Hin.
destruct Hin as [Hin| Hin]. {
  subst b.
  eapply Hirr; eassumption.
}
induction l as [| c]; [ contradiction | intros ].
destruct Hin as [Hin| Hin]. {
  subst c.
  apply Sorted_inv_2 in Hsort; destruct Hsort as (Hlt, _).
  eapply Htran in Hab; [ eapply Hirr, Hab | eassumption ].
}
apply IHl; [ idtac | assumption ].
eapply Sorted_minus_2nd; eassumption.
Qed.

Theorem Sorted_map : ∀ A B P (Q : A → B) (l : list A),
  Sorted (λ x y, P (Q x) (Q y)) l
  → Sorted P (List.map Q l).
Proof.
intros A B P Q l Hsort.
apply Sorted_LocallySorted_iff in Hsort.
apply Sorted_LocallySorted_iff.
induction l as [| a]; [ constructor | simpl ].
destruct l as [| b]; simpl; constructor. {
  apply IHl.
  inversion Hsort; subst; assumption.
} {
  inversion Hsort; subst; assumption.
}
Qed.

Theorem Sorted_trans_app : ∀ A (g : A → A → Prop) x y l,
  (∀ x y z, g x y → g y z → g x z)
  → x ∈ l
    → Sorted g (l ++ [y])
      → g x y.
Proof.
intros A g x y l Htrans Hx Hsort.
apply Sorted_LocallySorted_iff in Hsort.
revert x y Hx Hsort.
induction l as [| z]; intros; [ contradiction | idtac ].
simpl in Hsort.
inversion Hsort. {
  symmetry in H1.
  apply List.app_eq_nil in H1.
  destruct H1 as (_, H); discriminate H.
}
subst.
destruct Hx as [Hx| Hx]. {
  subst z.
  destruct l as [| z]. {
    simpl in H0.
    injection H0; clear H0; intros; subst.
    assumption.
  }
  eapply Htrans; [ eassumption | idtac ].
  apply IHl. {
    simpl in H0.
    injection H0; clear H0; intros; subst.
    left; reflexivity.
  }
  rewrite <- H0; assumption.
}
apply IHl; [ assumption | idtac ].
rewrite <- H0; assumption.
Qed.

Theorem HdRel_app : ∀ A (R : A → A → Prop) a l₁ l₂,
  HdRel R a l₁
  → HdRel R a l₂
    → HdRel R a (l₁ ++ l₂).
Proof.
intros A R a l₁ l₂ H₁ H₂.
destruct l₁ as [| b]; [ assumption | constructor ].
apply HdRel_inv in H₁; assumption.
Qed.

(* *)

Theorem minimise_slope_le : ∀ pt₁ pt₂ pts₂ ms,
  Sorted fst_lt [pt₂ … pts₂]
  → minimise_slope pt₁ pt₂ pts₂ = ms
    → (fst pt₂ <= fst (fin_pt ms))%nat.
Proof.
intros pt₁ pt₂ pts₂ ms Hsort Hms.
revert pt₁ pt₂ ms Hsort Hms.
induction pts₂ as [| pt]; intros. {
  subst ms; apply Nat.le_refl.
}
simpl in Hms.
remember (minimise_slope pt₁ pt pts₂) as ms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
destruct c; subst ms; simpl; [ idtac | apply Nat.le_refl | idtac ]. {
  apply Nat.lt_le_incl.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort as (Hlt, Hsort).
  eapply Nat.lt_le_trans; [ eassumption | idtac ].
  symmetry in Heqms₁.
  eapply IHpts₂; eassumption.
} {
  apply Nat.lt_le_incl.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort as (Hlt, Hsort).
  eapply Nat.lt_le_trans; [ eassumption | idtac ].
  symmetry in Heqms₁.
  eapply IHpts₂; eassumption.
}
Qed.

Theorem next_ch_points_hd : ∀ pt₁ pt₂ pt₃ pts₁ seg,
  lower_convex_hull_points [pt₁ … pts₁] = Some (mkns pt₂ pt₃ seg)
  → pt₁ = pt₂.
Proof.
intros * Hnp; simpl in Hnp.
destruct pts₁ as [| pt₄ pts]; [ easy | ].
injection Hnp; clear Hnp; intros H1 H2 H3.
specialize (minimised_slope_beg_pt pt₁ pt₄ pts) as Hm.
now rewrite <- H3, Hm.
Qed.

Theorem beg_lt_end_pt : ∀ pt₁ pt₂ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms
  → (fst (ini_pt ms) < fst (fin_pt ms))%nat.
Proof.
intros pt₁ pt₂ pts ms Hsort Hms.
revert pt₁ pt₂ ms Hsort Hms.
induction pts as [| pt₃]; intros. {
  subst ms; simpl.
  eapply Sorted_hd; [ eassumption | left; reflexivity ].
}
simpl in Hms.
remember (minimise_slope pt₁ pt₃ pts) as ms₁ eqn:Hms₁ .
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
symmetry in Heqc.
symmetry in Hms₁.
erewrite slope_slope_expr in Heqc; [ idtac | eassumption ].
destruct c. {
  subst ms; simpl.
  rewrite <- minimised_slope_beg_pt in |- * at 1.
  rewrite <- Hms₁.
  eapply IHpts; [ idtac | reflexivity ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
} {
  subst ms; simpl.
  eapply Sorted_hd; [ eassumption | left; reflexivity ].
} {
  subst ms₁.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
}
Qed.

Theorem ini_lt_fin_pt : ∀ pts ns,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some ns
  → (fst (ini_pt ns) < fst (fin_pt ns))%nat.
Proof.
intros pts ns Hsort Hns.
unfold lower_convex_hull_points in Hns.
destruct pts as [| pt₁ pts]; [ easy | ].
destruct pts as [| pt₂ pts]; [ easy | ].
remember (minimise_slope pt₁ pt₂ pts) as ms eqn:Hms.
symmetry in Hms.
injection Hns; clear Hns; intros Hns.
rewrite <- Hns; simpl.
now specialize (beg_lt_end_pt pt₁ pt₂ pts ms Hsort Hms) as H.
Qed.

Theorem minimised_slope : ∀ pt₁ pt₂ pt pts ms,
  minimise_slope pt₁ pt pts = ms
  → pt₂ = fin_pt ms
  → slope ms = slope_expr pt₁ pt₂.
Proof.
intros pt₁ pt₂ pt pts ms Hms Hkps.
unfold slope; subst.
rewrite minimised_slope_beg_pt; reflexivity.
Qed.

Theorem end_pt_in : ∀ pt₁ pt₂ pts ms,
  minimise_slope pt₁ pt₂ pts = ms
  → fin_pt ms ∈ [pt₂ … pts].
Proof.
intros pt₁ pt₂ pts ms Hms.
revert pt₁ pt₂ ms Hms.
induction pts as [| pt₃]; intros. {
  subst ms; simpl.
  left; reflexivity.
}
simpl in Hms.
remember (minimise_slope pt₁ pt₃ pts) as ms₁.
rename Heqms₁ into Hms₁.
symmetry in Hms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
symmetry in Heqc.
remember (fin_pt ms) as pt.
destruct c; subst ms; simpl in Heqpt; subst pt. {
  right; eapply IHpts; eassumption.
} {
  left; reflexivity.
} {
  right; eapply IHpts; eassumption.
}
Qed.
