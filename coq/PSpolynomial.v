(* PSpolynomial.v *)

(* polynomials of Puiseux series *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Field.
Require Import Fpolynomial.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_div.

Set Implicit Arguments.

Delimit Scope ps_lap_scope with pslap.

Definition lap_nth α {R : ring α} h la := (List.nth h la 0)%ps.
Definition poly_nth α {R : ring α} h pol := (lap_nth h (al pol)).

Arguments lap_nth _ _ h%nat la%pslap.

(* *)

Definition ps_lap_eq α {R : ring α} la lb :=
  @lap_eq (puiseux_series α) (ps_ring R) la lb.

Definition ps_lap_add α {R : ring α} la lb :=
  @lap_add (puiseux_series α) (ps_ring R) la lb.

Definition ps_lap_mul α {R : ring α} la lb :=
  @lap_mul (puiseux_series α) (ps_ring R) la lb.

Definition ps_lap_pow α {R : ring α} a n :=
  @lap_power (puiseux_series α) (ps_ring R) a n.

Definition ps_lap_comp α {R : ring α} la lb :=
  @lap_compose (puiseux_series α) (ps_ring R) la lb.

Arguments ps_lap_eq _ _ la%pslap lb%pslap.
Arguments ps_lap_add _ _ la%pslap lb%pslap.
Arguments ps_lap_mul _ _ la%pslap lb%pslap.
Arguments ps_lap_pow _ _ a%pslap _.
Arguments ps_lap_comp _ _ la%pslap lb%pslap.

Notation "a = b" := (ps_lap_eq a b) : ps_lap_scope.
Notation "a + b" := (ps_lap_add a b) : ps_lap_scope.
Notation "a * b" := (ps_lap_mul a b) : ps_lap_scope.
Notation "a ^ b" := (ps_lap_pow a b) : ps_lap_scope.
Notation "a ∘ b" := (ps_lap_comp a b) : ps_lap_scope.

Lemma fold_ps_lap_add : ∀ α (R : ring α) a b,
  @lap_add _ (ps_ring R) a b = ps_lap_add a b.
Proof. reflexivity. Qed.

Lemma fold_ps_lap_mul : ∀ α (R : ring α) a b,
  @lap_mul _ (ps_ring R) a b = ps_lap_mul a b.
Proof. reflexivity. Qed.

Lemma fold_ps_lap_pow : ∀ α (R : ring α) a n,
  @lap_power _ (ps_ring R) a n = ps_lap_pow a n.
Proof. reflexivity. Qed.

Lemma fold_ps_lap_comp : ∀ α (R : ring α) a b,
  @lap_compose _ (ps_ring R) a b = ps_lap_comp a b.
Proof. reflexivity. Qed.

Lemma fold_lap_nth : ∀ α (R : ring α) h la,
  List.nth h la 0%ps = lap_nth h la.
Proof. reflexivity. Qed.

Theorem ps_lap_eq_refl {α} {R : ring α} : reflexive _ (@ps_lap_eq _ R).
Proof.
intros la.
progress unfold ps_lap_eq; reflexivity.
Qed.

Theorem ps_lap_eq_sym {α} {R : ring α} : symmetric _ (@ps_lap_eq _ R).
Proof.
intros la lb Hlab.
progress unfold ps_lap_eq; symmetry; assumption.
Qed.

Theorem ps_lap_eq_trans {α} {R : ring α} : transitive _ (@ps_lap_eq _ R).
Proof.
intros la lb lc Hlab Hlbc.
progress unfold ps_lap_eq; etransitivity; eassumption.
Qed.

Add Parametric Relation α (R : ring α) : (list _) (@ps_lap_eq _ R)
 reflexivity proved by ps_lap_eq_refl
 symmetry proved by ps_lap_eq_sym
 transitivity proved by ps_lap_eq_trans
 as ps_lap_eq_rel.

Add Parametric Morphism α (R : ring α) : (@lap_nth _ R)
  with signature eq ==> @lap_eq _ (ps_ring R) ==> eq_ps
  as lap_nth_morph.
Proof.
intros n la lb Hlab.
rewrite Hlab; reflexivity.
Qed.

Add Parametric Morphism α (R : ring α) : (@poly_nth _ R)
  with signature eq ==> @eq_poly _ (ps_ring R) ==> eq_ps
  as poly_nth_morph.
Proof.
intros n pa pb Hpab.
progress unfold poly_nth; rewrite Hpab; reflexivity.
Qed.

Definition ps_pol_eq α {R : ring α} a b :=
  @eq_poly (puiseux_series α) (ps_ring R) a b.

Definition ps_pol_add α {R : ring α} a b :=
  @poly_add (puiseux_series α) (ps_ring R) a b.

Definition ps_pol_mul α {R : ring α} a b :=
  @poly_mul (puiseux_series α) (ps_ring R) a b.

Definition ps_pol_pow α {R : ring α} a n :=
  @poly_power (puiseux_series α) (ps_ring R) a n.

Definition ps_pol_comp α {R : ring α} a b :=
  @poly_compose (puiseux_series α) (ps_ring R) a b.

Definition ps_pol α a := @mkpol (puiseux_series α) a.

Lemma fold_ps_pol_add : ∀ α (R : ring α) a b,
  @poly_add _ (ps_ring R) a b = ps_pol_add a b.
Proof. reflexivity. Qed.

Lemma fold_ps_pol_mul : ∀ α (R : ring α) a b,
  @poly_mul _ (ps_ring R) a b = ps_pol_mul a b.
Proof. reflexivity. Qed.

Lemma fold_ps_pol_pow : ∀ α (R : ring α) a b,
  @poly_power _ (ps_ring R) a b = ps_pol_pow a b.
Proof. reflexivity. Qed.

Delimit Scope ps_pol_scope with pspol.
Notation "a = b" := (ps_pol_eq a b) : ps_pol_scope.
Notation "a + b" := (ps_pol_add a b) : ps_pol_scope.
Notation "a * b" := (ps_pol_mul a b) : ps_pol_scope.
Notation "a ^ b" := (ps_pol_pow a b) : ps_pol_scope.
Notation "a ∘ b" := (ps_pol_comp a b) : ps_pol_scope.
Notation "'POL' l" := (ps_pol l) (at level 1) : ps_pol_scope.
