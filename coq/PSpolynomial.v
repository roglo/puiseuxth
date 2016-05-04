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

Definition ps_lap_nth α {R : ring α} h la := (List.nth h la 0)%ps.
Definition ps_poly_nth α {R : ring α} h pol := (ps_lap_nth h (al pol)).

Arguments ps_lap_nth _ _ h%nat la%pslap.

(* *)

Definition ps_lap_eq α {R : ring α} {K : field R} la lb :=
  @lap_eq (puiseux_series α) (ps_ring K) la lb.

Definition ps_lap_add α {R : ring α} {K : field R} la lb :=
  @lap_add (puiseux_series α) (ps_ring K) la lb.

Definition ps_lap_mul α {R : ring α} {K : field R} la lb :=
  @lap_mul (puiseux_series α) (ps_ring K) la lb.

Definition ps_lap_pow α {R : ring α} {K : field R} a n :=
  @lap_power (puiseux_series α) (ps_ring K) a n.

Definition ps_lap_comp α {R : ring α} {K : field R} la lb :=
  @lap_compose (puiseux_series α) (ps_ring K) la lb.

Arguments ps_lap_eq _ _ _ la%pslap lb%pslap.
Arguments ps_lap_add _ _ _ la%pslap lb%pslap.
Arguments ps_lap_mul _ _ _ la%pslap lb%pslap.
Arguments ps_lap_pow _ _ _ a%pslap _.
Arguments ps_lap_comp _ _ _ la%pslap lb%pslap.

Notation "a = b" := (ps_lap_eq a b) : ps_lap_scope.
Notation "a ≠ b" := (not (ps_lap_eq a b)) : ps_lap_scope.
Notation "a + b" := (ps_lap_add a b) : ps_lap_scope.
Notation "a * b" := (ps_lap_mul a b) : ps_lap_scope.
Notation "a ^ b" := (ps_lap_pow a b) : ps_lap_scope.
Notation "a ∘ b" := (ps_lap_comp a b) : ps_lap_scope.

Theorem fold_ps_lap_add : ∀ α (R : ring α) (K : field R) a b,
  @lap_add _ (ps_ring K) a b = ps_lap_add a b.
Proof. reflexivity. Qed.

Theorem fold_ps_lap_mul : ∀ α (R : ring α) (K : field R) a b,
  @lap_mul _ (ps_ring K) a b = ps_lap_mul a b.
Proof. reflexivity. Qed.

Theorem fold_ps_lap_pow : ∀ α (R : ring α) (K : field R) a n,
  @lap_power _ (ps_ring K) a n = ps_lap_pow a n.
Proof. reflexivity. Qed.

Theorem fold_ps_lap_comp : ∀ α (R : ring α) (K : field R) a b,
  @lap_compose _ (ps_ring K) a b = ps_lap_comp a b.
Proof. reflexivity. Qed.

Theorem fold_ps_lap_nth : ∀ α (R : ring α) h la,
  List.nth h la 0%ps = ps_lap_nth h la.
Proof. reflexivity. Qed.

Theorem ps_lap_eq_refl {α} {R : ring α} {K : field R} :
  reflexive _ (@ps_lap_eq _ R K).
Proof.
intros la.
progress unfold ps_lap_eq; reflexivity.
Qed.

Theorem ps_lap_eq_sym {α} {R : ring α} {K : field R} :
  symmetric _ (@ps_lap_eq _ R K).
Proof.
intros la lb Hlab.
progress unfold ps_lap_eq; symmetry; assumption.
Qed.

Theorem ps_lap_eq_trans {α} {R : ring α} {K : field R} :
  transitive _ (@ps_lap_eq _ R K).
Proof.
intros la lb lc Hlab Hlbc.
progress unfold ps_lap_eq; etransitivity; eassumption.
Qed.

Add Parametric Relation α (R : ring α) (K : field R) :
  (list _) (@ps_lap_eq _ R K)
 reflexivity proved by ps_lap_eq_refl
 symmetry proved by ps_lap_eq_sym
 transitivity proved by ps_lap_eq_trans
 as ps_lap_eq_rel.

Add Parametric Morphism α (R : ring α) (K : field R) : (@ps_lap_nth _ R)
  with signature eq ==> @lap_eq _ (ps_ring K) ==> eq_ps
  as ps_lap_nth_morph.
Proof.
intros n la lb Hlab.
rewrite Hlab; reflexivity.
Qed.

Add Parametric Morphism α (R : ring α) (K : field R) : (@ps_poly_nth _ R)
  with signature eq ==> @eq_poly _ (ps_ring K) ==> eq_ps
  as ps_poly_nth_morph.
Proof.
intros n pa pb Hpab.
progress unfold ps_poly_nth; rewrite Hpab; reflexivity.
Qed.

Definition ps_pol_eq α {R : ring α} {K : field R} a b :=
  @eq_poly (puiseux_series α) (ps_ring K) a b.

Definition ps_pol_add α {R : ring α} {K : field R} a b :=
  @poly_add (puiseux_series α) (ps_ring K) a b.

Definition ps_pol_mul α {R : ring α} {K : field R} a b :=
  @poly_mul (puiseux_series α) (ps_ring K) a b.

Definition ps_pol_pow α {R : ring α} {K : field R} a n :=
  @poly_power (puiseux_series α) (ps_ring K) a n.

Definition ps_pol_comp α {R : ring α} {K : field R} a b :=
  @poly_compose (puiseux_series α) (ps_ring K) a b.

Definition ps_pol_apply α {R : ring α} {K : field R} a b :=
  @apply_poly _ (ps_ring K) a b.

Definition ps_pol α a := @mkpol (puiseux_series α) a.

Theorem fold_ps_pol_add : ∀ α (R : ring α) (K : field R) a b,
  @poly_add _ (ps_ring K) a b = ps_pol_add a b.
Proof. reflexivity. Qed.

Theorem fold_ps_pol_mul : ∀ α (R : ring α) (K : field R) a b,
  @poly_mul _ (ps_ring K) a b = ps_pol_mul a b.
Proof. reflexivity. Qed.

Delimit Scope ps_pol_scope with pspol.
Notation "a = b" := (ps_pol_eq a b) : ps_pol_scope.
Notation "a + b" := (ps_pol_add a b) : ps_pol_scope.
Notation "a * b" := (ps_pol_mul a b) : ps_pol_scope.
Notation "a ^ b" := (ps_pol_pow a b) : ps_pol_scope.
Notation "a ∘ b" := (ps_pol_comp a b) : ps_pol_scope.
Notation "'POL' l" := (ps_pol l) (at level 1) : ps_pol_scope.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Theorem ps_lap_nth_add : ∀ n la lb,
  (ps_lap_nth n (la + lb) = ps_lap_nth n la + ps_lap_nth n lb)%ps.
Proof.
intros n la lb.
unfold ps_lap_add; simpl.
unfold ps_lap_nth; simpl.
revert n lb.
induction la as [| a]; intros; simpl.
 rewrite match_id, ps_add_0_l; reflexivity.

 destruct lb as [| b]; simpl.
  rewrite match_id, ps_add_0_r; reflexivity.

  destruct n; [ reflexivity | apply IHla ].
Qed.

End theorems.
