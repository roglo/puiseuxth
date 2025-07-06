(* PSpolynomial.v *)

(* polynomials of Puiseux series *)

From Stdlib Require Import Utf8 Relations Morphisms.

Require Import A_QArith.
Require Import Misc.
Require Import Field2.
Require Import Fpolynomial.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_mul.
Require Import Ps_div.

Set Implicit Arguments.

Declare Scope ps_lap_scope.
Delimit Scope ps_lap_scope with pslap.

Definition ps_lap_nth α {R : ring α} h la := (List.nth h la 0)%ps.
Definition ps_poly_nth α {R : ring α} h f := (ps_lap_nth h (al f)).

Arguments ps_lap_nth _ _ h%_nat la%_pslap.

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

Arguments ps_lap_eq _ _ _ la%_pslap lb%_pslap.
Arguments ps_lap_add _ _ _ la%_pslap lb%_pslap.
Arguments ps_lap_mul _ _ _ la%_pslap lb%_pslap.
Arguments ps_lap_pow _ _ _ a%_pslap _.
Arguments ps_lap_comp _ _ _ la%_pslap lb%_pslap.

Notation "a = b" := (ps_lap_eq a b) : ps_lap_scope.
Notation "a ≠ b" := (not (ps_lap_eq a b)) : ps_lap_scope.
Notation "a + b" := (ps_lap_add a b) : ps_lap_scope.
Notation "a * b" := (ps_lap_mul a b) : ps_lap_scope.
Notation "a ^ b" := (ps_lap_pow a b) : ps_lap_scope.
Notation "a ∘ b" := (ps_lap_comp a b) : ps_lap_scope.

Inductive ps_lap_forall {α} {R : ring α} {K : field R} (P : _ → Prop) :
  list (puiseux_series α) → Prop :=
  | PLForall_nil : ∀ l, (l = [])%pslap → ps_lap_forall P l
  | PLForall_cons : ∀ x l,
      ([x … l] ≠ [])%pslap
      → P x
      → ps_lap_forall P l
      → ps_lap_forall P [x … l].

Arguments ps_lap_forall α%_type_scope _ _ _ l%_pslap.

Fixpoint ps_lap_in α {R : ring α} {K : field R} a l :=
  match l with
  | [] => False
  | [b … m] => (l ≠ [])%pslap ∧ (b = a)%ps ∨ ps_lap_in a m
  end.

Arguments ps_lap_in _ _ _ a%_ps l%_pslap.

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

Global Instance ps_poly_nth_morph α (R : ring α) (K : field R) :
  Proper (eq ==> @eq_poly _ (ps_ring K) ==> eq_ps) (@ps_poly_nth _ R).
Proof.
intros n n' Hn pa pb Hpab.
subst n'.
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

Declare Scope ps_pol_scope.
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
induction la as [| a]; intros; simpl. {
  rewrite match_id, ps_add_0_l; reflexivity.
}
destruct lb as [| b]; simpl. {
  rewrite match_id, ps_add_0_r; reflexivity.
}
destruct n; [ reflexivity | apply IHla ].
Qed.

Theorem lap_add_map_ps : ∀ la lb,
  (List.map (λ c, ps_monom c 0) (la + lb)%lap =
   List.map (λ c, ps_monom c 0) la + List.map (λ c, ps_monom c 0) lb)%pslap.
Proof.
intros la lb.
apply lap_add_map; intros a b.
rewrite ps_monom_add_l; reflexivity.
Qed.

End theorems.
