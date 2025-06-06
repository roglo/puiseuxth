(* Field.v *)

From Stdlib Require Import Utf8.
Require Import Setoid.
Require Import Morphisms.

Set Implicit Arguments.

Reserved Notation "¹/ a" (at level 1).
Reserved Notation "a ∘ b" (left associativity, at level 32).

Class ring α :=
  { rng_zero : α;
    rng_one : α;
    rng_add : α → α → α;
    rng_mul : α → α → α;
    rng_opp : α → α;
    rng_eq : α → α → Prop;
    rng_eq_refl : ∀ a, rng_eq a a;
    rng_eq_sym : ∀ a b, rng_eq a b → rng_eq b a;
    rng_eq_trans : ∀ a b c, rng_eq a b → rng_eq b c → rng_eq a c;
    rng_add_comm : ∀ a b, rng_eq (rng_add a b) (rng_add b a);
    rng_add_assoc : ∀ a b c,
      rng_eq (rng_add a (rng_add b c)) (rng_add (rng_add a b) c);
    rng_add_0_l : ∀ a, rng_eq (rng_add rng_zero a) a;
    rng_add_opp_l : ∀ a, rng_eq (rng_add (rng_opp a) a) rng_zero;
    rng_add_compat_l : ∀ a b c,
      rng_eq a b → rng_eq (rng_add c a) (rng_add c b);
    rng_mul_comm : ∀ a b, rng_eq (rng_mul a b) (rng_mul b a);
    rng_mul_assoc : ∀ a b c,
      rng_eq (rng_mul a (rng_mul b c)) (rng_mul (rng_mul a b) c);
    rng_mul_1_l : ∀ a, rng_eq (rng_mul rng_one a) a;
    rng_mul_compat_l : ∀ a b c,
      rng_eq a b → rng_eq (rng_mul c a) (rng_mul c b);
    rng_mul_add_distr_l : ∀ a b c,
      rng_eq (rng_mul a (rng_add b c))
        (rng_add (rng_mul a b) (rng_mul a c)) }.

Declare Scope field_scope.
Delimit Scope field_scope with K.
Notation "a = b" := (rng_eq a b) : field_scope.
Notation "a ≠ b" := (¬ rng_eq a b) : field_scope.
Notation "a + b" := (rng_add a b) : field_scope.
Notation "a - b" := (rng_add a (rng_opp b)) : field_scope.
Notation "a * b" := (rng_mul a b) : field_scope.
Notation "- a" := (rng_opp a) : field_scope.
Notation "0" := rng_zero : field_scope.
Notation "1" := rng_one : field_scope.

Fixpoint rng_power {α} {R : ring α} a n :=
  match n with
  | O => 1%K
  | S m => (a * rng_power a m)%K
  end.

Notation "a ^ b" := (rng_power a b) : field_scope.

Add Parametric Relation α (K : ring α) : α rng_eq
  reflexivity proved by rng_eq_refl
  symmetry proved by rng_eq_sym
  transitivity proved by rng_eq_trans
  as eq_rel.

Global Instance add_morph α (K : ring α) :
  Proper (rng_eq ==> rng_eq ==> rng_eq) rng_add.
Proof.
intros a b Hab c d Hcd.
rewrite rng_add_comm; symmetry.
rewrite rng_add_comm; symmetry.
rewrite rng_add_compat_l; [ idtac | eassumption ].
rewrite rng_add_comm; symmetry.
rewrite rng_add_comm; symmetry.
rewrite rng_add_compat_l; [ reflexivity | eassumption ].
Qed.

Global Instance opp_morph α (K : ring α) :
  Proper (rng_eq ==> rng_eq) rng_opp.
Proof.
intros a b Heq.
apply rng_add_compat_l with (c := rng_opp b) in Heq.
rewrite rng_add_opp_l in Heq.
rewrite rng_add_comm in Heq.
apply rng_add_compat_l with (c := rng_opp a) in Heq.
rewrite rng_add_assoc in Heq.
rewrite rng_add_opp_l in Heq.
rewrite rng_add_0_l in Heq.
symmetry in Heq.
rewrite rng_add_comm in Heq.
rewrite rng_add_0_l in Heq.
assumption.
Qed.

Global Instance mul_morph α (F : ring α) :
  Proper (rng_eq ==> rng_eq ==> rng_eq) rng_mul.
Proof.
intros a b Hab c d Hcd.
rewrite rng_mul_comm; symmetry.
rewrite rng_mul_comm; symmetry.
rewrite rng_mul_compat_l; [ idtac | eassumption ].
rewrite rng_mul_comm; symmetry.
rewrite rng_mul_comm; symmetry.
rewrite rng_mul_compat_l; [ reflexivity | eassumption ].
Qed.

Section ring_theorems.

Variable α : Type.
Variable r : ring α.

Theorem rng_add_opp_r : ∀ x, (x - x = 0)%K.
Proof.
intros x; simpl; rewrite rng_add_comm.
apply rng_add_opp_l.
Qed.

Theorem rng_mul_1_r : ∀ a, (a * 1 = a)%K.
Proof.
intros a; simpl.
rewrite rng_mul_comm, rng_mul_1_l.
reflexivity.
Qed.

Theorem rng_add_compat_r : ∀ a b c,
  (a = b)%K
  → (a + c = b + c)%K.
Proof.
intros a b c Hab.
rewrite Hab; reflexivity.
Qed.

Theorem rng_add_compat : ∀ a b c d,
  (a = b)%K
  → (c = d)%K
  → (a + c = b + d)%K.
Proof.
intros a b c d Hab Hcd.
rewrite Hab, Hcd; reflexivity.
Qed.

Theorem rng_mul_compat_r : ∀ a b c,
  (a = b)%K
  → (a * c = b * c)%K.
Proof.
intros a b c Hab; simpl in Hab |- *.
rewrite Hab; reflexivity.
Qed.

Theorem rng_mul_compat : ∀ a b c d,
  (a = b)%K
  → (c = d)%K
  → (a * c = b * d)%K.
Proof.
intros a b c d Hab Hcd.
rewrite Hab, Hcd; reflexivity.
Qed.

Theorem rng_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%K.
Proof.
intros x y z; simpl.
rewrite rng_mul_comm.
rewrite rng_mul_add_distr_l.
rewrite rng_mul_comm.
assert (rng_eq (rng_mul z y) (rng_mul y z)) as H. {
  apply rng_mul_comm.
}
rewrite H; reflexivity.
Qed.

Theorem rng_add_0_r : ∀ a, (a + 0 = a)%K.
Proof.
intros a; simpl.
rewrite rng_add_comm.
apply rng_add_0_l.
Qed.

Theorem rng_opp_0 : (- 0 = 0)%K.
Proof.
simpl; etransitivity; [ symmetry; apply rng_add_0_l | idtac ].
apply rng_add_opp_r.
Qed.

Theorem rng_add_reg_r : ∀ a b c, (a + c = b + c)%K → (a = b)%K.
Proof.
intros a b c Habc; simpl in Habc; simpl.
apply rng_add_compat_r with (c := (- c)%K) in Habc.
do 2 rewrite <- rng_add_assoc in Habc.
rewrite rng_add_opp_r in Habc.
do 2 rewrite rng_add_0_r in Habc.
assumption.
Qed.

Theorem rng_add_reg_l : ∀ a b c, (c + a = c + b)%K → (a = b)%K.
Proof.
intros a b c Habc; simpl in Habc; simpl.
apply rng_add_reg_r with (c := c).
rewrite rng_add_comm; symmetry.
rewrite rng_add_comm; symmetry.
assumption.
Qed.

Theorem rng_mul_0_l : ∀ a, (0 * a = 0)%K.
Proof.
intros a.
assert ((0 * a + a = a)%K) as H. {
  transitivity ((0 * a + 1 * a)%K). {
    rewrite rng_mul_1_l; reflexivity.
  }
  rewrite <- rng_mul_add_distr_r.
  rewrite rng_add_0_l, rng_mul_1_l.
  reflexivity.
}
apply rng_add_reg_r with (c := a).
rewrite rng_add_0_l; assumption.
Qed.

Theorem rng_mul_0_r : ∀ a, (a * 0 = 0)%K.
Proof.
intros a; simpl.
rewrite rng_mul_comm, rng_mul_0_l.
reflexivity.
Qed.

Theorem rng_mul_opp_l : ∀ a b, ((- a) * b = - (a * b))%K.
Proof.
intros a b; simpl.
apply rng_add_reg_l with (c := (a * b)%K).
rewrite rng_add_opp_r.
rewrite <- rng_mul_add_distr_r.
rewrite rng_add_opp_r, rng_mul_0_l.
reflexivity.
Qed.

Theorem rng_mul_opp_r : ∀ a b, (a * (- b) = - (a * b))%K.
Proof.
intros a b; simpl.
rewrite rng_mul_comm; symmetry.
rewrite rng_mul_comm; symmetry.
apply rng_mul_opp_l.
Qed.

Theorem rng_add_move_0_r : ∀ a b, (a + b = 0)%K ↔ (a = - b)%K.
Proof.
intros a b.
split; intros H. {
  apply rng_add_compat_r with (c := (- b)%K) in H.
  rewrite <- rng_add_assoc in H.
  rewrite rng_add_opp_r in H.
  rewrite rng_add_0_r, rng_add_0_l in H; assumption.
} {
  rewrite H.
  rewrite rng_add_opp_l; reflexivity.
}
Qed.

Theorem rng_opp_inj_wd : ∀ a b, (- a = - b)%K ↔ (a = b)%K.
Proof.
intros a b; split; intros H. {
  apply rng_add_move_0_r in H.
  rewrite rng_add_comm in H.
  apply rng_add_move_0_r in H.
  rewrite H.
  apply rng_add_move_0_r.
  apply rng_add_opp_r.
}
rewrite H; reflexivity.
Qed.

Theorem rng_add_add_swap : ∀ n m p, (n + m + p = n + p + m)%K.
Proof.
intros n m p; simpl.
do 2 rewrite <- rng_add_assoc.
assert (m + p = p + m)%K as H by apply rng_add_comm.
rewrite H; reflexivity.
Qed.

Theorem rng_mul_mul_swap : ∀ n m p, (n * m * p = n * p * m)%K.
Proof.
intros n m p.
do 2 rewrite <- rng_mul_assoc.
assert (m * p = p * m)%K as H by apply rng_mul_comm.
rewrite H; reflexivity.
Qed.

Theorem rng_mul_eq_0 : ∀ n m,
  (n = 0)%K ∨ (m = 0)%K
  → (n * m = 0)%K.
Proof.
intros n m H; simpl in H; simpl.
destruct H as [H| H]; rewrite H; [ apply rng_mul_0_l | apply rng_mul_0_r ].
Qed.

End ring_theorems.

Class field α (rng_ring : ring α) :=
  { fld_inv : α → α;
    fld_mul_inv_l : ∀ a,
      not (rng_eq a rng_zero)
      → rng_eq (rng_mul (fld_inv a) a) rng_one;
    fld_zerop : ∀ a, { rng_eq a rng_zero } + { not (rng_eq a rng_zero) } }.
Notation "¹/ a" := (fld_inv a) : field_scope.

(* Decidability of equality has been added for our field (fld_zerop),
   because it is required by the theorem. *)

Section field_theorems.

Variable α : Type.
Variable r : ring α.
Variable f : field r.

Theorem fld_mul_inv_r : ∀ x, (x ≠ 0)%K → (x * ¹/ x = 1)%K.
Proof.
intros x H; simpl; rewrite rng_mul_comm.
apply fld_mul_inv_l; assumption.
Qed.

Theorem fld_mul_reg_r : ∀ a b c,
  (c ≠ 0)%K
  → (a * c = b * c)%K
    → (a = b)%K.
Proof.
intros a b c Hc Habc; simpl in Hc, Habc; simpl.
apply rng_mul_compat_r with (c := (¹/ c)%K) in Habc.
do 2 rewrite <- rng_mul_assoc in Habc.
rewrite fld_mul_inv_r in Habc; [ idtac | assumption ].
do 2 rewrite rng_mul_1_r in Habc.
assumption.
Qed.

Theorem fld_mul_reg_l : ∀ a b c,
  (c ≠ 0)%K
  → (c * a = c * b)%K
  → (a = b)%K.
Proof.
intros a b c Hc Habc; simpl in Hc, Habc; simpl.
rewrite rng_mul_comm in Habc; symmetry in Habc.
rewrite rng_mul_comm in Habc; symmetry in Habc.
eapply fld_mul_reg_r; eassumption.
Qed.

Theorem fld_eq_mul_0_l : ∀ n m,
  (n * m = 0)%K
  → (m ≠ 0)%K
  → (n = 0)%K.
Proof.
intros n m Hnm Hm.
rewrite <- rng_mul_0_l in Hnm.
apply fld_mul_reg_r in Hnm; assumption.
Qed.

Theorem fld_eq_mul_0_r : ∀ n m,
  (n * m = 0)%K
  → (n ≠ 0)%K
  → (m = 0)%K.
Proof.
intros n m Hnm Hm; simpl in Hnm, Hm; simpl.
rewrite <- rng_mul_0_r in Hnm.
apply fld_mul_reg_l in Hnm; assumption.
Qed.

End field_theorems.

Global Hint Resolve rng_eq_refl : Arith.
