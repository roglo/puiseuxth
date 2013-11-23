(* $Id: Field.v,v 2.22 2013-11-23 03:47:20 deraugla Exp $ *)

Require Import Utf8.
Require Import Ring_theory.
Require Import Field_theory.
Require Import Setoid.

Set Implicit Arguments.

Module Field.

Record t α :=
  { zero : α;
    one : α;
    add : α → α → α;
    mul : α → α → α;
    opp : α → α;
    inv : α → α;
    eq : α → α → Prop;
    eq_refl : ∀ a, eq a a;
    eq_sym : ∀ a b, eq a b → eq b a;
    eq_trans : ∀ a b c, eq a b → eq b c → eq a c;
    neq_1_0 : not (eq one zero);
    add_comm : ∀ a b, eq (add a b) (add b a);
    add_assoc : ∀ a b c, eq (add a (add b c)) (add (add a b) c);
    add_0_l : ∀ a, eq (add zero a) a;
    add_opp_l : ∀ a, eq (add (opp a) a) zero;
    add_compat_l : ∀ a b c, eq a b → eq (add c a) (add c b);
    mul_comm : ∀ a b, eq (mul a b) (mul b a);
    mul_assoc : ∀ a b c, eq (mul a (mul b c)) (mul (mul a b) c);
    mul_1_l : ∀ a, eq (mul one a) a;
    mul_compat_l : ∀ a b c, eq a b → eq (mul c a) (mul c b);
    mul_inv_l : ∀ a, not (eq a zero) → eq (mul (inv a) a) one;
    mul_add_distr_l : ∀ a b c,
      eq (mul a (add b c)) (add (mul a b) (mul a c)) }.

Add Parametric Relation α (fld : t α) : α (eq fld)
 reflexivity proved by (eq_refl fld)
 symmetry proved by (eq_sym fld)
 transitivity proved by (eq_trans fld)
 as eq_rel.

Add Parametric Morphism α (fld : t α) : (add fld) with 
signature eq fld ==> eq fld ==> eq fld
  as add_morph.
Proof.
intros a b Hab c d Hcd.
rewrite add_comm; symmetry.
rewrite add_comm; symmetry.
rewrite add_compat_l; [ idtac | eassumption ].
rewrite add_comm; symmetry.
rewrite add_comm; symmetry.
rewrite add_compat_l; [ reflexivity | eassumption ].
Qed.

Add Parametric Morphism α (fld : t α) : (mul fld) with 
signature eq fld ==> eq fld ==> eq fld
  as mul_morph.
Proof.
intros a b Hab c d Hcd.
rewrite mul_comm; symmetry.
rewrite mul_comm; symmetry.
rewrite mul_compat_l; [ idtac | eassumption ].
rewrite mul_comm; symmetry.
rewrite mul_comm; symmetry.
rewrite mul_compat_l; [ reflexivity | eassumption ].
Qed.

Section fld.

Variable α : Type.
Variable fld : t α.
Notation "a ≍ b" := (eq fld a b) (at level 70).
Notation "a ≭ b" := (not (eq fld a b)) (at level 70).

Delimit Scope scope with fld.
Notation "0" := (zero fld) : scope.
Notation "1" := (one fld) : scope.
Notation "- a" := (opp fld a) : scope.
Notation "a + b" := (add fld a b)
  (left associativity, at level 50) : scope.
Notation "a - b" := (add fld a (opp fld b))
  (left associativity, at level 50) : scope.
Notation "a * b" := (mul fld a b)
  (left associativity, at level 40) : scope.

Theorem add_opp_r : ∀ x, (x + (-x) ≍ 0)%fld.
Proof.
intros x; rewrite add_comm.
apply add_opp_l.
Qed.

Theorem mul_1_r : ∀ a, (a * 1 ≍ a)%fld.
Proof.
intros a.
rewrite mul_comm, mul_1_l.
reflexivity.
Qed.

Theorem mul_inv_r : ∀ x, (x ≭ 0 → x * inv fld x ≍ 1)%fld.
Proof.
intros x H; rewrite mul_comm.
apply mul_inv_l; assumption.
Qed.

Theorem add_compat_r : ∀ a b c, (a ≍ b → a + c ≍ b + c)%fld.
Proof.
intros a b c Hab.
rewrite Hab; reflexivity.
Qed.

Theorem mul_compat_r : ∀ a b c, (a ≍ b → a * c ≍ b * c)%fld.
Proof.
intros a b c Hab.
rewrite Hab; reflexivity.
Qed.

Theorem mul_add_distr_r : ∀ x y z,
 ((x + y) * z)%fld ≍ (x * z + y * z)%fld.
Proof.
intros x y z.
rewrite mul_comm.
rewrite mul_add_distr_l.
rewrite mul_comm.
assert (eq fld (mul fld z y) (mul fld y z)) as H.
 apply mul_comm.

 rewrite H; reflexivity.
Qed.

Lemma ring :
  @ring_theory α (zero fld) (one fld) (add fld) (mul fld)
    (λ x y, add fld x (opp fld y)) (opp fld) (eq fld).
Proof.
constructor.
 apply add_0_l.

 apply add_comm.

 apply add_assoc.

 apply mul_1_l.

 apply mul_comm.

 apply mul_assoc.

 apply mul_add_distr_r.

 reflexivity.

 apply add_opp_r.
Qed.

(* comment ça marche, ce truc-là ? et à quoi ça sert ?

Lemma ring_morph :
  @ring_morph α (zero fld) (one fld) (add fld) (mul fld)
    (λ x y, add fld x (opp fld y)) (opp fld) (eq fld).

(R : Type) (rO rI : R) (radd rmul rsub : R → R → R)
(ropp : R → R) (req : R → R → Prop) (C : Type) (cO cI : C)
(cadd cmul csub : C → C → C) (copp : C → C) (ceqb : C → C → bool)
(phi : C → R) : Prop := mkmorph

Add Ring ring : ring (morphism glop).
bbb.
*)

Definition field :=
  {| F_R := ring;
     F_1_neq_0 := neq_1_0 fld;
     Fdiv_def x y := eq_refl fld (mul fld x (inv fld y));
     Finv_l := mul_inv_l fld |}.

(* *)

Theorem add_0_r : ∀ a, (a + 0 ≍ a)%fld.
Proof.
intros a.
rewrite add_comm.
apply add_0_l.
Qed.

Theorem opp_0 : (- 0 ≍ 0)%fld.
Proof.
etransitivity; [ symmetry; apply add_0_l | idtac ].
apply add_opp_r.
Qed.

Theorem add_reg_r : ∀ a b c, (a + c ≍ b + c → a ≍ b)%fld.
Proof.
intros a b c Habc.
apply add_compat_r with (c := (- c)%fld) in Habc.
do 2 rewrite <- add_assoc in Habc.
rewrite add_opp_r in Habc.
do 2 rewrite add_0_r in Habc.
assumption.
Qed.

Theorem add_reg_l : ∀ a b c, (c + a ≍ c + b → a ≍ b)%fld.
Proof.
intros a b c Habc.
apply add_reg_r with (c := c).
rewrite add_comm; symmetry.
rewrite add_comm; symmetry.
assumption.
Qed.

Theorem mul_reg_r : ∀ a b c, (c ≭ 0 → a * c ≍ b * c → a ≍ b)%fld.
Proof.
intros a b c Hc Habc.
apply mul_compat_r with (c := inv fld c) in Habc.
do 2 rewrite <- mul_assoc in Habc.
rewrite mul_inv_r in Habc; [ idtac | assumption ].
do 2 rewrite mul_1_r in Habc.
assumption.
Qed.

Theorem mul_reg_l : ∀ a b c, (c ≭ 0 → c * a ≍ c * b → a ≍ b)%fld.
Proof.
intros a b c Hc Habc.
rewrite mul_comm in Habc; symmetry in Habc.
rewrite mul_comm in Habc; symmetry in Habc.
eapply mul_reg_r; eassumption.
Qed.

Theorem add_id_uniq : ∀ a b, (a + b ≍ a → b ≍ 0)%fld.
Proof.
intros a b Hab.
rewrite add_comm in Hab.
apply add_reg_r with (c := a).
rewrite add_0_l; assumption.
Qed.

Theorem mul_0_l : ∀ a, (0 * a ≍ 0)%fld.
Proof.
intros a.
assert (0 * a + a ≍ a)%fld as H.
 transitivity (0 * a + 1 * a)%fld.
  rewrite mul_1_l; reflexivity.

  rewrite <- mul_add_distr_r.
  rewrite add_0_l, mul_1_l.
  reflexivity.

 apply add_reg_r with (c := a).
 rewrite add_0_l; assumption.
Qed.

Theorem mul_0_r : ∀ a, (a * 0 ≍ 0)%fld.
Proof.
intros a.
rewrite mul_comm, mul_0_l.
reflexivity.
Qed.

Theorem add_shuffle0 : ∀ n m p,
  eq fld (add fld (add fld n m) p) (add fld (add fld n p) m).
Proof.
intros n m p.
do 2 rewrite <- add_assoc.
assert (eq fld (add fld m p) (add fld p m)) as H by apply add_comm.
rewrite H; reflexivity.
Qed.

Theorem mul_shuffle0 : ∀ n m p,
  eq fld (mul fld (mul fld n m) p) (mul fld (mul fld n p) m).
Proof.
intros n m p.
do 2 rewrite <- mul_assoc.
assert (eq fld (mul fld m p) (mul fld p m)) as H by apply mul_comm.
rewrite H; reflexivity.
Qed.

Theorem mul_eq_0 : ∀ n m, (n ≍ 0 ∨ m ≍ 0 → n * m ≍ 0)%fld.
Proof.
intros n m H.
destruct H as [H| H]; rewrite H; [ apply mul_0_l | apply mul_0_r ].
Qed.

Theorem eq_mul_0_l : ∀ n m, (n * m ≍ 0 → m ≭ 0 → n ≍ 0)%fld.
Proof.
intros n m Hnm Hm.
rewrite <- mul_0_l with (a := m) in Hnm.
apply mul_reg_r in Hnm; assumption.
Qed.

Theorem eq_mul_0_r : ∀ n m, (n * m ≍ 0 → n ≭ 0 → m ≍ 0)%fld.
Proof.
intros n m Hnm Hm.
rewrite <- mul_0_r with (a := n) in Hnm.
apply mul_reg_l in Hnm; assumption.
Qed.

End fld.

End Field.
