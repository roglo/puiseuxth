(* $Id: Field.v,v 2.46 2013-12-23 20:47:31 deraugla Exp $ *)

Require Import Utf8.
(*
Require Import Ring_theory.
Require Import Field_theory.
*)
Require Import Setoid.

Set Implicit Arguments.

Module Tdef.
  Record r α :=
    { zero : α;
      one : α;
      add : α → α → α;
      mul : α → α → α;
      opp : α → α;
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
      mul_add_distr_l : ∀ a b c,
        eq (mul a (add b c)) (add (mul a b) (mul a c)) }.
  Record f α :=
    { ring : r α;
      inv : α → α;
      fld_mul_inv_l : ∀ a,
        not (eq ring a (zero ring))
        → eq ring (mul ring (inv a) a) (one ring) }.
End Tdef.

Module Type FieldType.
  Parameter α : Type.
  Parameter fld : Tdef.f α.
End FieldType.

Module Make (F : FieldType).

  Import F.
  Include Tdef.

  Module Syntax.

  Delimit Scope ring_scope with rng.
  Notation "0" := (λ R, zero R) : ring_scope.
  Notation "1" := (λ R, one R) : ring_scope.
  Notation "- a" := (λ R, opp R (a R)) : ring_scope.
  Notation "a = b" := (λ R, eq R (a R) (b R)) : ring_scope.
  Notation "a ≠ b" := (λ R, not (eq R (a R) (b R))) : ring_scope.
  Notation "a + b" := (λ R, add R (a R) (b R)) : ring_scope.
  Notation "a - b" := (λ R, add R (a R) (opp R (b R))) : ring_scope.
  Notation "a * b" := (λ R, mul R (a R) (b R)) : ring_scope.
  Notation "! a" := (λ _, a) (at level 0, a at level 0) : ring_scope.

  Delimit Scope field_scope with fld.
  Notation "¹/ a" := (inv fld a) (at level 99) : field_scope.

  End Syntax.

  Import Syntax.

  Let R := Tdef.ring fld.

  Add Parametric Relation : α (eq R)
   reflexivity proved by (eq_refl R)
   symmetry proved by (eq_sym R)
   transitivity proved by (eq_trans R)
   as eq_rel.

  Add Parametric Morphism : (add R)
    with signature eq R ==> eq R ==> eq R
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

  Add Parametric Morphism : (opp R)
    with signature eq R ==> eq R
    as opp_morph.
  Proof.
  intros a b Heq.
  apply add_compat_l with (c := (- !b)%rng R) in Heq.
  rewrite add_opp_l in Heq.
  rewrite add_comm in Heq.
  apply add_compat_l with (c := (- !a)%rng R) in Heq.
  rewrite add_assoc in Heq.
  rewrite add_opp_l in Heq.
  rewrite add_0_l in Heq.
  symmetry in Heq.
  rewrite add_comm in Heq.
  rewrite add_0_l in Heq.
  assumption.
  Qed.

  Add Parametric Morphism : (mul R)
    with signature eq R ==> eq R ==> eq R
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

  Theorem add_opp_r : ∀ x, (!x - !x = 0)%rng R.
  Proof.
  intros x; simpl; rewrite add_comm.
  apply add_opp_l.
  Qed.

  Theorem mul_1_r : ∀ a, (!a * 1 = !a)%rng R.
  Proof.
  intros a; simpl.
  rewrite mul_comm, mul_1_l.
  reflexivity.
  Qed.

  Theorem mul_inv_l : ∀ x, (!x ≠ 0)%rng R → (!(inv fld x) * !x = 1)%rng R.
  Proof.
  intros x H.
  apply fld_mul_inv_l; assumption.
  Qed.

  Theorem mul_inv_r : ∀ x, (!x ≠ 0)%rng R → (!x * !(inv fld x) = 1)%rng R.
  Proof.
  intros x H; simpl; rewrite mul_comm.
  apply mul_inv_l; assumption.
  Qed.

  Theorem add_compat_r : ∀ a b c,
    (!a = !b)%rng R
    → (!a + !c = !b + !c)%rng R.
  Proof.
  intros a b c Hab; simpl in Hab |- *.
  rewrite Hab; reflexivity.
  Qed.

  Theorem mul_compat_r : ∀ a b c,
    (!a = !b)%rng R
    → (!a * !c = !b * !c)%rng R.
  Proof.
  intros a b c Hab; simpl in Hab |- *.
  rewrite Hab; reflexivity.
  Qed.

  Theorem mul_add_distr_r : ∀ x y z,
    ((!x + !y) * !z = !x * !z + !y * !z)%rng R.
  Proof.
  intros x y z; simpl.
  rewrite mul_comm.
  rewrite mul_add_distr_l.
  rewrite mul_comm.
  assert (eq R (mul R z y) (mul R y z)) as H.
   apply mul_comm.

   rewrite H; reflexivity.
  Qed.

  Theorem add_0_r : ∀ a, (!a + 0 = !a)%rng R.
  Proof.
  intros a; simpl.
  rewrite add_comm.
  apply add_0_l.
  Qed.

  Theorem opp_0 : (- 0 = 0)%rng R.
  Proof.
  simpl; etransitivity; [ symmetry; apply add_0_l | idtac ].
  apply add_opp_r.
  Qed.

  Theorem add_reg_r : ∀ a b c, (!a + !c = !b + !c)%rng R → (!a = !b)%rng R.
  Proof.
  intros a b c Habc; simpl in Habc; simpl.
  apply add_compat_r with (c := (- !c)%rng R) in Habc.
  do 2 rewrite <- add_assoc in Habc.
  rewrite add_opp_r in Habc.
  do 2 rewrite add_0_r in Habc.
  assumption.
  Qed.

  Theorem add_reg_l : ∀ a b c, (!c + !a = !c + !b)%rng R → (!a = !b)%rng R.
  Proof.
  intros a b c Habc; simpl in Habc; simpl.
  apply add_reg_r with (c := c).
  rewrite add_comm; symmetry.
  rewrite add_comm; symmetry.
  assumption.
  Qed.

  Theorem add_sub : ∀ a b, (!a + !b - !b = !a)%rng R.
  Proof.
  intros a b; simpl.
  rewrite <- add_assoc.
  rewrite add_opp_r, add_0_r.
  reflexivity.
  Qed.

  Theorem mul_reg_r : ∀ a b c,
    (!c ≠ 0)%rng R
    → (!a * !c = !b * !c)%rng R
      → (!a = !b)%rng R.
  Proof.
  intros a b c Hc Habc; simpl in Hc, Habc; simpl.
  apply mul_compat_r with (c := inv fld c) in Habc.
  do 2 rewrite <- mul_assoc in Habc.
  rewrite mul_inv_r in Habc; [ idtac | assumption ].
  do 2 rewrite mul_1_r in Habc.
  assumption.
  Qed.

  Theorem mul_reg_l : ∀ a b c,
    (!c ≠ 0)%rng R
    → (!c * !a = !c * !b)%rng R
      → (!a = !b)%rng R.
  Proof.
  intros a b c Hc Habc; simpl in Hc, Habc; simpl.
  rewrite mul_comm in Habc; symmetry in Habc.
  rewrite mul_comm in Habc; symmetry in Habc.
  eapply mul_reg_r; eassumption.
  Qed.

  Theorem add_id_uniq : ∀ a b, (!a + !b = !a)%rng R → (!b = 0)%rng R.
  Proof.
  intros a b Hab; simpl in Hab; simpl.
  rewrite add_comm in Hab.
  apply add_reg_r with (c := a).
  rewrite add_0_l; assumption.
  Qed.

  Theorem mul_0_l : ∀ a, (0 * !a = 0)%rng R.
  Proof.
  intros a.
  assert ((0 * !a + !a = !a)%rng R) as H.
   transitivity ((0 * !a + 1 * !a)%rng R).
    rewrite mul_1_l; reflexivity.

    rewrite <- mul_add_distr_r.
    rewrite add_0_l, mul_1_l.
    reflexivity.

   apply add_reg_r with (c := a).
   rewrite add_0_l; assumption.
  Qed.

  Theorem mul_0_r : ∀ a, (!a * 0 = 0)%rng R.
  Proof.
  intros a; simpl.
  rewrite mul_comm, mul_0_l.
  reflexivity.
  Qed.

  Theorem mul_opp_l : ∀ a b, ((-!a) * !b = - (!a * !b))%rng R.
  Proof.
  intros a b; simpl.
  apply add_reg_l with (c := (!a * !b)%rng R).
  rewrite add_opp_r.
  rewrite <- mul_add_distr_r.
  rewrite add_opp_r, mul_0_l.
  reflexivity.
  Qed.

  Theorem mul_opp_r : ∀ a b, (!a * (- !b) = - (!a * !b))%rng R.
  Proof.
  intros a b; simpl.
  rewrite mul_comm; symmetry.
  rewrite mul_comm; symmetry.
  apply mul_opp_l.
  Qed.

  Theorem opp_add_distr : ∀ a b, (- (!a + !b) = - !a - !b)%rng R.
  Proof.
  intros a b.
  apply mul_reg_l with (c := 1%rng R).
   apply neq_1_0.

   rewrite mul_opp_r.
   rewrite <- mul_opp_l.
   rewrite mul_add_distr_l.
   do 2 rewrite mul_opp_l.
   do 3 rewrite mul_1_l.
   reflexivity.
  Qed.

  Theorem add_shuffle0 : ∀ n m p, (!n + !m + !p = !n + !p + !m)%rng R.
  Proof.
  intros n m p; simpl.
  do 2 rewrite <- add_assoc.
  assert (eq R (add R m p) (add R p m)) as H by apply add_comm.
  rewrite H; reflexivity.
  Qed.

  Theorem mul_shuffle0 : ∀ n m p,
    eq R (mul R (mul R n m) p) (mul R (mul R n p) m).
  Proof.
  intros n m p.
  do 2 rewrite <- mul_assoc.
  assert (eq R (mul R m p) (mul R p m)) as H by apply mul_comm.
  rewrite H; reflexivity.
  Qed.

  Theorem mul_eq_0 : ∀ n m,
    (n = 0)%rng ∨ (m = 0)%rng
    → (n * m = 0)%rng.
  Proof.
  intros n m H.
  destruct H as [H| H]; rewrite H; [ apply mul_0_l | apply mul_0_r ].
  Qed.

  Theorem eq_mul_0_l : ∀ n m,
    (n * m = 0)%rng
    → (m ≠ 0)%rng
      → (n = 0)%rng.
  Proof.
  intros n m Hnm Hm.
  rewrite <- mul_0_l with (a := m) in Hnm.
  apply mul_reg_r in Hnm; assumption.
  Qed.

  Theorem eq_mul_0_r : ∀ n m,
    (n * m = 0)%rng
    → (n ≠ 0)%rng
      → (m = 0)%rng.
  Proof.
  intros n m Hnm Hm.
  rewrite <- mul_0_r with (a := n) in Hnm.
  apply mul_reg_l in Hnm; assumption.
  Qed.

  (* AFAIK cannot be do with 'Add Parametric Morphim: (inv fld)
     because there is a condition 'a ≠ 0'; question: is is possible
     to do a conditional morphism? *)
  Theorem inv_compat : ∀ a b,
    (a ≠ 0)%rng
    → (a = b)%rng
      → (inv fld a = inv fld b)%rng.
  Proof.
  intros a b Ha Heq.
  remember Heq as Hab; clear HeqHab.
  apply mul_compat_l with (c := inv fld b) in Heq.
  unfold R in Heq.
  rewrite mul_inv_l in Heq.
   apply mul_compat_r with (c := inv fld a) in Heq.
   rewrite mul_1_l in Heq.
   rewrite <- mul_assoc in Heq.
   rewrite mul_inv_r in Heq; [ idtac | assumption ].
   rewrite mul_1_r in Heq.
   symmetry; assumption.

   intros H.
   rewrite H in Heq at 3.
   rewrite mul_0_r in Heq.
   rewrite H in Hab.
   contradiction.
  Qed.

End Make.
