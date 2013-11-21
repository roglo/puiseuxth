(* $Id: Field.v,v 2.16 2013-11-21 05:14:01 deraugla Exp $ *)

Require Import Utf8.
Require Import Ring_theory.
Require Import Field_theory.
Require Import Setoid.

Set Implicit Arguments.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    mul : α → α → α;
    opp : α → α;
    inv : α → α;
    fld_eq : α → α → Prop;
    fld_eq_refl : ∀ a, fld_eq a a;
    fld_eq_sym : ∀ a b, fld_eq a b → fld_eq b a;
    fld_eq_trans : ∀ a b c, fld_eq a b → fld_eq b c → fld_eq a c;
    fld_1_neq_0 : not (fld_eq one zero);
    fld_add_comm : ∀ a b, fld_eq (add a b) (add b a);
    fld_add_assoc : ∀ a b c, fld_eq (add a (add b c)) (add (add a b) c);
    fld_add_0_l : ∀ a, fld_eq (add zero a) a;
    fld_add_opp_diag_r : ∀ a, fld_eq (add a (opp a)) zero;
    fld_add_compat_r : ∀ a b c, fld_eq a b → fld_eq (add a c) (add b c);
    fld_mul_comm : ∀ a b, fld_eq (mul a b) (mul b a);
    fld_mul_assoc : ∀ a b c, fld_eq (mul a (mul b c)) (mul (mul a b) c);
    fld_mul_1_l : ∀ a, fld_eq (mul one a) a;
    fld_mul_compat_r : ∀ a b c, fld_eq a b → fld_eq (mul a c) (mul b c);
    fld_mul_inv : ∀ a, not (fld_eq a zero) → fld_eq (mul (inv a) a) one;
    fld_mul_add_distr_l : ∀ a b c,
      fld_eq (mul a (add b c)) (add (mul a b) (mul a c)) }.

Add Parametric Relation α (fld : field α) : α (fld_eq fld)
 reflexivity proved by (fld_eq_refl fld)
 symmetry proved by (fld_eq_sym fld)
 transitivity proved by (fld_eq_trans fld)
 as fld_eq_rel.

Add Parametric Morphism α (fld : field α) : (add fld) with 
signature fld_eq fld ==> fld_eq fld ==> fld_eq fld
  as fld_add_morph.
Proof.
intros a b Hab c d Hcd.
rewrite fld_add_compat_r; [ idtac | eassumption ].
rewrite fld_add_comm; symmetry.
rewrite fld_add_comm; symmetry.
rewrite fld_add_compat_r; [ reflexivity | eassumption ].
Qed.

Add Parametric Morphism α (fld : field α) : (mul fld) with 
signature fld_eq fld ==> fld_eq fld ==> fld_eq fld
  as fld_mul_morph.
Proof.
intros a b Hab c d Hcd.
rewrite fld_mul_compat_r; [ idtac | eassumption ].
rewrite fld_mul_comm; symmetry.
rewrite fld_mul_comm; symmetry.
rewrite fld_mul_compat_r; [ reflexivity | eassumption ].
Qed.

Section fld.

Variable α : Type.
Variable fld : field α.
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).

Delimit Scope fld_scope with fld.
Notation "0" := (zero fld).
Notation "- a" := (opp fld a) : fld_scope.
Notation "a + b" := (add fld a b)
  (left associativity, at level 50) : fld_scope.
Notation "a - b" := (add fld a (opp fld b))
  (left associativity, at level 50) : fld_scope.
Notation "a * b" := (mul fld a b)
  (left associativity, at level 40) : fld_scope.

Theorem fld_mul_add_distr_r : ∀ x y z,
 ((x + y) * z)%fld ≍ (x * z + y * z)%fld.
Proof.
intros x y z.
rewrite fld_mul_comm.
rewrite fld_mul_add_distr_l.
rewrite fld_mul_comm.
assert (fld_eq fld (mul fld z y) (mul fld y z)) as H.
 apply fld_mul_comm.

 rewrite H; reflexivity.
Qed.

Lemma fld_ring :
  @ring_theory α (zero fld) (one fld) (add fld) (mul fld)
    (λ x y, add fld x (opp fld y)) (opp fld) (fld_eq fld).
Proof.
constructor.
 apply fld_add_0_l.

 apply fld_add_comm.

 apply fld_add_assoc.

 apply fld_mul_1_l.

 apply fld_mul_comm.

 apply fld_mul_assoc.

 apply fld_mul_add_distr_r.

 reflexivity.

 apply fld_add_opp_diag_r.
Qed.

(* comment ça marche, ce truc-là ? et à quoi ça sert ?

Lemma fld_ring_morph :
  @ring_morph α (zero fld) (one fld) (add fld) (mul fld)
    (λ x y, add fld x (opp fld y)) (opp fld) (fld_eq fld).

(R : Type) (rO rI : R) (radd rmul rsub : R → R → R)
(ropp : R → R) (req : R → R → Prop) (C : Type) (cO cI : C)
(cadd cmul csub : C → C → C) (copp : C → C) (ceqb : C → C → bool)
(phi : C → R) : Prop := mkmorph

Add Ring fld_ring : fld_ring (morphism glop).
bbb.
*)

Definition fld_field :=
  {| F_R := fld_ring;
     F_1_neq_0 := fld_1_neq_0 fld;
     Fdiv_def x y := fld_eq_refl fld (mul fld x (inv fld y));
     Finv_l := fld_mul_inv fld |}.

(* *)

Theorem fld_add_0_r : ∀ a, (a + 0 ≍ a)%fld.
Proof.
intros a.
rewrite fld_add_comm.
apply fld_add_0_l.
Qed.

Theorem fld_opp_0 : (- 0 ≍ 0)%fld.
Proof.
etransitivity; [ symmetry; apply fld_add_0_l | idtac ].
apply fld_add_opp_diag_r.
Qed.

(*
Theorem add_cancel_l : ∀ a b c, (c + a ≍ c + b ↔ a ≍ b)%fld.
Proof.
bbb.

Theorem add_cancel_r : ∀ a b c, (a + c ≍ b + c ↔ a ≍ b)%fld.
Proof.
bbb.

Theorem sub_cancel_r : ∀ a b c, (a - c = b - c ↔ a = b)%fld.
Proof.
bbb.

Theorem add_move_l : ∀ a b c, a + b = c ↔ a = c - b.
Proof.
bbb.

Theorem add_move_0_r : ∀ a b, a + b = 0 ↔ a = -b.
Proof.
bbb.
*)

Theorem fld_mul_opp_l : ∀ a b, (- a * b ≍ - (a * b))%fld.
Proof.
intros a b.
bbb.

Theorem fld_mul_0_l : ∀ a, (0 * a ≍ 0)%fld.
Proof.
intros a.
assert (0 ≍ 0 - 0)%fld as H.
 symmetry.
 apply fld_add_opp_diag_r.

 rewrite H in |- * at 1.
 rewrite fld_mul_add_distr_r.
 rewrite fld_mul_opp_l.
 rewrite fld_add_opp_diag_r.
 reflexivity.
qed.

Theorem fld_add_shuffle0 : ∀ n m p,
  fld_eq fld (add fld (add fld n m) p) (add fld (add fld n p) m).
Proof.
intros n m p.
do 2 rewrite <- fld_add_assoc.
assert (fld_eq fld (add fld m p) (add fld p m)) as H by apply fld_add_comm.
rewrite H; reflexivity.
Qed.

Theorem fld_mul_shuffle0 : ∀ n m p,
  fld_eq fld (mul fld (mul fld n m) p) (mul fld (mul fld n p) m).
Proof.
intros n m p.
do 2 rewrite <- fld_mul_assoc.
assert (fld_eq fld (mul fld m p) (mul fld p m)) as H by apply fld_mul_comm.
rewrite H; reflexivity.
Qed.

End fld.
