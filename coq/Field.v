(* Field.v *)

Require Import Utf8.
Require Import Setoid.

Set Implicit Arguments.

Reserved Notation "a .= x b" (at level 70, x at level 0).
Reserved Notation "a .≠ x b" (at level 70, x at level 0).
Reserved Notation "a .+ x b" (left associativity, at level 50, x at level 0).
Reserved Notation "a .- x b" (left associativity, at level 50, x at level 0).
Reserved Notation "a .* x b" (left associativity, at level 40, x at level 0).
Reserved Notation "a ./ x b" (left associativity, at level 40, x at level 0).
Reserved Notation ".- x a" (at level 35, x at level 0).
Reserved Notation "a .∘ x b" (left associativity, at level 32, x at level 0).
Reserved Notation "a .^ x b" (at level 30, x at level 0).
Reserved Notation ".¹/ x a" (at level 1, x at level 0).
Reserved Notation ".0 x" (at level 0, x at level 0).
Reserved Notation ".1 x" (at level 0, x at level 0).

Reserved Notation "¹/ a" (at level 1).
Reserved Notation "! x" (at level 1).

Reserved Notation "a ∘ b" (left associativity, at level 32).

Class field α :=
  { fld_zero : α;
    fld_one : α;
    fld_add : α → α → α;
    fld_mul : α → α → α;
    fld_opp : α → α;
    fld_eq : α → α → Prop;
    fld_eq_refl : ∀ a, fld_eq a a;
    fld_eq_sym : ∀ a b, fld_eq a b → fld_eq b a;
    fld_eq_trans : ∀ a b c, fld_eq a b → fld_eq b c → fld_eq a c;
    fld_add_comm : ∀ a b, fld_eq (fld_add a b) (fld_add b a);
    fld_add_assoc : ∀ a b c,
      fld_eq (fld_add a (fld_add b c)) (fld_add (fld_add a b) c);
    fld_add_0_l : ∀ a, fld_eq (fld_add fld_zero a) a;
    fld_add_opp_l : ∀ a, fld_eq (fld_add (fld_opp a) a) fld_zero;
    fld_add_compat_l : ∀ a b c,
      fld_eq a b → fld_eq (fld_add c a) (fld_add c b);
    fld_mul_comm : ∀ a b, fld_eq (fld_mul a b) (fld_mul b a);
    fld_mul_assoc : ∀ a b c,
      fld_eq (fld_mul a (fld_mul b c)) (fld_mul (fld_mul a b) c);
    fld_mul_1_l : ∀ a, fld_eq (fld_mul fld_one a) a;
    fld_mul_compat_l : ∀ a b c,
      fld_eq a b → fld_eq (fld_mul c a) (fld_mul c b);
    fld_mul_add_distr_l : ∀ a b c,
      fld_eq (fld_mul a (fld_add b c))
        (fld_add (fld_mul a b) (fld_mul a c));
    fld_inv : α → α;
    fld_mul_inv_l : ∀ a,
      not (fld_eq a fld_zero)
      → fld_eq (fld_mul (fld_inv a) a) fld_one }.

Delimit Scope field_scope with K.
Notation "a = b" := (fld_eq a b) : field_scope.
Notation "a ≠ b" := (¬ fld_eq a b) : field_scope.
Notation "a + b" := (fld_add a b) : field_scope.
Notation "a - b" := (fld_add a (fld_opp b)) : field_scope.
Notation "a * b" := (fld_mul a b) : field_scope.
Notation "- a" := (fld_opp a) : field_scope.
Notation "¹/ a" := (fld_inv a) : field_scope.
Notation "0" := fld_zero : field_scope.
Notation "1" := fld_one : field_scope.

(*
Notation "a = b" := (λ f, fld_eq f a b) : field_scope.
Notation "a ≠ b" := (λ f, ¬ fld_eq f a b) : field_scope.
Notation "a + b" := (λ f, fld_add f a b) : field_scope.
Notation "a - b" := (λ f, fld_add f a (fld_opp f b)) : field_scope.
Notation "a * b" := (λ f, fld_mul f a b) : field_scope.
Notation "- a" := (λ f, fld_opp f a) : field_scope.
Notation "¹/ a" := (λ f, fld_inv f a) : field_scope.
Notation "0" := (λ f, fld_zero f) : field_scope.
Notation "1" := (λ f, fld_one f) : field_scope.
*)
(*
Notation "! x" := (λ _, x) : field_scope.
*)

Add Parametric Relation α (K : field α) : α fld_eq
 reflexivity proved by fld_eq_refl
 symmetry proved by fld_eq_sym
 transitivity proved by fld_eq_trans
 as eq_rel.

Add Parametric Morphism α (K : field α) : fld_add
  with signature fld_eq ==> fld_eq ==> fld_eq
  as add_morph.
Proof.
intros a b Hab c d Hcd.
rewrite fld_add_comm; symmetry.
rewrite fld_add_comm; symmetry.
rewrite fld_add_compat_l; [ idtac | eassumption ].
rewrite fld_add_comm; symmetry.
rewrite fld_add_comm; symmetry.
rewrite fld_add_compat_l; [ reflexivity | eassumption ].
Qed.

Add Parametric Morphism α (K : field α) : fld_opp
  with signature fld_eq ==> fld_eq
  as opp_morph.
Proof.
intros a b Heq.
apply fld_add_compat_l with (c := fld_opp b) in Heq.
rewrite fld_add_opp_l in Heq.
rewrite fld_add_comm in Heq.
apply fld_add_compat_l with (c := fld_opp a) in Heq.
rewrite fld_add_assoc in Heq.
rewrite fld_add_opp_l in Heq.
rewrite fld_add_0_l in Heq.
symmetry in Heq.
rewrite fld_add_comm in Heq.
rewrite fld_add_0_l in Heq.
assumption.
Qed.

Add Parametric Morphism α (F : field α) : fld_mul
  with signature fld_eq ==> fld_eq ==> fld_eq
  as mul_morph.
Proof.
intros a b Hab c d Hcd.
rewrite fld_mul_comm; symmetry.
rewrite fld_mul_comm; symmetry.
rewrite fld_mul_compat_l; [ idtac | eassumption ].
rewrite fld_mul_comm; symmetry.
rewrite fld_mul_comm; symmetry.
rewrite fld_mul_compat_l; [ reflexivity | eassumption ].
Qed.

Section misc_theorems.

Variable α : Type.
Variable f : field α.

Theorem fld_add_opp_r : ∀ x, (x - x = 0)%K.
Proof.
intros x; simpl; rewrite fld_add_comm.
apply fld_add_opp_l.
Qed.

Theorem fld_mul_1_r : ∀ a, (a * 1 = a)%K.
Proof.
intros a; simpl.
rewrite fld_mul_comm, fld_mul_1_l.
reflexivity.
Qed.

Theorem fld_mul_inv_r : ∀ x, (x ≠ 0)%K → (x * ¹/ x = 1)%K.
Proof.
intros x H; simpl; rewrite fld_mul_comm.
apply fld_mul_inv_l; assumption.
Qed.

Theorem fld_add_compat_r : ∀ a b c,
  (a = b)%K
  → (a + c = b + c)%K.
Proof.
intros a b c Hab.
rewrite Hab; reflexivity.
Qed.

Theorem fld_add_compat : ∀ a b c d,
  (a = b)%K
  → (c = d)%K
    → (a + c = b + d)%K.
Proof.
intros a b c d Hab Hcd.
rewrite Hab, Hcd; reflexivity.
Qed.

Theorem fld_mul_compat_r : ∀ a b c,
  (a = b)%K
  → (a * c = b * c)%K.
Proof.
intros a b c Hab; simpl in Hab |- *.
rewrite Hab; reflexivity.
Qed.

Theorem fld_mul_compat : ∀ a b c d,
  (a = b)%K
  → (c = d)%K
    → (a * c = b * d)%K.
Proof.
intros a b c d Hab Hcd.
rewrite Hab, Hcd; reflexivity.
Qed.

Theorem fld_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%K.
Proof.
intros x y z; simpl.
rewrite fld_mul_comm.
rewrite fld_mul_add_distr_l.
rewrite fld_mul_comm.
assert (fld_eq (fld_mul z y) (fld_mul y z)) as H.
 apply fld_mul_comm.

 rewrite H; reflexivity.
Qed.

Theorem fld_add_0_r : ∀ a, (a + 0 = a)%K.
Proof.
intros a; simpl.
rewrite fld_add_comm.
apply fld_add_0_l.
Qed.

Theorem fld_opp_0 : (- 0 = 0)%K.
Proof.
simpl; etransitivity; [ symmetry; apply fld_add_0_l | idtac ].
apply fld_add_opp_r.
Qed.

Theorem fld_add_reg_r : ∀ a b c, (a + c = b + c)%K → (a = b)%K.
Proof.
intros a b c Habc; simpl in Habc; simpl.
apply fld_add_compat_r with (c := (- c)%K) in Habc.
do 2 rewrite <- fld_add_assoc in Habc.
rewrite fld_add_opp_r in Habc.
do 2 rewrite fld_add_0_r in Habc.
assumption.
Qed.

Theorem fld_add_reg_l : ∀ a b c, (c + a = c + b)%K → (a = b)%K.
Proof.
intros a b c Habc; simpl in Habc; simpl.
apply fld_add_reg_r with (c := c).
rewrite fld_add_comm; symmetry.
rewrite fld_add_comm; symmetry.
assumption.
Qed.

Theorem fld_add_sub : ∀ a b, (a + b - b = a)%K.
Proof.
intros a b; simpl.
rewrite <- fld_add_assoc.
rewrite fld_add_opp_r, fld_add_0_r.
reflexivity.
Qed.

Theorem fld_mul_reg_r : ∀ a b c,
  (c ≠ 0)%K
  → (a * c = b * c)%K
    → (a = b)%K.
Proof.
intros a b c Hc Habc; simpl in Hc, Habc; simpl.
apply fld_mul_compat_r with (c := (¹/ c)%K) in Habc.
do 2 rewrite <- fld_mul_assoc in Habc.
rewrite fld_mul_inv_r in Habc; [ idtac | assumption ].
do 2 rewrite fld_mul_1_r in Habc.
assumption.
Qed.

Theorem fld_mul_reg_l : ∀ a b c,
  (c ≠ 0)%K
  → (c * a = c * b)%K
    → (a = b)%K.
Proof.
intros a b c Hc Habc; simpl in Hc, Habc; simpl.
rewrite fld_mul_comm in Habc; symmetry in Habc.
rewrite fld_mul_comm in Habc; symmetry in Habc.
eapply fld_mul_reg_r; eassumption.
Qed.

Theorem fld_add_id_uniq : ∀ a b, (a + b = a)%K → (b = 0)%K.
Proof.
intros a b Hab; simpl in Hab; simpl.
rewrite fld_add_comm in Hab.
apply fld_add_reg_r with (c := a).
rewrite fld_add_0_l; assumption.
Qed.

Theorem fld_mul_0_l : ∀ a, (0 * a = 0)%K.
Proof.
intros a.
assert ((0 * a + a = a)%K) as H.
 transitivity ((0 * a + 1 * a)%K).
  rewrite fld_mul_1_l; reflexivity.

  rewrite <- fld_mul_add_distr_r.
  rewrite fld_add_0_l, fld_mul_1_l.
  reflexivity.

 apply fld_add_reg_r with (c := a).
 rewrite fld_add_0_l; assumption.
Qed.

Theorem fld_mul_0_r : ∀ a, (a * 0 = 0)%K.
Proof.
intros a; simpl.
rewrite fld_mul_comm, fld_mul_0_l.
reflexivity.
Qed.

Theorem fld_mul_opp_l : ∀ a b, ((- a) * b = - (a * b))%K.
Proof.
intros a b; simpl.
apply fld_add_reg_l with (c := (a * b)%K).
rewrite fld_add_opp_r.
rewrite <- fld_mul_add_distr_r.
rewrite fld_add_opp_r, fld_mul_0_l.
reflexivity.
Qed.

Theorem fld_mul_opp_r : ∀ a b, (a * (- b) = - (a * b))%K.
Proof.
intros a b; simpl.
rewrite fld_mul_comm; symmetry.
rewrite fld_mul_comm; symmetry.
apply fld_mul_opp_l.
Qed.

Theorem fld_add_move_0_r : ∀ a b, (a + b = 0)%K ↔ (a = - b)%K.
Proof.
intros a b.
split; intros H.
 apply fld_add_compat_r with (c := (- b)%K) in H.
 rewrite <- fld_add_assoc in H.
 rewrite fld_add_opp_r in H.
 rewrite fld_add_0_r, fld_add_0_l in H; assumption.

 rewrite H.
 rewrite fld_add_opp_l; reflexivity.
Qed.

Theorem fld_mul_opp_1_l : ∀ a, (- (1) * a = - a)%K.
Proof.
intros a.
apply fld_add_reg_r with (c := (1 * a)%K).
rewrite <- fld_mul_add_distr_r.
rewrite fld_add_opp_l, fld_mul_0_l.
symmetry.
apply fld_add_move_0_r.
rewrite fld_mul_1_l; reflexivity.
Qed.

Theorem fld_opp_add_distr : ∀ a b, (- (a + b) = - a - b)%K.
Proof.
intros a b.
rewrite <- fld_mul_opp_1_l.
rewrite fld_mul_add_distr_l.
do 2 rewrite fld_mul_opp_1_l.
reflexivity.
Qed.

Theorem fld_add_shuffle0 : ∀ n m p, (n + m + p = n + p + m)%K.
Proof.
intros n m p; simpl.
do 2 rewrite <- fld_add_assoc.
assert (m + p = p + m)%K as H by apply fld_add_comm.
rewrite H; reflexivity.
Qed.

Theorem fld_mul_shuffle0 : ∀ n m p, (n * m * p = n * p * m)%K.
Proof.
intros n m p.
do 2 rewrite <- fld_mul_assoc.
assert (m * p = p * m)%K as H by apply fld_mul_comm.
rewrite H; reflexivity.
Qed.

Theorem fld_mul_eq_0 : ∀ n m,
  (n = 0)%K ∨ (m = 0)%K
  → (n * m = 0)%K.
Proof.
intros n m H; simpl in H; simpl.
destruct H as [H| H]; rewrite H; [ apply fld_mul_0_l | apply fld_mul_0_r ].
Qed.

Theorem fld_eq_mul_0_l : ∀ n m,
  (n * m = 0)%K
  → (m ≠ 0)%K
    → (n = 0)%K.
Proof.
intros n m Hnm Hm.
rewrite <- fld_mul_0_l with (a := m) in Hnm.
apply fld_mul_reg_r in Hnm; assumption.
Qed.

Theorem fld_eq_mul_0_r : ∀ n m,
  (n * m = 0)%K
  → (n ≠ 0)%K
    → (m = 0)%K.
Proof.
intros n m Hnm Hm; simpl in Hnm, Hm; simpl.
rewrite <- fld_mul_0_r with (a := n) in Hnm.
apply fld_mul_reg_l in Hnm; assumption.
Qed.

(* AFAIK cannot be do with 'Add Parametric Morphim: (inv fld)
   because there is a condition 'a ≠ 0'; question: is is possible
   to do a conditional morphism? *)
Theorem fld_inv_compat : ∀ a b,
  (a ≠ 0)%K
  → (a = b)%K
    → (¹/ a = ¹/ b)%K.
Proof.
intros a b Ha Heq.
remember Heq as Hab; clear HeqHab.
apply fld_mul_compat_l with (c := ¹/ b%K) in Heq.
rewrite fld_mul_inv_l in Heq.
 apply fld_mul_compat_r with (c := ¹/ a%K) in Heq.
 rewrite fld_mul_1_l in Heq.
 rewrite <- fld_mul_assoc in Heq.
 rewrite fld_mul_inv_r in Heq; [ idtac | assumption ].
 rewrite fld_mul_1_r in Heq.
 symmetry; assumption.

 intros H.
 rewrite H in Heq at 3.
 rewrite fld_mul_0_r in Heq.
 rewrite H in Hab.
 contradiction.
Qed.

End misc_theorems.
