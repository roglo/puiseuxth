(* $Id: Fpolynomial.v,v 1.1 2013-07-08 21:09:18 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Require Import Field.
Require Import Polynomial.

Set Implicit Arguments.

Fixpoint list_eq α (cmp : α → α → bool) l₁ l₂ :=
  match l₁ with
  | [] =>
      match l₂ with
      | [] => true
      | [x₂ … ll₂] => false
      end
  | [x₁ … ll₁] =>
      match l₂ with
      | [] => false
      | [x₂ … ll₂] => cmp x₁ x₂ && list_eq cmp ll₁ ll₂
      end
  end.

Definition poly_eq α fld (x y : polynomial α) :=
  list_eq (fld_eq fld) (al x ++ [an x]) (al y ++ [an y]).

Definition poly_add α (fld : field α) :=
  pol_add (add fld).

Definition poly_mul α (fld : field α) :=
  pol_mul (zero fld) (add fld) (mul fld).

Definition Pdivide α fld (x y : polynomial α) :=
  ∃ z, poly_eq fld y (poly_mul fld z x) = true.

(* commutativity polynomial addition *)

Lemma list_eq_append_one : ∀ α cmp (x₁ x₂ : α) l₁ l₂,
  list_eq cmp (l₁ ++ [x₁]) (l₂ ++ [x₂]) = list_eq cmp l₁ l₂ && cmp x₁ x₂.
Proof.
intros α cmp x₁ x₂ l₁ l₂.
revert x₁ x₂ l₂.
induction l₁ as [| x₃]; intros; simpl.
 destruct l₂ as [| x₄]; simpl.
  apply andb_true_r.

  destruct l₂ as [| x₅]; simpl; apply andb_false_r.

 destruct l₂ as [| x₄]; simpl.
  destruct l₁ as [| x₅]; simpl; apply andb_false_r.

  rewrite <- andb_assoc.
  f_equal.
  apply IHl₁.
Qed.

Lemma pol_add_loop_comm : ∀ α (fld : field α) an₁ an₂ al₁ al₂ rp₁ rp₂,
  rp₁ = pol_add_loop (add fld) an₁ an₂ al₁ al₂
  → rp₂ = pol_add_loop (add fld) an₂ an₁ al₂ al₁
    → list_eq (fld_eq fld) (al rp₁) (al rp₂) = true.
Proof.
intros α fld an₁ an₂ al₁ al₂ rp₁ rp₂ H₁ H₂.
revert al₂ rp₁ rp₂ H₁ H₂.
induction al₁ as [| a₁]; intros.
 simpl in H₁.
 destruct al₂ as [| a₂].
  simpl in H₂.
  subst rp₁ rp₂; reflexivity.

  simpl in H₂.
  subst rp₁ rp₂; simpl.
  rewrite (add_comm fld); simpl.
  clear a₂.
  induction al₂ as [| a₂]; [ reflexivity | simpl ].
  rewrite fld_eq_refl.
  assumption.

 simpl in H₁.
 destruct al₂ as [| a₂].
  simpl in H₂.
  subst rp₁ rp₂; simpl.
  rewrite add_comm; simpl.
  clear a₁ IHal₁.
  induction al₁ as [| a₁]; [ reflexivity | simpl ].
  rewrite fld_eq_refl; assumption.

  simpl in H₂.
  rewrite H₁, H₂; simpl.
  rewrite add_comm; simpl.
  eapply IHal₁; reflexivity.
Qed.

Lemma fld_eq_an : ∀ α (fld : field α) an₁ an₂ al₁ al₂ rp₁ rp₂,
  rp₁ = pol_add_loop (add fld) an₁ an₂ al₁ al₂
  → rp₂ = pol_add_loop (add fld) an₂ an₁ al₂ al₁
    → fld_eq fld (an rp₁) (an rp₂) = true.
Proof.
intros α fld an₁ an₂ al₁ al₂ rp₁ rp₂ H₁ H₂.
revert an₁ an₂ al₂ rp₁ rp₂ H₁ H₂.
induction al₁ as [| a₁]; intros.
 simpl in H₁.
 destruct al₂ as [| a₂].
  simpl in H₂.
  subst rp₁ rp₂; simpl.
  apply add_comm.

  simpl in H₂.
  subst rp₁ rp₂; simpl.
  apply fld_eq_refl.

 simpl in H₁.
 destruct al₂ as [| a₂].
  simpl in H₂.
  subst rp₁ rp₂; simpl.
  apply fld_eq_refl.

  simpl in H₁, H₂.
  rewrite H₁, H₂; simpl.
  eapply IHal₁; reflexivity.
Qed.

Lemma poly_add_comm : ∀ α (fld : field α) pol₁ pol₂,
  poly_eq fld (poly_add fld pol₁ pol₂) (poly_add fld pol₂ pol₁) = true.
Proof.
intros α fld pol₁ pol₂.
unfold poly_eq.
rewrite list_eq_append_one.
apply andb_true_intro.
split.
 eapply pol_add_loop_comm; reflexivity.

 eapply fld_eq_an; reflexivity.
Qed.
