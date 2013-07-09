(* $Id: Fpolynomial.v,v 1.4 2013-07-09 09:51:26 deraugla Exp $ *)

(* polynomials on a field *)

Require Import Utf8.
Require Import QArith.

Require Import Field.
Require Import Misc.
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

Lemma list_eq_comm : ∀ α (fld : field α) l₁ l₂,
  list_eq (fld_eq fld) l₁ l₂ = list_eq (fld_eq fld) l₂ l₁.
Proof.
intros α fld l₁ l₂.
revert l₂.
induction l₁ as [| x₁]; intros; simpl.
 destruct l₂ as [| x₂]; reflexivity.

 destruct l₂ as [| x₂]; [ reflexivity | simpl ].
 rewrite fld_eq_comm, IHl₁; reflexivity.
Qed.

Lemma list_eq_app_one_comm : ∀ α (fld : field α) x₁ x₂ l₁ l₂,
  list_eq (fld_eq fld) (l₁ ++ [x₁]) (l₂ ++ [x₂]) =
  list_eq (fld_eq fld) [x₁ … l₁] [x₂ … l₂].
Proof.
intros α fld x₁ x₂ l₁ l₂.
simpl.
revert x₁ x₂ l₂.
induction l₁ as [| x₃]; intros.
 simpl.
 destruct l₂ as [| x₄]; simpl.
  reflexivity.

  destruct l₂ as [| x₅]; simpl.
   do 2 rewrite andb_false_r; reflexivity.

   do 2 rewrite andb_false_r; reflexivity.

 simpl.
 destruct l₂ as [| x₄]; simpl.
  rewrite andb_false_r.
  rewrite andb_comm.
  destruct l₁; reflexivity.

  rewrite IHl₁.
  do 2 rewrite andb_assoc; f_equal.
  apply andb_comm.
Qed.

(* addition commutativity *)

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

(* addition associativity *)

Lemma zzz : ∀ α (fld : field α) an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂,
  rp₁ = pol_add_loop (add fld)
          (an (pol_add_loop (add fld) an₁ an₂ al₁ al₂)) an₃
          (al (pol_add_loop (add fld) an₁ an₂ al₁ al₂)) al₃
  → rp₂ = pol_add_loop (add fld)
           an₁ (an (pol_add_loop (add fld) an₂ an₃ al₂ al₃))
           al₁ (al (pol_add_loop (add fld) an₂ an₃ al₂ al₃))
    → list_eq (fld_eq fld) (al rp₁) (al rp₂) = true.
Proof.
intros α fld an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
revert an₁ an₂ an₃ al₁ al₃ rp₁ rp₂ H₁ H₂.
induction al₂ as [| a₂]; intros.
 simpl in H₂.
 destruct al₃ as [| a₃]; simpl in H₁, H₂.
  eapply pol_add_loop_comm in H₂; [ idtac | reflexivity ].
  simpl in H₂.
  destruct al₁ as [| a₁]; simpl in H₁, H₂.
   subst rp₁; simpl.
   assumption.

   subst rp₁; simpl.
   destruct (al rp₂) as [| a₂ al₂]; [ discriminate H₂ | idtac ].
   rewrite <- H₂.
   f_equal.
bbb.

Lemma poly_add_assoc : ∀ α (fld : field α) pol₁ pol₂ pol₃,
  poly_eq fld
    (poly_add fld (poly_add fld pol₁ pol₂) pol₃)
    (poly_add fld pol₁ (poly_add fld pol₂ pol₃)) = true.
Proof.
intros α fld pol₁ pol₂ pol₃.
unfold poly_eq.
rewrite list_eq_append_one.
apply andb_true_intro.
split.
bbb.
