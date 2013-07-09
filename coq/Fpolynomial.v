(* $Id: Fpolynomial.v,v 1.15 2013-07-09 20:16:39 deraugla Exp $ *)

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

Lemma list_eq_refl : ∀ α (fld : field α) l,
  list_eq (fld_eq fld) l l = true.
Proof.
intros α fld l.
induction l as [| x]; [ reflexivity | simpl ].
apply andb_true_iff.
split; [ apply fld_eq_refl | assumption ].
Qed.

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

(* addition commutativity *)

Lemma pol_add_loop_al_comm : ∀ α (fld : field α) an₁ an₂ al₁ al₂ rp₁ rp₂,
  rp₁ = pol_add_loop (add fld) an₁ an₂ al₁ al₂
  → rp₂ = pol_add_loop (add fld) an₂ an₁ al₂ al₁
    → list_eq (fld_eq fld) (al rp₁) (al rp₂) = true.
Proof.
intros α fld an₁ an₂ al₁ al₂ rp₁ rp₂ H₁ H₂.
revert al₂ rp₁ rp₂ H₁ H₂.
induction al₁ as [| a₁]; intros.
 simpl in H₁.
 destruct al₂ as [| a₂].
  subst rp₁ rp₂; reflexivity.

  subst rp₁ rp₂; simpl.
  rewrite fld_add_comm; simpl.
  clear a₂.
  induction al₂ as [| a₂]; [ reflexivity | simpl ].
  rewrite fld_eq_refl.
  assumption.

 simpl in H₁.
 destruct al₂ as [| a₂].
  subst rp₁ rp₂; simpl.
  rewrite fld_add_comm; simpl.
  clear a₁ IHal₁.
  induction al₁ as [| a₁]; [ reflexivity | simpl ].
  rewrite fld_eq_refl; assumption.

  rewrite H₁, H₂; simpl.
  rewrite fld_add_comm; simpl.
  eapply IHal₁; reflexivity.
Qed.

Lemma pol_add_loop_an_comm : ∀ α (fld : field α) an₁ an₂ al₁ al₂ rp₁ rp₂,
  rp₁ = pol_add_loop (add fld) an₁ an₂ al₁ al₂
  → rp₂ = pol_add_loop (add fld) an₂ an₁ al₂ al₁
    → fld_eq fld (an rp₁) (an rp₂) = true.
Proof.
intros α fld an₁ an₂ al₁ al₂ rp₁ rp₂ H₁ H₂.
revert an₁ an₂ al₂ rp₁ rp₂ H₁ H₂.
induction al₁ as [| a₁]; intros.
 simpl in H₁.
 destruct al₂ as [| a₂].
  subst rp₁ rp₂; simpl.
  apply fld_add_comm.

  subst rp₁ rp₂; simpl.
  apply fld_eq_refl.

 simpl in H₁.
 destruct al₂ as [| a₂].
  subst rp₁ rp₂; simpl.
  apply fld_eq_refl.

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
 eapply pol_add_loop_al_comm; reflexivity.

 eapply pol_add_loop_an_comm; reflexivity.
Qed.

(* addition associativity *)

Lemma pol_add_loop_al_assoc :
    ∀ α (fld : field α) an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂,
  rp₁ = pol_add_loop (add fld)
          (an (pol_add_loop (add fld) an₁ an₂ al₁ al₂)) an₃
          (al (pol_add_loop (add fld) an₁ an₂ al₁ al₂)) al₃
  → rp₂ = pol_add_loop (add fld)
           an₁ (an (pol_add_loop (add fld) an₂ an₃ al₂ al₃))
           al₁ (al (pol_add_loop (add fld) an₂ an₃ al₂ al₃))
    → list_eq (fld_eq fld) (al rp₁) (al rp₂) = true.
Proof.
intros α fld an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
revert an₁ an₂ an₃ al₂ al₃ rp₁ rp₂ H₁ H₂.
induction al₁ as [| a₁]; intros.
 simpl in H₁, H₂.
 destruct al₂ as [| a₂]; simpl in H₁.
  destruct al₃ as [| a₃]; simpl in H₁.
   subst rp₁ rp₂; simpl.
   reflexivity.

   subst rp₁ rp₂; simpl.
   apply andb_true_iff.
   split; [ apply fld_add_assoc | apply list_eq_refl ].

  destruct al₃ as [| a₃]; simpl in H₁.
   subst rp₁ rp₂; simpl.
   apply andb_true_iff.
   split; [ apply fld_add_assoc | apply list_eq_refl ].

   subst rp₁ rp₂; simpl.
   apply andb_true_iff.
   split; [ apply fld_add_assoc | apply list_eq_refl ].

 simpl in H₁.
 destruct al₂ as [| a₂]; simpl in H₁.
  destruct al₃ as [| a₃]; simpl in H₁.
   subst rp₁ rp₂; simpl.
   apply andb_true_iff.
   split; [ apply fld_add_assoc | apply list_eq_refl ].

   subst rp₁ rp₂; simpl.
   apply andb_true_iff.
   split; [ apply fld_add_assoc | apply list_eq_refl ].

  destruct al₃ as [| a₃]; simpl in H₁.
   subst rp₁ rp₂; simpl.
   apply andb_true_iff.
   split; [ apply fld_add_assoc | apply list_eq_refl ].

   subst rp₁ rp₂; simpl.
   apply andb_true_iff.
   split; [ apply fld_add_assoc | eapply IHal₁; reflexivity ].
Qed.

Lemma pol_add_loop_an_assoc :
    ∀ α (fld : field α) an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂,
  rp₁ = pol_add_loop (add fld)
          (an (pol_add_loop (add fld) an₁ an₂ al₁ al₂)) an₃
          (al (pol_add_loop (add fld) an₁ an₂ al₁ al₂)) al₃
  → rp₂ = pol_add_loop (add fld)
           an₁ (an (pol_add_loop (add fld) an₂ an₃ al₂ al₃))
           al₁ (al (pol_add_loop (add fld) an₂ an₃ al₂ al₃))
    → fld_eq fld (an rp₁) (an rp₂) = true.
Proof.
intros α fld an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
revert an₁ an₂ an₃ al₂ al₃ rp₁ rp₂ H₁ H₂.
induction al₁ as [| a₁]; intros.
 simpl in H₁, H₂.
 destruct al₂ as [| a₂]; simpl in H₁.
  destruct al₃ as [| a₃]; simpl in H₁.
   subst rp₁ rp₂; simpl.
   apply fld_add_assoc.

   subst rp₁ rp₂; simpl.
   apply fld_eq_refl.

  destruct al₃ as [| a₃]; simpl in H₁.
   subst rp₁ rp₂; simpl.
   apply fld_eq_refl.

   subst rp₁ rp₂; simpl.
   apply fld_eq_refl.

 simpl in H₁.
 destruct al₂ as [| a₂]; simpl in H₁.
  destruct al₃ as [| a₃]; simpl in H₁.
   subst rp₁ rp₂; simpl.
   apply fld_eq_refl.

   subst rp₁ rp₂; simpl.
   apply fld_eq_refl.

  destruct al₃ as [| a₃]; simpl in H₁.
   subst rp₁ rp₂; simpl.
   apply fld_eq_refl.

   subst rp₁ rp₂; simpl.
   eapply IHal₁; reflexivity.
Qed.

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
 eapply pol_add_loop_al_assoc; reflexivity.

 eapply pol_add_loop_an_assoc; reflexivity.
Qed.
