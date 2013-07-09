(* $Id: Fpolynomial.v,v 1.11 2013-07-09 18:59:53 deraugla Exp $ *)

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

Lemma list_eq_trans : ∀ α (fld : field α) l₁ l₂ l₃,
  list_eq (fld_eq fld) l₁ l₂ = true
  → list_eq (fld_eq fld) l₂ l₃ = true
    → list_eq (fld_eq fld) l₁ l₃ = true.
Proof.
intros α fld l₁ l₂ l₃ H₁ H₂.
revert l₁ l₃ H₁ H₂.
induction l₂ as [| x₂]; intros.
 rewrite list_eq_comm in H₁.
 simpl in H₁, H₂.
 destruct l₁; [ idtac | discriminate H₁ ].
 simpl.
 assumption.

 rewrite list_eq_comm in H₁.
 simpl in H₁, H₂.
 destruct l₁ as [| x₁]; [ discriminate H₁ | idtac ].
 destruct l₃ as [| x₃]; [ discriminate H₂ | idtac ].
 simpl.
 apply andb_true_iff in H₁.
 apply andb_true_iff in H₂.
 apply andb_true_iff.
 destruct H₁ as (H₁, H₃).
 destruct H₂ as (H₂, H₄).
 split.
  rewrite fld_eq_comm in H₁.
  eapply fld_eq_trans; eassumption.

  rewrite list_eq_comm in H₃.
  eapply IHl₂; eassumption.
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
  simpl in H₂.
  subst rp₁ rp₂; reflexivity.

  simpl in H₂.
  subst rp₁ rp₂; simpl.
  rewrite fld_add_comm; simpl.
  clear a₂.
  induction al₂ as [| a₂]; [ reflexivity | simpl ].
  rewrite fld_eq_refl.
  assumption.

 simpl in H₁.
 destruct al₂ as [| a₂].
  simpl in H₂.
  subst rp₁ rp₂; simpl.
  rewrite fld_add_comm; simpl.
  clear a₁ IHal₁.
  induction al₁ as [| a₁]; [ reflexivity | simpl ].
  rewrite fld_eq_refl; assumption.

  simpl in H₂.
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
  simpl in H₂.
  subst rp₁ rp₂; simpl.
  apply fld_add_comm.

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
revert an₁ an₂ an₃ al₁ al₃ rp₁ rp₂ H₁ H₂.
induction al₂ as [| a₂]; intros.
 simpl in H₂.
 destruct al₃ as [| a₃]; simpl in H₁, H₂.
  eapply pol_add_loop_al_comm in H₂; [ idtac | reflexivity ].
  simpl in H₂.
  destruct al₁ as [| a₁]; simpl in H₁, H₂.
   subst rp₁; simpl.
   assumption.

   subst rp₁; simpl.
   destruct (al rp₂) as [| a₂ al₂]; [ discriminate H₂ | idtac ].
   apply andb_true_iff.
   apply andb_true_iff in H₂.
   destruct H₂ as (Hf, He).
   split; [ idtac | assumption ].
   eapply fld_eq_trans; [ idtac | eassumption ].
   eapply fld_eq_trans; [ apply fld_add_assoc | apply fld_add_comm ].

  eapply pol_add_loop_al_comm in H₂; [ idtac | reflexivity ].
  simpl in H₂.
  destruct al₁ as [| a₁]; simpl in H₁, H₂.
   subst rp₁; simpl.
   destruct (al rp₂) as [| a₂ al₂]; [ discriminate H₂ | idtac ].
   apply andb_true_iff.
   apply andb_true_iff in H₂.
   destruct H₂ as (Hf, He).
   split; [ idtac | assumption ].
   eapply fld_eq_trans; [ idtac | eassumption ].
   eapply fld_eq_trans; [ apply fld_add_assoc | apply fld_add_comm ].

   subst rp₁; simpl.
   destruct (al rp₂) as [| a₂ al₂]; [ discriminate H₂ | idtac ].
   apply andb_true_iff.
   apply andb_true_iff in H₂.
   destruct H₂ as (Hf, He).
   split.
    eapply fld_eq_trans; [ rewrite fld_eq_comm | eassumption ].
    eapply fld_eq_trans; [ apply fld_add_comm | rewrite fld_eq_comm ].
    apply fld_add_assoc.

    rewrite list_eq_comm.
    rewrite list_eq_comm in He.
    eapply list_eq_trans; [ eassumption | idtac ].
    eapply pol_add_loop_al_comm; reflexivity.

 simpl in H₂.
 destruct al₃ as [| a₃]; simpl in H₂.
  destruct al₁ as [| a₁]; simpl in H₁, H₂.
   subst rp₁ rp₂; simpl.
   apply andb_true_iff.
   split; [ apply fld_add_assoc | apply list_eq_refl ].

   subst rp₁ rp₂; simpl.
   apply andb_true_iff.
   split; [ apply fld_add_assoc | apply list_eq_refl ].

  destruct al₁ as [| a₁]; simpl in H₁, H₂.
   subst rp₁ rp₂; simpl.
   apply andb_true_iff.
   split; [ apply fld_add_assoc | apply list_eq_refl ].

   subst rp₁ rp₂; simpl.
   apply andb_true_iff.
   split; [ apply fld_add_assoc | idtac ].
   eapply IHal₂; reflexivity.
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

bbb.
intros α fld an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
revert an₁ an₂ an₃ al₁ al₃ rp₁ rp₂ H₁ H₂.
induction al₂ as [| a₂]; intros.
 simpl in H₂.
 destruct al₃ as [| a₃]; simpl in H₁, H₂.
  eapply pol_add_loop_al_comm in H₂; [ idtac | reflexivity ].
  simpl in H₂.
  destruct al₁ as [| a₁]; simpl in H₁, H₂.
   subst rp₁; simpl.
   remember (al rp₂) as al₂.
   destruct al₂; [ idtac | discriminate H₂ ].
   Focus 2.
   subst rp₁; simpl.
   remember (al rp₂) as al₂.
   destruct al₂ as [| a₂]; [ discriminate H₂ | idtac ].
   apply andb_true_iff in H₂.
   destruct H₂ as (H₁, H₂).
bbb.
*)


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
bbb.
