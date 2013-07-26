(* $Id: Fpolynomial.v,v 1.20 2013-07-26 21:38:42 deraugla Exp $ *)

(* polynomials on a field *)

Require Import Utf8.
Require Import QArith.

Require Import Field.
Require Import Misc.
Require Import Polynomial.

Set Implicit Arguments.

Inductive list_eq α (cmp : α → α → Prop) : list α → list α → Prop :=
  | list_eq_nil : list_eq cmp [] []
  | list_eq_cons : ∀ x₁ x₂ l₁ l₂,
      cmp x₁ x₂ → list_eq cmp l₁ l₂ → list_eq cmp [x₁ … l₁] [x₂ … l₂].

Definition poly_eq α fld (x y : polynomial α) :=
  list_eq (fld_eq fld) (al x ++ [an x]) (al y ++ [an y]).

Definition poly_add α (fld : field α) :=
  pol_add (add fld).

Definition poly_mul α (fld : field α) :=
  pol_mul (zero fld) (add fld) (mul fld).

Definition Pdivide α fld (x y : polynomial α) :=
  ∃ z, poly_eq fld y (poly_mul fld z x).

Lemma list_eq_refl : ∀ α (fld : field α) l,
  list_eq (fld_eq fld) l l.
Proof.
intros α fld l.
induction l; constructor; [ apply fld_eq_refl | assumption ].
Qed.

Lemma list_eq_append_one : ∀ α cmp (x₁ x₂ : α) l₁ l₂,
  list_eq cmp l₁ l₂ ∧ cmp x₁ x₂
  → list_eq cmp (l₁ ++ [x₁]) (l₂ ++ [x₂]).
Proof.
intros α cmp x₁ x₂ l₁ l₂.
revert x₁ x₂ l₂.
induction l₁ as [| x₃]; intros; simpl.
 destruct l₂ as [| x₄]; simpl.
  constructor; destruct H; assumption.

  destruct H as (H, _); inversion H.

 destruct l₂ as [| x₄]; simpl.
  destruct H as (H, _); inversion H.

  constructor.
   destruct H as (H, _).
   inversion H; assumption.

   apply IHl₁.
   split; [ idtac | destruct H; assumption ].
   destruct H as (H, _).
   inversion H; assumption.
Qed.

(* addition commutativity *)

Lemma pol_add_loop_al_comm : ∀ α (fld : field α) an₁ an₂ al₁ al₂ rp₁ rp₂,
  rp₁ = pol_add_loop (add fld) an₁ an₂ al₁ al₂
  → rp₂ = pol_add_loop (add fld) an₂ an₁ al₂ al₁
    → list_eq (fld_eq fld) (al rp₁) (al rp₂).
Proof.
intros α fld an₁ an₂ al₁ al₂ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert an₁ an₂ al₂.
induction al₁; intros.
 destruct al₂; [ apply list_eq_refl | simpl ].
 constructor; [ apply fld_add_comm | apply list_eq_refl ].

 destruct al₂.
  constructor; [ apply fld_add_comm | apply list_eq_refl ].

  constructor; [ apply fld_add_comm | apply IHal₁ ].
Qed.

Lemma pol_add_loop_an_comm : ∀ α (fld : field α) an₁ an₂ al₁ al₂ rp₁ rp₂,
  rp₁ = pol_add_loop (add fld) an₁ an₂ al₁ al₂
  → rp₂ = pol_add_loop (add fld) an₂ an₁ al₂ al₁
    → fld_eq fld (an rp₁) (an rp₂).
Proof.
intros α fld an₁ an₂ al₁ al₂ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert an₁ an₂ al₂.
induction al₁; intros.
 destruct al₂; [ apply fld_add_comm | apply fld_eq_refl ].

 destruct al₂; [ apply fld_eq_refl | eapply IHal₁; reflexivity ].
Qed.

Lemma poly_add_comm : ∀ α (fld : field α) pol₁ pol₂,
  poly_eq fld (poly_add fld pol₁ pol₂) (poly_add fld pol₂ pol₁).
Proof.
intros α fld pol₁ pol₂.
unfold poly_eq.
apply list_eq_append_one.
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
    → list_eq (fld_eq fld) (al rp₁) (al rp₂).
Proof.
intros α fld an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert an₁ an₂ an₃ al₂ al₃.
induction al₁; intros.
 destruct al₂.
  destruct al₃; [ apply list_eq_refl | idtac ].
  constructor; [ apply fld_add_assoc | apply list_eq_refl ].

  destruct al₃; simpl.
   constructor; [ apply fld_add_assoc | apply list_eq_refl ].

   constructor; [ apply fld_add_assoc | apply list_eq_refl ].

 destruct al₂.
  destruct al₃; simpl.
   constructor; [ apply fld_add_assoc | apply list_eq_refl ].

   constructor; [ apply fld_add_assoc | apply list_eq_refl ].

  destruct al₃; simpl.
   constructor; [ apply fld_add_assoc | apply list_eq_refl ].

   constructor; [ apply fld_add_assoc | apply IHal₁ ].
Qed.

Lemma pol_add_loop_an_assoc :
    ∀ α (fld : field α) an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂,
  rp₁ = pol_add_loop (add fld)
          (an (pol_add_loop (add fld) an₁ an₂ al₁ al₂)) an₃
          (al (pol_add_loop (add fld) an₁ an₂ al₁ al₂)) al₃
  → rp₂ = pol_add_loop (add fld)
           an₁ (an (pol_add_loop (add fld) an₂ an₃ al₂ al₃))
           al₁ (al (pol_add_loop (add fld) an₂ an₃ al₂ al₃))
    → fld_eq fld (an rp₁) (an rp₂).
Proof.
intros α fld an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert an₁ an₂ an₃ al₂ al₃.
induction al₁; intros.
 destruct al₂.
  destruct al₃; [ apply fld_add_assoc | apply fld_eq_refl ].

  destruct al₃; apply fld_eq_refl.

 destruct al₂.
  destruct al₃; apply fld_eq_refl.

  destruct al₃; [ apply fld_eq_refl | eapply IHal₁; reflexivity ].
Qed.

Lemma poly_add_assoc : ∀ α (fld : field α) pol₁ pol₂ pol₃,
  poly_eq fld
    (poly_add fld (poly_add fld pol₁ pol₂) pol₃)
    (poly_add fld pol₁ (poly_add fld pol₂ pol₃)).
Proof.
intros α fld pol₁ pol₂ pol₃.
unfold poly_eq.
apply list_eq_append_one.
split.
 eapply pol_add_loop_al_assoc; reflexivity.

 eapply pol_add_loop_an_assoc; reflexivity.
Qed.
