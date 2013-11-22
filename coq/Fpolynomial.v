(* $Id: Fpolynomial.v,v 2.2 2013-11-22 19:20:28 deraugla Exp $ *)

(* polynomials on a field *)

Require Import Utf8.
Require Import QArith.

Require Import Field.
Require Import Misc.
Require Import Polynomial.

Set Implicit Arguments.

Definition list_eq := List.Forall2.

Definition eq_poly α fld (x y : polynomial α) :=
  list_eq (Field.eq fld) (al x ++ [an x]) (al y ++ [an y]).

Definition poly_add α (fld : Field.t α) :=
  pol_add (Field.add fld).

Definition poly_mul α (fld : Field.t α) :=
  pol_mul (Field.zero fld) (Field.add fld) (Field.mul fld).

Definition Pdivide α fld (x y : polynomial α) :=
  ∃ z, eq_poly fld y (poly_mul fld z x).

Lemma list_eq_refl : ∀ α (fld : Field.t α) l,
  list_eq (Field.eq fld) l l.
Proof.
intros α fld l.
induction l; constructor; [ reflexivity | assumption ].
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

Lemma pol_add_loop_al_comm : ∀ α (fld : Field.t α) an₁ an₂ al₁ al₂ rp₁ rp₂,
  rp₁ = pol_add_loop (Field.add fld) an₁ an₂ al₁ al₂
  → rp₂ = pol_add_loop (Field.add fld) an₂ an₁ al₂ al₁
    → list_eq (Field.eq fld) (al rp₁) (al rp₂).
Proof.
intros α fld an₁ an₂ al₁ al₂ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert an₁ an₂ al₂.
induction al₁; intros.
 destruct al₂; [ apply list_eq_refl | simpl ].
 constructor; [ apply Field.add_comm | apply list_eq_refl ].

 destruct al₂.
  constructor; [ apply Field.add_comm | apply list_eq_refl ].

  constructor; [ apply Field.add_comm | apply IHal₁ ].
Qed.

Lemma pol_add_loop_an_comm : ∀ α (fld : Field.t α) an₁ an₂ al₁ al₂ rp₁ rp₂,
  rp₁ = pol_add_loop (Field.add fld) an₁ an₂ al₁ al₂
  → rp₂ = pol_add_loop (Field.add fld) an₂ an₁ al₂ al₁
    → Field.eq fld (an rp₁) (an rp₂).
Proof.
intros α fld an₁ an₂ al₁ al₂ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert an₁ an₂ al₂.
induction al₁; intros.
 destruct al₂; [ apply Field.add_comm | reflexivity ].

 destruct al₂; [ reflexivity | eapply IHal₁; reflexivity ].
Qed.

Lemma poly_add_comm : ∀ α (fld : Field.t α) pol₁ pol₂,
  eq_poly fld (poly_add fld pol₁ pol₂) (poly_add fld pol₂ pol₁).
Proof.
intros α fld pol₁ pol₂.
unfold eq_poly.
apply list_eq_append_one.
split.
 eapply pol_add_loop_al_comm; reflexivity.

 eapply pol_add_loop_an_comm; reflexivity.
Qed.

(* addition associativity *)

Lemma pol_add_loop_al_assoc :
    ∀ α (fld : Field.t α) an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂,
  rp₁ = pol_add_loop (Field.add fld)
          (an (pol_add_loop (Field.add fld) an₁ an₂ al₁ al₂)) an₃
          (al (pol_add_loop (Field.add fld) an₁ an₂ al₁ al₂)) al₃
  → rp₂ = pol_add_loop (Field.add fld)
           an₁ (an (pol_add_loop (Field.add fld) an₂ an₃ al₂ al₃))
           al₁ (al (pol_add_loop (Field.add fld) an₂ an₃ al₂ al₃))
    → list_eq (Field.eq fld) (al rp₁) (al rp₂).
Proof.
intros α fld an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert an₁ an₂ an₃ al₂ al₃.
induction al₁; intros.
 destruct al₂.
  destruct al₃; [ apply list_eq_refl | idtac ].
  constructor; [ symmetry; apply Field.add_assoc | apply list_eq_refl ].

  destruct al₃; simpl.
   constructor; [ symmetry; apply Field.add_assoc | apply list_eq_refl ].

   constructor; [ symmetry; apply Field.add_assoc | apply list_eq_refl ].

 destruct al₂.
  destruct al₃; simpl.
   constructor; [ symmetry; apply Field.add_assoc | apply list_eq_refl ].

   constructor; [ symmetry; apply Field.add_assoc | apply list_eq_refl ].

  destruct al₃; simpl.
   constructor; [ symmetry; apply Field.add_assoc | apply list_eq_refl ].

   constructor; [ symmetry; apply Field.add_assoc | apply IHal₁ ].
Qed.

Lemma pol_add_loop_an_assoc :
    ∀ α (fld : Field.t α) an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂,
  rp₁ = pol_add_loop (Field.add fld)
          (an (pol_add_loop (Field.add fld) an₁ an₂ al₁ al₂)) an₃
          (al (pol_add_loop (Field.add fld) an₁ an₂ al₁ al₂)) al₃
  → rp₂ = pol_add_loop (Field.add fld)
           an₁ (an (pol_add_loop (Field.add fld) an₂ an₃ al₂ al₃))
           al₁ (al (pol_add_loop (Field.add fld) an₂ an₃ al₂ al₃))
    → Field.eq fld (an rp₁) (an rp₂).
Proof.
intros α fld an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert an₁ an₂ an₃ al₂ al₃.
induction al₁; intros.
 destruct al₂.
  destruct al₃; [ symmetry; apply Field.add_assoc | reflexivity ].

  destruct al₃; reflexivity.

 destruct al₂.
  destruct al₃; reflexivity.

  destruct al₃; [ reflexivity | eapply IHal₁; reflexivity ].
Qed.

Lemma poly_add_assoc : ∀ α (fld : Field.t α) pol₁ pol₂ pol₃,
  eq_poly fld
    (poly_add fld (poly_add fld pol₁ pol₂) pol₃)
    (poly_add fld pol₁ (poly_add fld pol₂ pol₃)).
Proof.
intros α fld pol₁ pol₂ pol₃.
unfold eq_poly.
apply list_eq_append_one.
split.
 eapply pol_add_loop_al_assoc; reflexivity.

 eapply pol_add_loop_an_assoc; reflexivity.
Qed.
