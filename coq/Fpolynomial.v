(* Fpolynomial.v *)

(* polynomials on a field *)

Require Import Utf8.
Require Import QArith.

Require Field.
Require Import Misc.
Require Import Polynomial.

Set Implicit Arguments.

Definition list_eq := List.Forall2.

Section poly.

Variable α : Type.
Variable K : Field.f α.
Let R := Field.ring K.

Definition eq_poly (x y : polynomial α) :=
  list_eq (Field.eq R) (al x ++ [an x]) (al y ++ [an y]).

Definition poly_add :=
  pol_add (Field.add R).

Definition poly_mul :=
  pol_mul (Field.zero R) (Field.add R) (Field.mul R).

Definition Pdivide (x y : polynomial α) :=
  ∃ z, eq_poly y (poly_mul z x).

Lemma list_eq_refl : ∀ l, list_eq (Field.eq R) l l.
Proof.
intros l.
induction l; constructor; [ reflexivity | assumption ].
Qed.

Lemma list_eq_append_one : ∀ cmp (x₁ x₂ : α) l₁ l₂,
  list_eq cmp l₁ l₂ ∧ cmp x₁ x₂
  → list_eq cmp (l₁ ++ [x₁]) (l₂ ++ [x₂]).
Proof.
intros cmp x₁ x₂ l₁ l₂.
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

Lemma pol_add_loop_al_comm : ∀ an₁ an₂ al₁ al₂ rp₁ rp₂,
  rp₁ = pol_add_loop (Field.add R) an₁ an₂ al₁ al₂
  → rp₂ = pol_add_loop (Field.add R) an₂ an₁ al₂ al₁
    → list_eq (Field.eq R) (al rp₁) (al rp₂).
Proof.
intros an₁ an₂ al₁ al₂ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert an₁ an₂ al₂.
induction al₁; intros.
 destruct al₂; [ apply list_eq_refl | simpl ].
 constructor; [ apply Field.add_comm | apply list_eq_refl ].

 destruct al₂.
  constructor; [ apply Field.add_comm | apply list_eq_refl ].

  constructor; [ apply Field.add_comm | apply IHal₁ ].
Qed.

Lemma pol_add_loop_an_comm : ∀ an₁ an₂ al₁ al₂ rp₁ rp₂,
  rp₁ = pol_add_loop (Field.add R) an₁ an₂ al₁ al₂
  → rp₂ = pol_add_loop (Field.add R) an₂ an₁ al₂ al₁
    → Field.eq R (an rp₁) (an rp₂).
Proof.
intros an₁ an₂ al₁ al₂ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert an₁ an₂ al₂.
induction al₁; intros.
 destruct al₂; [ apply Field.add_comm | reflexivity ].

 destruct al₂; [ reflexivity | eapply IHal₁; reflexivity ].
Qed.

Lemma poly_add_comm : ∀ pol₁ pol₂,
  eq_poly (poly_add pol₁ pol₂) (poly_add pol₂ pol₁).
Proof.
intros pol₁ pol₂.
unfold eq_poly.
apply list_eq_append_one.
split.
 eapply pol_add_loop_al_comm; reflexivity.

 eapply pol_add_loop_an_comm; reflexivity.
Qed.

(* addition associativity *)

Lemma pol_add_loop_al_assoc : ∀ an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂,
  rp₁ = pol_add_loop (Field.add R)
          (an (pol_add_loop (Field.add R) an₁ an₂ al₁ al₂)) an₃
          (al (pol_add_loop (Field.add R) an₁ an₂ al₁ al₂)) al₃
  → rp₂ = pol_add_loop (Field.add R)
           an₁ (an (pol_add_loop (Field.add R) an₂ an₃ al₂ al₃))
           al₁ (al (pol_add_loop (Field.add R) an₂ an₃ al₂ al₃))
    → list_eq (Field.eq R) (al rp₁) (al rp₂).
Proof.
intros an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
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

Lemma pol_add_loop_an_assoc : ∀ an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂,
  rp₁ = pol_add_loop (Field.add R)
          (an (pol_add_loop (Field.add R) an₁ an₂ al₁ al₂)) an₃
          (al (pol_add_loop (Field.add R) an₁ an₂ al₁ al₂)) al₃
  → rp₂ = pol_add_loop (Field.add R)
           an₁ (an (pol_add_loop (Field.add R) an₂ an₃ al₂ al₃))
           al₁ (al (pol_add_loop (Field.add R) an₂ an₃ al₂ al₃))
    → Field.eq R (an rp₁) (an rp₂).
Proof.
intros an₁ an₂ an₃ al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
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

Lemma poly_add_assoc : ∀ pol₁ pol₂ pol₃,
  eq_poly
    (poly_add (poly_add pol₁ pol₂) pol₃)
    (poly_add pol₁ (poly_add pol₂ pol₃)).
Proof.
intros pol₁ pol₂ pol₃.
unfold eq_poly.
apply list_eq_append_one.
split.
 eapply pol_add_loop_al_assoc; reflexivity.

 eapply pol_add_loop_an_assoc; reflexivity.
Qed.

End poly.
