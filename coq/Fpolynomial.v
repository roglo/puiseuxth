(* Fpolynomial.v *)

(* polynomials on a field *)

Require Import Utf8.
Require Import QArith.

Require Import Misc.
Require Import Field.
Require Import Polynomial.

Set Implicit Arguments.

Definition list_eq := List.Forall2.

Definition eq_poly α (f : field α) (x y : polynomial α) :=
  list_eq (fld_eq f) (al x) (al y).

Definition poly_add α (f : field α) := pol_add (fld_add f).
Definition poly_mul α (f : field α) := pol_mul .0 f%F (fld_add f) (fld_mul f).

Delimit Scope poly_scope with pol.
Notation "a .= f b" := (eq_poly f a b) : poly_scope.
Notation "a .+ f b" := (poly_add f a b) : poly_scope.
Notation "a .* f b" := (poly_mul f a b) : poly_scope.

Definition Pdivide α (f : field α) x y := ∃ z, (y .= f z .* f x)%pol.

Theorem eq_poly_refl α (f : field α) : reflexive _ (eq_poly f).
Proof.
bbb.
*)

Theorem eq_poly_sym α (f : field α) : symmetric _ (eq_poly f).
Proof.
bbb.
*)

Theorem eq_poly_trans α (f : field α) : transitive _ (eq_poly f).
Proof.
bbb.
*)

Add Parametric Relation α (f : field α) : (polynomial α) (eq_poly f)
 reflexivity proved by (eq_poly_refl f)
 symmetry proved by (eq_poly_sym (f := f))
 transitivity proved by (eq_poly_trans (f := f))
 as eq_poly_rel.

Section poly.

Variable α : Type.
Variable f : field α.

Lemma list_eq_refl : ∀ l, list_eq (fld_eq f) l l.
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

Lemma pol_add_loop_al_comm : ∀ al₁ al₂ rp₁ rp₂,
  rp₁ = pol_add_loop (fld_add f) al₁ al₂
  → rp₂ = pol_add_loop (fld_add f) al₂ al₁
    → list_eq (fld_eq f) rp₁ rp₂.
Proof.
intros al₁ al₂ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert al₂.
induction al₁; intros.
 destruct al₂; [ apply list_eq_refl | simpl ].
 constructor; [ reflexivity | apply list_eq_refl ].

 destruct al₂.
  constructor; [ reflexivity | apply list_eq_refl ].

  constructor; [ apply fld_add_comm | apply IHal₁ ].
Qed.

Lemma poly_add_comm : ∀ pol₁ pol₂, (pol₁ .+ f pol₂ .= f pol₂ .+ f pol₁)%pol.
Proof.
intros pol₁ pol₂.
unfold eq_poly.
eapply pol_add_loop_al_comm; reflexivity.
Qed.

(* addition associativity *)

Lemma pol_add_loop_al_assoc : ∀ al₁ al₂ al₃ rp₁ rp₂,
  rp₁ = pol_add_loop (fld_add f) (pol_add_loop (fld_add f) al₁ al₂) al₃
  → rp₂ = pol_add_loop (fld_add f) al₁ (pol_add_loop (fld_add f) al₂ al₃)
    → list_eq (fld_eq f) rp₁ rp₂.
Proof.
intros al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
revert al₂ al₃.
induction al₁; intros.
 destruct al₂.
  destruct al₃; [ apply list_eq_refl | idtac ].
  constructor; [ reflexivity | apply list_eq_refl ].

  destruct al₃; simpl.
   constructor; [ reflexivity | apply list_eq_refl ].

   constructor; [ reflexivity | apply list_eq_refl ].

 destruct al₂.
  destruct al₃; simpl.
   constructor; [ reflexivity | apply list_eq_refl ].

   constructor; [ reflexivity | apply list_eq_refl ].

  destruct al₃; simpl.
   constructor; [ reflexivity | apply list_eq_refl ].

   constructor; [ symmetry; apply fld_add_assoc | apply IHal₁ ].
Qed.

Lemma poly_add_assoc : ∀ pol₁ pol₂ pol₃,
  ((pol₁ .+ f pol₂) .+ f pol₃ .= f pol₁ .+ f (pol₂ .+ f pol₃))%pol.
Proof.
intros pol₁ pol₂ pol₃.
unfold eq_poly.
eapply pol_add_loop_al_assoc; reflexivity.
Qed.

End poly.
