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
intros pol.
unfold eq_poly, list_eq.
induction (al pol); constructor; [ reflexivity | assumption ].
Qed.

Theorem eq_poly_sym α (f : field α) : symmetric _ (eq_poly f).
Proof.
intros pol₁ pol₂ Heq.
unfold eq_poly, list_eq.
unfold eq_poly, list_eq in Heq.
remember (al pol₁) as l₁.
remember (al pol₂) as l₂.
clear pol₁ pol₂ Heql₁ Heql₂.
revert l₂ Heq.
induction l₁ as [| x₁]; intros.
 destruct l₂; [ constructor | inversion Heq ].

 destruct l₂ as [| x₂]; [ inversion Heq | idtac ].
 constructor.
  inversion Heq; subst; symmetry; assumption.

  inversion Heq; subst; apply IHl₁; assumption.
Qed.

Theorem eq_poly_trans α (f : field α) : transitive _ (eq_poly f).
Proof.
intros pol₁ pol₂ pol₃ H₁ H₂.
unfold eq_poly, list_eq.
unfold eq_poly, list_eq in H₁.
unfold eq_poly, list_eq in H₂.
remember (al pol₁) as l₁.
remember (al pol₂) as l₂.
remember (al pol₃) as l₃.
revert H₁ H₂; clear; intros.
revert l₁ l₃ H₁ H₂.
induction l₂ as [| x₂]; intros.
 inversion H₁; subst; assumption.

 destruct l₁ as [| x₁]; [ inversion H₁ | idtac ].
 destruct l₃ as [| x₃]; [ inversion H₂ | idtac ].
 constructor.
  inversion H₁; subst.
  inversion H₂; subst.
  transitivity x₂; assumption.

  inversion H₁; subst.
  inversion H₂; subst.
  apply IHl₂; assumption.
Qed.

Add Parametric Relation α (f : field α) : (polynomial α) (eq_poly f)
 reflexivity proved by (eq_poly_refl f)
 symmetry proved by (eq_poly_sym (f := f))
 transitivity proved by (eq_poly_trans (f := f))
 as eq_poly_rel.

Add Parametric Morphism α (f : field α) : (poly_add f)
  with signature (eq_poly f) ==> (eq_poly f) ==> (eq_poly f)
  as ps_pol_add_morph.
Proof.
intros a c Hac b d Hbd.
unfold eq_poly, poly_add; simpl.
unfold eq_poly in Hac, Hbd.
unfold list_eq in Hac, Hbd |- *.
remember (al a) as la.
remember (al b) as lb.
remember (al c) as lc.
remember (al d) as ld.
revert Hac Hbd; clear; intros.
revert lb lc ld Hac Hbd.
induction la as [| a]; intros.
 inversion Hac; subst; simpl.
 inversion Hbd; subst; constructor; assumption.

 inversion Hac; subst; simpl.
 destruct lb as [| b].
  destruct ld as [| d]; [ assumption | inversion Hbd ].

  destruct ld as [| d]; [ inversion Hbd | idtac ].
  constructor.
   inversion Hbd; subst.
   rewrite H1, H4; reflexivity.

   apply IHla; [ inversion Hac | inversion Hbd ]; assumption.
Qed.

Add Parametric Morphism α (f : field α) : (poly_mul f)
  with signature (eq_poly f) ==> (eq_poly f) ==> (eq_poly f)
  as ps_pol_mul_morph.
Proof.
intros a c Hac b d Hbd.
unfold eq_poly, poly_mul; simpl.
unfold eq_poly in Hac, Hbd.
unfold list_eq in Hac, Hbd |- *.
remember (al a) as la.
remember (al b) as lb.
remember (al c) as lc.
remember (al d) as ld.
revert Hac Hbd; clear; intros.
revert lb lc ld Hac Hbd.
induction la as [| a]; intros.
 simpl.
 inversion Hac; subst; simpl.
 inversion Hbd; subst.
  constructor.

  simpl.
  constructor.
   unfold sigma; simpl.
   do 2 rewrite fld_mul_0_l; reflexivity.

   clear Hac Hbd.
bbb.
   remember (length l) as len.
   remember (length l') as len'.
   destruct len.
    simpl.
    destruct len'.
     simpl.
     constructor.

     inversion H0; subst.
      discriminate Heqlen'.

      discriminate Heqlen.

    destruct len'.
     inversion H0; subst.
      discriminate Heqlen.

      discriminate Heqlen'.
bbb.

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

(* addition compatibility with equality *)

Theorem pol_add_compat : ∀ a b c d,
  (a .= f c)%pol
  → (b .= f d)%pol
    → (a .+ f b .= f c .+ f d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
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

(* multiplication compatibility with equality *)

Theorem pol_mul_compat : ∀ a b c d,
  (a .= f c)%pol
  → (b .= f d)%pol
    → (a .* f b .= f c .* f d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

End poly.
