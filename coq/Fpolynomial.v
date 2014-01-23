(* Fpolynomial.v *)

(* polynomials on a field *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Field.
Require Import Fsummation.

Set Implicit Arguments.

Record polynomial α := mkpol { al : list α }.

Inductive list_eq α (f : field α) : list α → list α → Prop :=
  | list_eq_nil : list_eq f [] []
  | list_eq_cons : ∀ x₁ x₂ l₁ l₂,
      (x₁ .= f x₂)%K
      → list_eq f l₁ l₂
        → list_eq f [x₁ … l₁] [x₂ … l₂]
  | list_eq_nil_right : ∀ x l,
      (x .= f .0 f)%K
      → list_eq f l []
        → list_eq f [x … l] []
  | list_eq_nil_left : ∀ x l,
      (x .= f .0 f)%K
      → list_eq f [] l
        → list_eq f [] [x … l].

Delimit Scope poly_scope with pol.
Notation "'POL' l" := {| al := l |} (at level 1) : poly_scope.

Definition eq_poly α (f : field α) x y := list_eq f (al x) (al y).

Notation "a .= f b" := (eq_poly f a b) : poly_scope.

Definition poly_one α (f : field α) := POL [.1 f%K]%pol.
Notation ".1 f" := (poly_one f) : poly_scope.

Theorem list_eq_refl α (f : field α) : reflexive _ (list_eq f).
Proof.
intros l.
induction l; constructor; [ reflexivity | assumption ].
Qed.

Theorem list_eq_sym α (f : field α) : symmetric _ (list_eq f).
Proof.
intros l₁ l₂ Heq.
revert l₂ Heq.
induction l₁ as [| x₁]; intros.
 induction l₂ as [| x₂]; constructor; inversion Heq.
  assumption.

  apply IHl₂; assumption.

 induction l₂ as [| x₂]; constructor; inversion Heq.
  assumption.

  apply IHl₁; assumption.

  symmetry; assumption.

  apply IHl₁; assumption.
Qed.

Theorem list_eq_trans α (f : field α) : transitive _ (list_eq f).
Proof.
intros l₁ l₂ l₃ H₁ H₂.
revert l₁ l₃ H₁ H₂.
induction l₂ as [| x₂]; intros.
 revert l₃ H₂.
 induction l₁ as [| x₁]; intros; [ assumption | idtac ].
 destruct l₃ as [| x₃]; [ assumption | idtac ].
 constructor.
  inversion H₁; subst.
  inversion H₂; subst.
  symmetry in H3.
  etransitivity; eassumption.

  apply IHl₁.
   inversion H₁; assumption.

   inversion H₂; assumption.

 inversion H₁; subst.
  inversion H₂; subst.
   constructor.
    etransitivity; eassumption.

    apply IHl₂; assumption.

   constructor; [ etransitivity; eassumption | idtac ].
   apply IHl₂; assumption.

  clear H₁ IHl₂.
  revert x₂ l₂ H₂ H2 H3.
  induction l₃ as [| x₃]; intros; [ constructor | idtac ].
  constructor.
   inversion H₂; subst.
   symmetry in H4.
   etransitivity; eassumption.

   inversion H₂; subst.
   inversion H3; subst; [ assumption | idtac ].
   eapply IHl₃; eassumption.
Qed.

Add Parametric Relation α (f : field α) : (list α) (list_eq f)
 reflexivity proved by (list_eq_refl f)
 symmetry proved by (list_eq_sym (f := f))
 transitivity proved by (list_eq_trans (f := f))
 as list_eq_rel.

Theorem eq_poly_refl α (f : field α) : reflexive _ (eq_poly f).
Proof.
intros pol.
unfold eq_poly; reflexivity.
Qed.

Theorem eq_poly_sym α (f : field α) : symmetric _ (eq_poly f).
Proof.
intros pol₁ pol₂ Heq.
unfold eq_poly; symmetry; assumption.
Qed.

Theorem eq_poly_trans α (f : field α) : transitive _ (eq_poly f).
Proof.
intros pol₁ pol₂ pol₃ H₁ H₂.
unfold eq_poly; etransitivity; eassumption.
Qed.

Add Parametric Relation α (f : field α) : (polynomial α) (eq_poly f)
 reflexivity proved by (eq_poly_refl f)
 symmetry proved by (eq_poly_sym (f := f))
 transitivity proved by (eq_poly_trans (f := f))
 as eq_poly_rel.

(* addition *)

Fixpoint poly_add_loop α (f : field α) al₁ al₂ :=
  match al₁ with
  | [] => al₂
  | [a₁ … bl₁] =>
      match al₂ with
      | [] => al₁
      | [a₂ … bl₂] => [(a₁ .+ f a₂)%K … poly_add_loop f bl₁ bl₂]
      end
  end.

Definition poly_add α (f : field α) pol₁ pol₂ :=
  {| al := poly_add_loop f (al pol₁) (al pol₂) |}.

(* multiplication *)

Fixpoint poly_convol_mul α (f : field α) al₁ al₂ i len :=
  match len with
  | O => []
  | S len₁ =>
      [Σ f (j = 0, i) _ List.nth j al₁ .0 f .* f List.nth (i - j) al₂ .0 f …
       poly_convol_mul f al₁ al₂ (S i) len₁]
  end.

Definition poly_mul α (f : field α) pol₁ pol₂ :=
  {| al :=
       poly_convol_mul f (al pol₁) (al pol₂) O
         (max (List.length (al pol₁)) (List.length (al pol₂))) |}.

(* *)

Notation "a .+ f b" := (poly_add f a b) : poly_scope.
Notation "a .* f b" := (poly_mul f a b) : poly_scope.

Definition Pdivide α (f : field α) x y := ∃ z, (y .= f z .* f x)%pol.

Add Parametric Morphism α (f : field α) : (@al α)
  with signature eq_poly f ==> list_eq f
  as al_morph.
Proof.
intros a b Hab.
inversion Hab; constructor; assumption.
Qed.

Add Parametric Morphism α (f : field α) : (poly_add f)
  with signature (eq_poly f) ==> (eq_poly f) ==> (eq_poly f)
  as ps_poly_add_morph.
Proof.
intros a c Hac b d Hbd.
unfold eq_poly, poly_add; simpl.
unfold eq_poly in Hac, Hbd.
remember (al a) as la.
remember (al b) as lb.
remember (al c) as lc.
remember (al d) as ld.
revert Hac Hbd; clear; intros.
revert lb lc ld Hac Hbd.
induction la as [| a]; intros.
 simpl.
 inversion Hac; subst; [ assumption | simpl ].
 destruct ld as [| d]; [ etransitivity; eassumption | idtac ].
 etransitivity; [ eassumption | idtac ].
 constructor; [ rewrite H, fld_add_0_l; reflexivity | idtac ].
 revert H H0; clear; intros.
 revert x ld H.
 induction l as [| y]; intros; [ reflexivity | simpl ].
 destruct ld as [| d]; [ assumption | idtac ].
 constructor.
  inversion H0; subst.
  rewrite H3, fld_add_0_l; reflexivity.

  eapply IHl; [ idtac | eassumption ].
  inversion H0; assumption.

 simpl.
 destruct lb as [| b].
  etransitivity; [ eassumption | idtac ].
  revert Hbd; clear; intros.
  revert lc Hbd.
  induction ld as [| d]; intros.
   simpl.
   destruct lc; reflexivity.

   destruct lc as [| c]; [ assumption | simpl ].
   constructor.
    inversion Hbd; subst.
    rewrite H1, fld_add_0_r; reflexivity.

    apply IHld.
    inversion Hbd; assumption.

  destruct lc as [| c]; simpl.
   destruct ld as [| d].
    constructor.
     inversion Hac; inversion Hbd; subst.
     rewrite H1, fld_add_0_l; assumption.

     inversion Hac; inversion Hbd; subst.
     rewrite IHla; try eassumption; reflexivity.

    constructor.
     inversion Hac; inversion Hbd; subst.
     rewrite H1, fld_add_0_l; assumption.

     inversion Hac; inversion Hbd; subst.
     rewrite IHla; try eassumption; reflexivity.

   destruct ld as [| d].
    constructor.
     inversion Hac; inversion Hbd; subst.
     rewrite H7, fld_add_0_r; assumption.

     inversion Hac; inversion Hbd; subst.
     rewrite IHla; try eassumption.
     destruct lc; reflexivity.

    constructor.
     inversion Hac; inversion Hbd; subst.
     rewrite H2, H8; reflexivity.

     inversion Hac; inversion Hbd; subst.
     apply IHla; assumption.
Qed.

Lemma poly_convol_mul_comm : ∀ α (f : field α) l₁ l₂ i len,
  list_eq f (poly_convol_mul f l₁ l₂ i len) (poly_convol_mul f l₂ l₁ i len).
Proof.
intros α f l₁ l₂ i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite summation_rtl.
apply summation_compat; intros j (_, Hj).
rewrite Nat.add_0_r.
rewrite fld_mul_comm.
apply fld_mul_compat; [ idtac | reflexivity ].
rewrite Nat_sub_sub_distr; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Lemma poly_convol_mul_nil_l : ∀ α (f : field α) l i len,
  list_eq f (poly_convol_mul f [] l i len) [].
Proof.
intros α f l i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite all_0_summation_0; [ reflexivity | idtac ].
intros k (_, Hk).
destruct k; rewrite fld_mul_0_l; reflexivity.
Qed.

Lemma poly_convol_mul_nil_r : ∀ α (f : field α) l i len,
  list_eq f (poly_convol_mul f l [] i len) [].
Proof.
intros α f l i len.
rewrite poly_convol_mul_comm.
apply poly_convol_mul_nil_l.
Qed.

Lemma poly_convol_mul_compat : ∀ α (f : field α) la lb lc ld i len,
  list_eq f la lc
  → list_eq f lb ld
    → list_eq f (poly_convol_mul f la lb i len)
        (poly_convol_mul f lc ld i len).
Proof.
intros α f la lb lc ld i len Hac Hbd.
revert la lb lc ld i Hac Hbd.
induction len; intros; [ reflexivity | simpl ].
constructor.
 apply summation_compat; intros j (_, Hj).
 apply fld_mul_compat.
  clear Hj; revert j.
  induction Hac; intros.
   reflexivity.

   destruct j; [ assumption | apply IHHac ].

   destruct j; [ assumption | simpl; rewrite IHHac ].
   destruct j; reflexivity.

   symmetry.
   destruct j; [ assumption | simpl; rewrite <- IHHac ].
   destruct j; reflexivity.

  remember (i - j)%nat as k; clear Heqk; revert k.
  induction Hbd; intros.
   reflexivity.

   destruct k; [ assumption | apply IHHbd ].

   destruct k; [ assumption | simpl; rewrite IHHbd ].
   destruct k; reflexivity.

   symmetry.
   destruct k; [ assumption | simpl; rewrite <- IHHbd ].
   destruct k; reflexivity.

 apply IHlen; assumption.
Qed.

Add Parametric Morphism α (f : field α) : (poly_mul f)
  with signature (eq_poly f) ==> (eq_poly f) ==> (eq_poly f)
  as ps_poly_mul_morph.
Proof.
intros a c Hac b d Hbd.
unfold eq_poly, poly_mul; simpl.
inversion Hac; subst.
 do 2 rewrite poly_convol_mul_nil_l; reflexivity.

 inversion Hbd.
  do 2 rewrite poly_convol_mul_nil_r; reflexivity.

  simpl.
  constructor.
   do 2 rewrite summation_only_one.
   rewrite H1, H5; reflexivity.
bbb.

intros a c Hac b d Hbd.
unfold eq_poly, poly_mul; simpl.
inversion Hac; subst.
 inversion Hbd; simpl.
  reflexivity.

  constructor.
   do 2 rewrite summation_only_one.
   do 2 rewrite fld_mul_0_l; reflexivity.

   apply poly_convol_mul_nil_l.

  constructor.
   rewrite all_0_summation_0; [ reflexivity | idtac ].
   intros k (_, Hk).
   destruct k; rewrite fld_mul_0_l; reflexivity.

   clear.
bbb.

intros a c Hac b d Hbd.
unfold eq_poly, poly_mul; simpl.
erewrite list_eq_length_eq; [ idtac | eassumption ].
rewrite Nat.max_comm; symmetry.
rewrite Nat.max_comm; symmetry.
erewrite list_eq_length_eq; [ idtac | eassumption ].
apply poly_convol_mul_compat; assumption.
Qed.

Section poly.

Variable α : Type.
Variable f : field α.

Lemma list_eq_append_one : ∀ x₁ x₂ l₁ l₂,
  list_eq f l₁ l₂ ∧ (x₁ .= f x₂)%K
  → list_eq f (l₁ ++ [x₁]) (l₂ ++ [x₂]).
Proof.
intros x₁ x₂ l₁ l₂.
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

(* addition theorems *)

Theorem poly_add_compat : ∀ a b c d,
  (a .= f c)%pol
  → (b .= f d)%pol
    → (a .+ f b .= f c .+ f d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Lemma poly_add_loop_al_comm : ∀ al₁ al₂ rp₁ rp₂,
  rp₁ = poly_add_loop f al₁ al₂
  → rp₂ = poly_add_loop f al₂ al₁
    → list_eq f rp₁ rp₂.
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

Theorem poly_add_comm : ∀ pol₁ pol₂, (pol₁ .+ f pol₂ .= f pol₂ .+ f pol₁)%pol.
Proof.
intros pol₁ pol₂.
unfold eq_poly.
eapply poly_add_loop_al_comm; reflexivity.
Qed.

Lemma poly_add_loop_al_assoc : ∀ al₁ al₂ al₃ rp₁ rp₂,
  rp₁ = poly_add_loop f (poly_add_loop f al₁ al₂) al₃
  → rp₂ = poly_add_loop f al₁ (poly_add_loop f al₂ al₃)
    → list_eq f rp₁ rp₂.
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
eapply poly_add_loop_al_assoc; reflexivity.
Qed.

(* multiplication theorems *)

Theorem poly_mul_compat : ∀ a b c d,
  (a .= f c)%pol
  → (b .= f d)%pol
    → (a .* f b .= f c .* f d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Theorem poly_mul_1_l : ∀ a, (a .* f .1 f .= f a)%pol.
Proof.
intros a.
unfold eq_poly; simpl.
remember (al a) as cl eqn:Hcl .
symmetry in Hcl.
destruct cl as [| c].
 simpl.
bbb.

End poly.

(* Horner's algorithm *)
Definition apply_poly α β γ
    (zero_c : α) (add_v_c : α → β → α) (mul_v_x : α → γ → α)
    (pol : polynomial β) (x : γ) :=
  List.fold_right (λ c accu, add_v_c (mul_v_x accu x) c) zero_c (al pol).
