(* Power_series.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Nbar.
Require Import Field.
Require Import Fsummation.

Set Implicit Arguments.

Record power_series α := { terms : nat → α }.

Notation "s .[ i ]" := (terms s i) (at level 1).

Definition series_0 α (f : field α) :=
  {| terms i := .0 f%K |}.

Definition series_const α (f : field α) c :=
  {| terms i := if zerop i then c else .0 f%K |}.
Definition series_1 α (f : field α) :=
  series_const f (.1 f%K).

Delimit Scope series_scope with ser.
Notation ".0 f" := (series_0 f) : series_scope.
Notation ".1 f" := (series_1 f) : series_scope.

Inductive eq_series α (f : field α) :
    power_series α → power_series α → Prop :=
  eq_series_base : ∀ s₁ s₂,
    (∀ i, (s₁ .[i] .= f s₂ .[i])%K)
    → eq_series f s₁ s₂.

Notation "a .= f b" := (eq_series f a b) : series_scope.
Notation "a .≠ f b" := (¬ eq_series f a b) : series_scope.

Theorem eq_series_refl α (f : field α) : reflexive _ (eq_series f).
Proof.
intros s.
constructor; reflexivity.
Qed.

Theorem eq_series_sym α (f : field α) : symmetric _ (eq_series f).
Proof.
intros s₁ s₂ H.
inversion H; subst.
constructor.
intros i; symmetry; apply H0.
Qed.

Theorem eq_series_trans α (f : field α) : transitive _ (eq_series f).
Proof.
intros s₁ s₂ s₃ H₁ H₂.
inversion H₁; inversion H₂; subst.
constructor.
etransitivity; [ apply H | apply H2 ].
Qed.

Add Parametric Relation α (f : field α) : (power_series α) (eq_series f)
 reflexivity proved by (eq_series_refl f)
 symmetry proved by (eq_series_sym (f := f))
 transitivity proved by (eq_series_trans (f := f))
 as eq_series_rel.

(* *)

Lemma fold_series_const : ∀ α (f : field α) c,
  {| terms := λ i, if zerop i then c else .0 f%K |} =
  series_const f c.
Proof. reflexivity. Qed.

(* series_add *)

Definition series_add α (f : field α) s₁ s₂ :=
  {| terms i := (s₁ .[i] .+ f s₂ .[i])%K |}.

Definition series_opp α (f : field α) s :=
  {| terms i := (.- f terms s i)%K |}.

Notation "a .+ f b" := (series_add f a b) : series_scope.
Notation "a .- f b" := (series_add f a (series_opp f b)) : series_scope.
Notation ".- f a" := (series_opp f a) : series_scope.

Section theorems_add.

Variable α : Type.
Variable f : field α.

Theorem series_add_comm : ∀ s₁ s₂, (s₁ .+ f s₂ .= f s₂ .+ f s₁)%ser.
Proof.
intros s₁ s₂.
constructor; intros i; simpl.
rewrite fld_add_comm; reflexivity.
Qed.

Theorem series_add_assoc : ∀ s₁ s₂ s₃,
  (s₁ .+ f (s₂ .+ f s₃) .= f (s₁ .+ f s₂) .+ f s₃)%ser.
Proof.
intros s₁ s₂ s₃.
unfold series_add; simpl.
constructor; intros i; simpl.
rewrite fld_add_assoc; reflexivity.
Qed.

Lemma series_nth_series_0 : ∀ i, (.0 f%ser .[i])%K = .0 f%K.
Proof. reflexivity. Qed.

Theorem series_add_0_l : ∀ s, (.0 f .+ f s .= f s)%ser.
Proof.
intros s.
constructor; intros i; simpl.
rewrite fld_add_0_l; reflexivity.
Qed.

Theorem series_add_opp_r : ∀ s, (s .- f s .= f .0 f)%ser.
Proof.
intros s.
constructor; intros i; simpl.
apply fld_add_opp_r.
Qed.

Theorem series_add_opp_l : ∀ s, (.- f s .+ f s .= f .0 f)%ser.
Proof.
intros s.
rewrite series_add_comm.
apply series_add_opp_r.
Qed.

End theorems_add.

(* series_mul *)

Definition convol_mul α (f : field α) a b k :=
  Σ f (i = 0, k), a .[i] .* f b .[k-i].

Definition series_mul α (f : field α) a b :=
  {| terms k := convol_mul f a b k |}.

Notation "a .* f b" := (series_mul f a b) : series_scope.

Add Parametric Morphism α (F : field α) : (series_mul F)
  with signature eq_series F ==> eq_series F ==> eq_series F
  as series_mul_morph.
Proof.
intros a b Hab c d Hcd.
constructor; intros k; simpl.
unfold convol_mul.
apply summation_compat; intros i Hi.
inversion Hab; subst.
inversion Hcd; subst.
rewrite H, H0; reflexivity.
Qed.

Section misc_lemmas.

Variable α : Type.
Variable f : field α.

Theorem convol_mul_comm : ∀ a b i,
  (convol_mul f a b i .= f convol_mul f b a i)%K.
Proof.
intros a b k.
unfold convol_mul.
rewrite summation_rtl.
apply summation_compat; intros i Hi.
rewrite Nat.add_0_r.
rewrite Nat_sub_sub_distr; [ idtac | destruct Hi; auto ].
rewrite Nat.add_comm, Nat.add_sub, fld_mul_comm; reflexivity.
Qed.

Theorem series_mul_comm : ∀ a b, (a .* f b .= f b .* f a)%ser.
Proof.
intros a b.
constructor; intros k; simpl.
apply convol_mul_comm.
Qed.

Theorem convol_mul_0_l : ∀ a i, (convol_mul f .0 f%ser a i .= f .0 f)%K.
Proof.
intros a k.
unfold convol_mul.
apply all_0_summation_0; intros i Hi.
rewrite series_nth_series_0.
rewrite fld_mul_0_l; reflexivity.
Qed.

Theorem series_mul_0_l : ∀ s, (.0 f .* f s .= f .0 f)%ser.
Proof.
intros s.
constructor; intros k.
unfold series_mul; simpl.
apply convol_mul_0_l.
Qed.

Theorem series_mul_1_l : ∀ s, (.1 f .* f s .= f s)%ser.
Proof.
intros s.
constructor; intros k; simpl.
unfold convol_mul; simpl.
rewrite summation_only_one_non_0 with (v := O).
 rewrite Nat.sub_0_r; simpl.
 apply fld_mul_1_l.

 split; [ reflexivity | apply Nat.le_0_l ].

 intros i Hik Hi.
 destruct i; [ exfalso; apply Hi; reflexivity | simpl ].
 apply fld_mul_0_l.
Qed.

Theorem series_mul_1_r : ∀ s, (s .* f .1 f .= f s)%ser.
Proof.
intros s.
rewrite series_mul_comm.
apply series_mul_1_l.
Qed.

Theorem series_mul_assoc : ∀ a b c,
  (a .* f (b .* f c) .= f (a .* f b) .* f c)%ser.
Proof.
intros a b c.
constructor; intros k; simpl.
unfold convol_mul; simpl.
unfold convol_mul; simpl.
symmetry.
rewrite summation_mul_comm.
rewrite <- summation_summation_mul_swap.
rewrite <- summation_summation_mul_swap.
rewrite summation_summation_exch.
rewrite summation_summation_shift.
apply summation_compat; intros i Hi.
apply summation_compat; intros j Hj.
rewrite fld_mul_comm, fld_mul_assoc.
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm, Nat.sub_add_distr.
reflexivity.
Qed.

Lemma series_nth_add : ∀ a b i,
  (((a .+ f b)%ser) .[i] .= f a .[i] .+ f b .[i])%K.
Proof. reflexivity. Qed.

Lemma convol_mul_add_distr_l : ∀ a b c i,
  (convol_mul f a (b .+ f c)%ser i .= f
   convol_mul f a b i .+ f convol_mul f a c i)%K.
Proof.
intros a b c k.
unfold convol_mul.
rewrite <- summation_add_distr.
apply summation_compat; intros i Hi.
rewrite series_nth_add.
rewrite fld_mul_add_distr_l.
reflexivity.
Qed.

Theorem series_mul_add_distr_l : ∀ a b c,
  (a .* f (b .+ f c) .= f a .* f b .+ f a .* f c)%ser.
Proof.
intros a b c.
constructor; intros k; simpl.
apply convol_mul_add_distr_l.
Qed.

End misc_lemmas.

Add Parametric Morphism α (F : field α) : (series_add F)
  with signature eq_series F ==> eq_series F ==> eq_series F
  as series_add_morph.
Proof.
intros s₁ s₂ Heq₁ s₃ s₄ Heq₂.
inversion Heq₁; subst.
inversion Heq₂; subst.
constructor; intros i; simpl.
rewrite H, H0; reflexivity.
Qed.

Add Parametric Morphism α (F : field α) : (@terms α)
  with signature eq_series F ==> eq ==> (fld_eq F)
  as series_nth_morph.
Proof.
intros s₁ s₂ Heq i.
inversion Heq; subst.
apply H.
Qed.

Section other_lemmas.

Variable α : Type.
Variable f : field α.

Theorem series_add_compat_l : ∀ a b c,
  (a .= f b)%ser
  → (c .+ f a .= f c .+ f b)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_compat_l : ∀ a b c,
  (a .= f b)%ser
  → (c .* f a .= f c .* f b)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_compat_r : ∀ a b c,
  (a .= f b)%ser
  → (a .* f c .= f b .* f c)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_add_distr_r : ∀ a b c,
  ((a .+ f b) .* f c .= f a .* f c .+ f b .* f c)%ser.
Proof.
intros a b c.
rewrite series_mul_comm, series_mul_add_distr_l.
rewrite series_mul_comm.
apply series_add_compat_l.
apply series_mul_comm.
Qed.

End other_lemmas.

Fixpoint term_inv α (f : field α) c s n :=
  if zerop n then .¹/f (s .[0])%K
  else
   match c with
   | O => .0 f%K
   | S c₁ =>
       (.-f .¹/f (s .[0]) .* f
        Σ f (i = 1, n), s .[i] .* f term_inv f c₁ s (n - i)%nat)%K
   end.

Definition series_inv α (f : field α) s :=
  {| terms i := term_inv f (S i) s i |}.

Notation ".¹/ f a" := (series_inv f a) : series_scope.

Section lemmas_again.

Variable α : Type.
Variable f : field α.

Lemma term_inv_iter_enough : ∀ a i j k,
  k ≤ i → k ≤ j → (term_inv f i a k .= f term_inv f j a k)%K.
Proof.
intros a i j k Hki Hkj.
revert j k Hki Hkj.
induction i; intros.
 apply Nat.le_0_r in Hki; subst k.
 destruct j; reflexivity.

 simpl.
 destruct k; simpl.
  destruct j; reflexivity.

  destruct j.
   apply Nat.nle_succ_0 in Hkj; contradiction.

   simpl.
   apply fld_mul_compat_l.
   apply summation_compat; intros l (Hl, Hlj).
   apply fld_mul_compat_l.
   destruct l.
    apply Nat.nle_gt in Hl.
    exfalso; apply Hl; reflexivity.

    apply IHi; omega.
Qed.

Lemma term_inv_nth_gen_formula : ∀ k a a' i,
  (a.[0] .≠ f .0 f)%K
  → a' = series_inv f a
    → (S k - i ≠ 0)%nat
      → (a' .[S k - i] .= f
         .- f a' .[0] .* f
         Σ f (j = 1, S k - i),
         a .[j] .* f term_inv f (S k) a (S k - i - j))%K.
Proof.
(* à revoir... *)
intros k a a' i Ha Ha' Hki.
rewrite Ha'.
remember minus as g; simpl; subst g.
destruct (zerop (S k - i)) as [| H₁]; [ contradiction | idtac ].
remember (S k - i)%nat as ki eqn:Hki₂ .
destruct ki.
 exfalso; apply Hki; reflexivity.

 clear H₁.
 apply fld_mul_compat_l.
 apply summation_compat; intros j Hj.
 apply fld_mul_compat_l.
 remember minus as g; simpl; subst g.
 destruct (zerop (S ki - j)) as [H₁| H₁].
  reflexivity.

  apply fld_mul_compat_l.
  apply summation_compat; intros l Hl.
  apply fld_mul_compat_l.
  apply term_inv_iter_enough; [ fast_omega Hl | idtac ].
  rewrite Hki₂.
  destruct Hl as (H, _).
  apply Nat.nle_gt in H.
  destruct l; [ exfalso; apply H, Nat.le_0_l | idtac ].
  do 2 rewrite <- Nat.sub_add_distr.
  do 2 rewrite Nat.add_succ_r.
  rewrite Nat.sub_succ.
  apply Nat.le_sub_l.
Qed.

Lemma term_inv_nth_formula : ∀ k a a',
  (a.[0] .≠ f .0 f)%K
  → a' = series_inv f a
    → (a' .[S k] .= f
       .- f a' .[0] .* f Σ f (i = 1, S k), a .[i] .* f a' .[S k - i])%K.
Proof.
intros k a a' Ha Ha'.
pose proof (term_inv_nth_gen_formula k O Ha Ha') as H.
rewrite Nat.sub_0_r in H.
rewrite H; [ idtac | intros HH; discriminate HH ].
apply fld_mul_compat_l.
apply summation_compat; intros i Hi.
apply fld_mul_compat_l.
rewrite Ha'.
remember minus as g; simpl; subst g.
destruct (zerop (S k - i)) as [H₂| H₂].
 reflexivity.

 apply fld_mul_compat_l.
 apply summation_compat; intros j Hj.
 apply fld_mul_compat_l.
 apply term_inv_iter_enough; fast_omega Hj.
Qed.

Lemma convol_mul_inv_r : ∀ k a a',
  (a.[0] .≠ f .0 f)%K
  → a' = series_inv f a
    → (convol_mul f a a' (S k) .= f .0 f)%K.
Proof.
intros k a a' Ha Ha'.
unfold convol_mul.
pose proof (term_inv_nth_formula k Ha Ha') as Hi.
apply fld_mul_compat_l with (c := a .[0]%K) in Hi.
symmetry in Hi.
rewrite fld_mul_assoc in Hi.
rewrite fld_mul_opp_r in Hi.
rewrite Ha' in Hi.
rewrite fld_mul_inv_r in Hi; auto.
rewrite fld_mul_opp_l, fld_mul_1_l in Hi.
rewrite <- Ha' in Hi.
eapply fld_add_compat_r in Hi.
rewrite fld_add_opp_l in Hi.
symmetry in Hi.
rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
rewrite Nat.sub_0_r; auto.
Qed.

Theorem series_mul_inv_r : ∀ a,
  (a .[0] .≠ f .0 f)%K
  → (a .* f .¹/f a .= f .1 f)%ser.
Proof.
intros a Ha.
constructor; intros i; simpl.
destruct i; simpl.
 unfold convol_mul; simpl.
 rewrite summation_only_one; simpl.
 rewrite fld_mul_inv_r; [ reflexivity | assumption ].

 apply convol_mul_inv_r; [ assumption | reflexivity ].
Qed.

Theorem series_mul_inv_l : ∀ a,
  (a .[0] .≠ f .0 f)%K
  → (.¹/f a .* f a .= f .1 f)%ser.
Proof.
intros a Ha.
rewrite series_mul_comm.
apply series_mul_inv_r.
assumption.
Qed.

End lemmas_again.
