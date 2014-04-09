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

Notation "s .[ i ]" := (@terms _ s i) (at level 1).

Definition series_0 {α} {r : ring α} :=
  {| terms i := 0%K |}.

Definition series_const α (r : ring α) c :=
  {| terms i := if zerop i then c else 0%K |}.
Definition series_1 {α} {r : ring α} :=
  series_const r (1%K).

Delimit Scope series_scope with ser.
Notation "0" := series_0 : series_scope.
Notation "1" := series_1 : series_scope.

Inductive eq_series {α} {r : ring α} :
    power_series α → power_series α → Prop :=
  eq_series_base : ∀ s₁ s₂,
    (∀ i, (s₁.[i] = s₂.[i])%K)
    → eq_series s₁ s₂.

Notation "a = b" := (eq_series a b) : series_scope.
Notation "a ≠ b" := (¬ eq_series a b) : series_scope.

Theorem eq_series_refl {α} {r : ring α} : reflexive _ eq_series.
Proof.
intros s.
constructor; reflexivity.
Qed.

Theorem eq_series_sym {α} {r : ring α} : symmetric _ eq_series.
Proof.
intros s₁ s₂ H.
inversion H; subst.
constructor.
intros i; symmetry; apply H0.
Qed.

Theorem eq_series_trans {α} {r : ring α} : transitive _ eq_series.
Proof.
intros s₁ s₂ s₃ H₁ H₂.
inversion H₁; inversion H₂; subst.
constructor.
etransitivity; [ apply H | apply H2 ].
Qed.

Add Parametric Relation α (r : ring α) : (power_series α) eq_series
 reflexivity proved by eq_series_refl
 symmetry proved by (eq_series_sym (r := r))
 transitivity proved by (eq_series_trans (r := r))
 as eq_series_rel.

(* *)

Lemma fold_series_const : ∀ α (r : ring α) c,
  {| terms := λ i, if zerop i then c else 0%K |} =
  series_const r c.
Proof. reflexivity. Qed.

(* series_add *)

Definition series_add {α} {r : ring α} s₁ s₂ :=
  {| terms i := (s₁.[i] + s₂.[i])%K |}.

Definition series_opp {α} {r : ring α} s :=
  {| terms i := (- s.[i])%K |}.

Notation "a + b" := (series_add a b) : series_scope.
Notation "a - b" := (series_add a (series_opp b)) : series_scope.
Notation "- a" := (series_opp a) : series_scope.

Section theorems_add.

Variable α : Type.
Variable r : ring α.

Theorem series_add_comm : ∀ s₁ s₂, (s₁ + s₂ = s₂ + s₁)%ser.
Proof.
intros s₁ s₂.
constructor; intros i; simpl.
rewrite rng_add_comm; reflexivity.
Qed.

Theorem series_add_assoc : ∀ s₁ s₂ s₃,
  (s₁ + (s₂ + s₃) = (s₁ + s₂) + s₃)%ser.
Proof.
intros s₁ s₂ s₃.
unfold series_add; simpl.
constructor; intros i; simpl.
rewrite rng_add_assoc; reflexivity.
Qed.

Lemma series_nth_series_0 : ∀ i, (0%ser .[i])%K = 0%K.
Proof. reflexivity. Qed.

Theorem series_add_0_l : ∀ s, (0 + s = s)%ser.
Proof.
intros s.
constructor; intros i; simpl.
rewrite rng_add_0_l; reflexivity.
Qed.

Theorem series_add_opp_r : ∀ s, (s - s = 0)%ser.
Proof.
intros s.
constructor; intros i; simpl.
apply rng_add_opp_r.
Qed.

Theorem series_add_opp_l : ∀ s, (- s + s = 0)%ser.
Proof.
intros s.
rewrite series_add_comm.
apply series_add_opp_r.
Qed.

End theorems_add.

(* series_mul *)

Definition convol_mul {α} {r : ring α} a b k :=
  Σ r (i = 0, k), a.[i] * b.[k-i].

Definition series_mul {α} {r : ring α} a b :=
  {| terms k := convol_mul a b k |}.

Notation "a * b" := (series_mul a b) : series_scope.

Add Parametric Morphism α (R : ring α) : series_mul
  with signature eq_series ==> eq_series ==> eq_series
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
Variable r : ring α.

Theorem convol_mul_comm : ∀ a b i,
  (convol_mul a b i = convol_mul b a i)%K.
Proof.
intros a b k.
unfold convol_mul.
rewrite summation_rtl.
apply summation_compat; intros i Hi.
rewrite Nat.add_0_r.
rewrite Nat_sub_sub_distr; [ idtac | destruct Hi; auto ].
rewrite Nat.add_comm, Nat.add_sub, rng_mul_comm; reflexivity.
Qed.

Theorem series_mul_comm : ∀ a b, (a * b = b * a)%ser.
Proof.
intros a b.
constructor; intros k; simpl.
apply convol_mul_comm.
Qed.

Theorem convol_mul_0_l : ∀ a i, (convol_mul 0%ser a i = 0)%K.
Proof.
intros a k.
unfold convol_mul.
apply all_0_summation_0; intros i Hi.
rewrite series_nth_series_0.
rewrite rng_mul_0_l; reflexivity.
Qed.

Theorem series_mul_0_l : ∀ s, (0 * s = 0)%ser.
Proof.
intros s.
constructor; intros k.
unfold series_mul; simpl.
apply convol_mul_0_l.
Qed.

Theorem series_mul_1_l : ∀ s, (1 * s = s)%ser.
Proof.
intros s.
constructor; intros k; simpl.
unfold convol_mul; simpl.
rewrite summation_only_one_non_0 with (v := O).
 rewrite Nat.sub_0_r; simpl.
 apply rng_mul_1_l.

 split; [ reflexivity | apply Nat.le_0_l ].

 intros i Hik Hi.
 destruct i; [ exfalso; apply Hi; reflexivity | simpl ].
 apply rng_mul_0_l.
Qed.

Theorem series_mul_1_r : ∀ s, (s * 1 = s)%ser.
Proof.
intros s.
rewrite series_mul_comm.
apply series_mul_1_l.
Qed.

Theorem series_mul_assoc : ∀ a b c,
  (a * (b * c) = (a * b) * c)%ser.
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
rewrite rng_mul_comm, rng_mul_assoc.
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm, Nat.sub_add_distr.
reflexivity.
Qed.

Lemma series_nth_add : ∀ a b i,
  (((a + b)%ser) .[i] = a.[i] + b.[i])%K.
Proof. reflexivity. Qed.

Lemma convol_mul_add_distr_l : ∀ a b c i,
  (convol_mul a (b + c)%ser i = convol_mul a b i + convol_mul a c i)%K.
Proof.
intros a b c k.
unfold convol_mul.
rewrite <- summation_add_distr.
apply summation_compat; intros i Hi.
rewrite series_nth_add.
rewrite rng_mul_add_distr_l.
reflexivity.
Qed.

Theorem series_mul_add_distr_l : ∀ a b c,
  (a * (b + c) = a * b + a * c)%ser.
Proof.
intros a b c.
constructor; intros k; simpl.
apply convol_mul_add_distr_l.
Qed.

End misc_lemmas.

Add Parametric Morphism α (R : ring α) : series_add
  with signature eq_series ==> eq_series ==> eq_series
  as series_add_morph.
Proof.
intros s₁ s₂ Heq₁ s₃ s₄ Heq₂.
inversion Heq₁; subst.
inversion Heq₂; subst.
constructor; intros i; simpl.
rewrite H, H0; reflexivity.
Qed.

Add Parametric Morphism α (R : ring α) : (@terms α)
  with signature eq_series ==> eq ==> rng_eq
  as series_nth_morph.
Proof.
intros s₁ s₂ Heq i.
inversion Heq; subst.
apply H.
Qed.

Section other_lemmas.

Variable α : Type.
Variable r : ring α.

Theorem series_add_compat_l : ∀ a b c,
  (a = b)%ser
  → (c + a = c + b)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_compat_l : ∀ a b c,
  (a = b)%ser
  → (c * a = c * b)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_compat_r : ∀ a b c,
  (a = b)%ser
  → (a * c = b * c)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_add_distr_r : ∀ a b c,
  ((a + b) * c = a * c + b * c)%ser.
Proof.
intros a b c.
rewrite series_mul_comm, series_mul_add_distr_l.
rewrite series_mul_comm.
apply series_add_compat_l.
apply series_mul_comm.
Qed.

End other_lemmas.

Fixpoint term_inv {α} {r : ring α} {f : field r} c s n :=
  if zerop n then ¹/ (s.[0])%K
  else
   match c with
   | O => 0%K
   | S c₁ =>
       (- ¹/ (s.[0]) *
        Σ r (i = 1, n), s.[i] * term_inv c₁ s (n - i)%nat)%K
   end.

Definition series_inv {α} {r : ring α} {f : field r} s :=
  {| terms i := term_inv (S i) s i |}.

Notation "¹/ a" := (series_inv a) : series_scope.

Section lemmas_again.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Lemma term_inv_iter_enough : ∀ a i j k,
  k ≤ i → k ≤ j → (term_inv i a k = term_inv j a k)%K.
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
   apply rng_mul_compat_l.
   apply summation_compat; intros l (Hl, Hlj).
   apply rng_mul_compat_l.
   destruct l.
    apply Nat.nle_gt in Hl.
    exfalso; apply Hl; reflexivity.

    apply IHi; omega.
Qed.

Lemma term_inv_nth_gen_formula : ∀ k a a' i,
  (a.[0] ≠ 0)%K
  → a' = series_inv a
    → (S k - i ≠ 0)%nat
      → (a'.[S k - i] =
         - a'.[0] *
         Σ R (j = 1, S k - i),
         a.[j] * term_inv (S k) a (S k - i - j))%K.
Proof.
(* à revoir... *)
intros k a a' i Ha Ha' Hki.
rewrite Ha'.
remember minus as g; simpl; subst g.
destruct (zerop (S k - i)) as [| H₁]; [ contradiction | idtac ].
remember (S k - i)%nat as ki eqn:Hki₂.
destruct ki.
 exfalso; apply Hki; reflexivity.

 clear H₁.
 apply rng_mul_compat_l.
 apply summation_compat; intros j Hj.
 apply rng_mul_compat_l.
 remember minus as g; simpl; subst g.
 destruct (zerop (S ki - j)) as [H₁| H₁].
  reflexivity.

  apply rng_mul_compat_l.
  apply summation_compat; intros l Hl.
  apply rng_mul_compat_l.
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
  (a.[0] ≠ 0)%K
  → a' = series_inv a
    → (a'.[S k] =
       - a'.[0] * Σ R (i = 1, S k), a.[i] * a'.[S k - i])%K.
Proof.
intros k a a' Ha Ha'.
pose proof (term_inv_nth_gen_formula k O Ha Ha') as H.
rewrite Nat.sub_0_r in H.
rewrite H; [ idtac | intros HH; discriminate HH ].
apply rng_mul_compat_l.
apply summation_compat; intros i Hi.
apply rng_mul_compat_l.
rewrite Ha'.
remember minus as g; simpl; subst g.
destruct (zerop (S k - i)) as [H₂| H₂].
 reflexivity.

 apply rng_mul_compat_l.
 apply summation_compat; intros j Hj.
 apply rng_mul_compat_l.
 apply term_inv_iter_enough; fast_omega Hj.
Qed.

Lemma convol_mul_inv_r : ∀ k a a',
  (a.[0] ≠ 0)%K
  → a' = series_inv a
    → (convol_mul a a' (S k) = 0)%K.
Proof.
intros k a a' Ha Ha'.
unfold convol_mul.
pose proof (term_inv_nth_formula k Ha Ha') as Hi.
apply rng_mul_compat_l with (c := a.[0]%K) in Hi.
symmetry in Hi.
rewrite rng_mul_assoc in Hi.
rewrite rng_mul_opp_r in Hi.
rewrite Ha' in Hi.
assert (a.[0] * (¹/ a%ser) .[ 0] = 1)%K as H.
 simpl; rewrite fld_mul_inv_r; [ reflexivity | auto ].

 rewrite H in Hi; clear H.
 rewrite rng_mul_opp_l, rng_mul_1_l in Hi.
 rewrite <- Ha' in Hi.
 eapply rng_add_compat_r in Hi.
 rewrite rng_add_opp_l in Hi.
 symmetry in Hi.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite Nat.sub_0_r; auto.
Qed.

Theorem series_mul_inv_r : ∀ a,
  (a.[0] ≠ 0)%K
  → (a * ¹/ a = 1)%ser.
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
  (a.[0] ≠ 0)%K
  → (¹/ a * a = 1)%ser.
Proof.
intros a Ha.
rewrite series_mul_comm.
apply series_mul_inv_r.
assumption.
Qed.

Theorem series_mul_integral : ∀ a b,
  (a * b = 0)%ser → (a = 0)%ser ∨ (b = 0)%ser.
Proof.
intros a b Hab.
assert (∀ i, (a .[ i] = 0)%K \/ (b .[ i] = 0)%K) as HH.
 intros n.
 induction n using all_lt_all.
 apply rng_mul_integral.
 inversion Hab; subst.
 simpl in H0.
 unfold convol_mul in H0.
 pose proof (H0 n) as Hn.
 destruct n.
  unfold summation in Hn; simpl in Hn.
  rewrite rng_add_0_r in Hn.
  assumption.

  rewrite summation_split_last in Hn.
   rewrite Nat.sub_diag in Hn.
   rewrite summation_split_first in Hn.
    rewrite Nat.sub_0_r in Hn.
    assert (0 < S n)%nat as Hsn.
     apply Nat.lt_0_succ.

     apply H in Hsn.
     destruct Hsn as [Hsn| Hsn].
      rewrite Hsn in Hn.
      rewrite rng_mul_0_l, rng_add_0_l in Hn.
      rewrite all_0_summation_0 in Hn.
       rewrite rng_add_0_l in Hn.
       apply rng_mul_integral in Hn.
       destruct Hn as [Hn| Hn].
        rewrite Hn, rng_mul_0_l; reflexivity.
bbb.

End lemmas_again.

Definition series_ring α (r : ring α) : ring (power_series α) :=
  {| rng_zero := series_0;
     rng_one := series_1;
     rng_add := series_add;
     rng_mul := series_mul;
     rng_opp := series_opp;
     rng_eq := eq_series;
     rng_eq_refl := eq_series_refl;
     rng_eq_sym := eq_series_sym (r := r);
     rng_eq_trans := eq_series_trans (r := r);
     rng_add_comm := series_add_comm r;
     rng_add_assoc := series_add_assoc r;
     rng_add_0_l := series_add_0_l r;
     rng_add_opp_l := series_add_opp_l r;
     rng_add_compat_l := @series_add_compat_l α r;
     rng_mul_comm := series_mul_comm r;
     rng_mul_assoc := series_mul_assoc r;
     rng_mul_1_l := series_mul_1_l r;
     rng_mul_compat_l := @series_mul_compat_l α r;
     rng_mul_add_distr_l := series_mul_add_distr_l r;
     rng_mul_integral := series_mul_integral (R := r) |}.

Canonical Structure series_ring.
