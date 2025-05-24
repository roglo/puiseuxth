(* Power_series.v *)

From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import QArith.

Require Import RingLike.Core.
Require Import RingLike.IterAdd.
Require Import Misc.
Require Import NbarM.
Require Import Field2.
Require Import Fsummation.

Set Implicit Arguments.

Record power_series α := series { terms : nat → α }.

Notation "s .[[ i ]]" := (@terms _ s i) (at level 1).

Definition series_0 {α} {r : ring_like_op α} :=
  {| terms i := 0%L |}.

Definition series_const α {R : ring_like_op α} c :=
  {| terms i := if zerop i then c else 0%L |}.
Definition series_1 {α} {R : ring_like_op α} :=
  series_const (1%L).

Declare Scope series_scope.
Delimit Scope series_scope with ser.
Notation "0" := series_0 : series_scope.
Notation "1" := series_1 : series_scope.

Inductive eq_series {α} {r : ring_like_op α} :
    power_series α → power_series α → Prop :=
  eq_series_base : ∀ s₁ s₂,
    (∀ i, (s₁.[[i]] = s₂.[[i]])%L)
    → eq_series s₁ s₂.

Notation "a = b" := (eq_series a b) : series_scope.
Notation "a ≠ b" := (¬ eq_series a b) : series_scope.

Theorem eq_series_refl {α} {r : ring_like_op α} : reflexive _ eq_series.
Proof.
intros s.
constructor; reflexivity.
Qed.

Theorem eq_series_sym {α} {r : ring_like_op α} : symmetric _ eq_series.
Proof.
intros s₁ s₂ H.
inversion H; subst.
constructor.
intros i; symmetry; apply H0.
Qed.

Theorem eq_series_trans {α} {r : ring_like_op α} : transitive _ eq_series.
Proof.
intros s₁ s₂ s₃ H₁ H₂.
inversion H₁; inversion H₂; subst.
constructor.
etransitivity; [ apply H | apply H2 ].
Qed.

Add Parametric Relation α (r : ring_like_op α) : (power_series α) eq_series
  reflexivity proved by eq_series_refl
  symmetry proved by (eq_series_sym (r := r))
  transitivity proved by (eq_series_trans (r := r))
  as eq_series_rel.

(* *)

Theorem fold_series_const : ∀ α (r : ring_like_op α) c,
  {| terms := λ i, if zerop i then c else 0%L |} =
  series_const c.
Proof. reflexivity. Qed.

(* series_add *)

Definition series_add {α} {r : ring_like_op α} s₁ s₂ :=
  {| terms i := (s₁.[[i]] + s₂.[[i]])%L |}.

Definition series_opp {α} {r : ring_like_op α} s :=
  {| terms i := (- s.[[i]])%L |}.

Notation "a + b" := (series_add a b) : series_scope.
Notation "a - b" := (series_add a (series_opp b)) : series_scope.
Notation "- a" := (series_opp a) : series_scope.

Section theorems_add.

Variable α : Type.
Variable ro : ring_like_op α.
Variable rp : ring_like_prop α.
Context {Hop : rngl_has_opp α = true}.

Theorem series_add_comm : ∀ s₁ s₂, (s₁ + s₂ = s₂ + s₁)%ser.
Proof.
intros s₁ s₂.
constructor; intros i; simpl.
rewrite rngl_add_comm; reflexivity.
Qed.

Theorem series_add_assoc : ∀ s₁ s₂ s₃,
  (s₁ + (s₂ + s₃) = (s₁ + s₂) + s₃)%ser.
Proof.
intros s₁ s₂ s₃.
unfold series_add; simpl.
constructor; intros i; simpl.
rewrite rngl_add_assoc; reflexivity.
Qed.

Theorem series_nth_series_0 : ∀ i, (0%ser .[[i]])%L = 0%L.
Proof. reflexivity. Qed.

Theorem series_add_0_l : ∀ s, (0 + s = s)%ser.
Proof.
intros s.
constructor; intros i; simpl.
rewrite rngl_add_0_l; reflexivity.
Qed.

Theorem series_add_opp_r : ∀ s, (s - s = 0)%ser.
Proof.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros s.
constructor; intros i; simpl.
rewrite (rngl_add_opp_r Hop).
apply (rngl_sub_diag Hos).
Qed.

Theorem series_add_opp_l : ∀ s, (- s + s = 0)%ser.
Proof.
intros s.
rewrite series_add_comm.
apply series_add_opp_r.
Qed.

End theorems_add.

(* series_mul *)

Definition convol_mul {α} {r : ring_like_op α} a b k :=
  ∑ (i = 0, k), (a.[[i]] * b.[[k-i]])%L.

Definition series_mul {α} {r : ring_like_op α} a b :=
  {| terms k := convol_mul a b k |}.

Notation "a * b" := (series_mul a b) : series_scope.

Global Instance series_mul_morph α (R : ring_like_op α) :
  Proper (eq_series ==> eq_series ==> eq_series) series_mul.
Proof.
intros a b Hab c d Hcd.
constructor; intros k; simpl.
unfold convol_mul.
apply rngl_summation_eq_compat; intros i Hi.
inversion Hab; subst.
inversion Hcd; subst.
rewrite H, H0; reflexivity.
Qed.

Section misc_theorems.

Variable α : Type.
Variable ro : ring_like_op α.
Variable rp : ring_like_prop α.
Context {Hop : rngl_has_opp α = true}.
Context {Hic : rngl_mul_is_comm α = true}.
Context {Hon : rngl_has_1 α = true}.

Theorem convol_mul_comm : ∀ a b i,
  (convol_mul a b i = convol_mul b a i)%L.
Proof.
intros a b k.
unfold convol_mul.
rewrite rngl_summation_rtl.
apply rngl_summation_eq_compat; intros i Hi.
rewrite Nat.add_0_r.
rewrite Nat_sub_sub_distr; [ idtac | destruct Hi; auto ].
now rewrite Nat.add_comm, Nat.add_sub, (rngl_mul_comm Hic).
Qed.

Theorem series_mul_comm : ∀ a b, (a * b = b * a)%ser.
Proof.
intros a b.
constructor; intros k; simpl.
apply convol_mul_comm.
Qed.

Theorem convol_mul_0_l : ∀ a i, (convol_mul 0%ser a i = 0)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros a k.
unfold convol_mul.
apply all_0_rngl_summation_0; intros i Hi.
rewrite series_nth_series_0.
rewrite (rngl_mul_0_l Hos); reflexivity.
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
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros s.
constructor; intros k; simpl.
unfold convol_mul; simpl.
rewrite rngl_summation_split_first; [ | easy ].
rewrite Nat.sub_0_r.
rewrite all_0_rngl_summation_0. {
  rewrite rngl_add_0_r.
  apply (rngl_mul_1_l Hon).
} {
  intros i Hi.
  destruct i; [ easy | cbn ].
  apply (rngl_mul_0_l Hos).
}
Qed.

Theorem series_mul_assoc : ∀ a b c,
  (a * (b * c) = (a * b) * c)%ser.
Proof.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros a b c.
constructor; intros k; simpl.
unfold convol_mul; simpl.
unfold convol_mul; simpl.
symmetry.
(**)
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite (rngl_mul_summation_distr_r Hos).
}
cbn.
rewrite rngl_summation_depend_summation_exch.
apply rngl_summation_eq_compat.
intros i Hi.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  now rewrite <- rngl_mul_assoc.
}
cbn.
rewrite <- (rngl_mul_summation_distr_l Hos).
progress f_equal.
rewrite (rngl_summation_shift i); [ | easy ].
rewrite Nat.sub_diag.
apply rngl_summation_eq_compat.
intros j Hj.
rewrite Nat.add_comm, Nat.add_sub.
progress f_equal.
progress f_equal.
rewrite Nat.add_comm.
apply Nat.sub_add_distr.
Qed.

Theorem series_nth_add : ∀ a b i,
  (((a + b)%ser) .[[i]] = a.[[i]] + b.[[i]])%L.
Proof. reflexivity. Qed.

Theorem convol_mul_add_distr_l : ∀ a b c i,
  (convol_mul a (b + c)%ser i = convol_mul a b i + convol_mul a c i)%L.
Proof.
intros a b c k.
unfold convol_mul.
rewrite <- rngl_summation_add_distr.
apply rngl_summation_eq_compat; intros i Hi.
rewrite series_nth_add.
rewrite rngl_mul_add_distr_l.
reflexivity.
Qed.

Theorem series_mul_add_distr_l : ∀ a b c,
  (a * (b + c) = a * b + a * c)%ser.
Proof.
intros a b c.
constructor; intros k; simpl.
apply convol_mul_add_distr_l.
Qed.

End misc_theorems.

Arguments series_mul_comm {α ro rp} Hic (a b)%_ser.
Arguments series_mul_add_distr_l {α ro rp} (a b c)%_ser.

Global Instance series_add_morph α (R : ring_like_op α) :
  Proper (eq_series ==> eq_series ==> eq_series) series_add.
Proof.
intros s₁ s₂ Heq₁ s₃ s₄ Heq₂.
inversion Heq₁; subst.
inversion Heq₂; subst.
constructor; intros i; simpl.
rewrite H, H0; reflexivity.
Qed.

(*
Global Instance series_nth_morph α (R : ring_like_op α) :
  Proper (eq_series ==> eq ==> rngl_eq) (@terms α).
Proof.
intros s₁ s₂ Heq x y Hxy.
inversion Heq; subst.
apply H.
Qed.
*)

Section other_theorems.

Variable α : Type.
Variable ro : ring_like_op α.
Variable rp : ring_like_prop α.
Context {Hic : rngl_mul_is_comm α = true}.

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

Theorem series_mul_add_distr_r : ∀ a b c,
  ((a + b) * c = a * c + b * c)%ser.
Proof.
intros a b c.
rewrite (series_mul_comm Hic), series_mul_add_distr_l.
rewrite (series_mul_comm Hic).
now rewrite (series_mul_comm Hic b).
Qed.

End other_theorems.

Fixpoint term_inv {α} {r : ring_like_op α} c s n :=
  match n with
  | O => (s.[[0]]⁻¹)%L
  | S n₁ =>
      match c with
      | O => 0%L
      | S c₁ =>
          (- (s.[[0]])⁻¹ *
           ∑ (i = 0, n₁), s.[[S i]] * term_inv c₁ s (n₁ - i)%nat)%L
      end
  end.

Definition series_inv {α} {r : ring_like_op α} s :=
  {| terms i := term_inv (S i) s i |}.

Notation "¹/ a" := (series_inv a) (at level 1) : series_scope.

Section theorems_again.

Variable α : Type.
Variable R : ring_like_op α.

Theorem term_inv_iter_enough : ∀ a i j k,
  k ≤ i → k ≤ j → (term_inv i a k = term_inv j a k)%L.
Proof.
intros a i j k Hki Hkj.
revert j k Hki Hkj.
induction i; intros. {
  apply Nat.le_0_r in Hki; subst k.
  destruct j; reflexivity.
}
simpl.
destruct k; simpl; [ destruct j; reflexivity | ].
destruct j; [ apply Nat.nle_succ_0 in Hkj; contradiction | ].
simpl.
progress f_equal.
apply rngl_summation_eq_compat.
intros l Hl.
progress f_equal.
apply IHi; apply Nat.succ_le_mono; [ fast_omega Hki | fast_omega Hkj ].
Qed.

Theorem term_inv_nth_gen_formula : ∀ k a a' i,
  (a.[[0]] ≠ 0)%L
  → a' = series_inv a
  → (S k - i ≠ 0)%nat
  → (a'.[[S k - i]] =
       - a'.[[0]] *
           ∑ (j = 1, S k - i),
      a.[[j]] * term_inv (S k) a (S k - i - j))%L.
Proof.
(* à revoir... *)
intros k a a' i Ha Ha' Hki.
rewrite Ha'.
remember minus as g; simpl; subst g.
destruct (zerop (S k - i)) as [| H₁]; [ contradiction | idtac ].
remember (S k - i)%nat as ki eqn:Hki₂.
destruct ki; [ exfalso; apply Hki; reflexivity | ].
progress f_equal.
clear H₁.
...
apply rngl_mul_compat_l.
rewrite rngl_summation_succ_succ.
apply rngl_summation_compat; intros j Hj.
apply rngl_mul_compat_l.
remember minus as g; simpl; subst g.
rewrite Nat.sub_succ.
remember (ki - j)%nat as n eqn:Hn.
destruct n; [ reflexivity | ].
apply rngl_mul_compat_l.
apply rngl_summation_compat; intros l Hl.
apply rngl_mul_compat_l.
apply term_inv_iter_enough; [ fast_omega Hl Hn | idtac ].
rewrite <- Nat.sub_succ, Hki₂ in Hn.
rewrite <- Nat.sub_succ, Hn.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_succ_l.
rewrite Nat_sub_sub_comm, Nat.sub_succ.
rewrite <- Nat.sub_add_distr.
apply Nat.le_sub_l.
Qed.

Theorem term_inv_nth_formula : ∀ k a a',
  (a.[[0] ≠ 0)%L
  → a' = series_inv a
  → (a'.[[S k] =
       - a'.[[0] * ∑ (i = 1, S k), a.[[i] * a'.[[S k - i])%L.
Proof.
intros k a a' Ha Ha'.
pose proof (term_inv_nth_gen_formula k O Ha Ha') as H.
rewrite Nat.sub_0_r in H.
rewrite H; [ idtac | intros HH; discriminate HH ].
apply rngl_mul_compat_l.
apply rngl_summation_compat; intros i Hi.
apply rngl_mul_compat_l.
rewrite Ha'.
remember minus as g; simpl; subst g.
remember (S k - i)%nat as n eqn:Hn.
destruct n; [ reflexivity | ].
apply rngl_mul_compat_l.
apply rngl_summation_compat; intros j Hj.
apply rngl_mul_compat_l.
apply term_inv_iter_enough; fast_omega Hn Hj.
Qed.

Theorem convol_mul_inv_r : ∀ k a a',
  (a.[[0] ≠ 0)%L
  → a' = series_inv a
  → (convol_mul a a' (S k) = 0)%L.
Proof.
intros k a a' Ha Ha'.
unfold convol_mul.
pose proof (term_inv_nth_formula k Ha Ha') as Hi.
apply rngl_mul_compat_l with (c := a.[[0]%L) in Hi.
symmetry in Hi.
rewrite rngl_mul_assoc in Hi.
rewrite rngl_mul_opp_r in Hi.
rewrite Ha' in Hi.
assert (a.[[0] * (¹/ a%ser) .[[ 0] = 1)%L as H. {
  simpl; rewrite fld_mul_inv_r; [ reflexivity | auto ].
}
rewrite H in Hi; clear H.
rewrite rngl_mul_opp_l, rngl_mul_1_l in Hi.
rewrite <- Ha' in Hi.
eapply rngl_add_compat_r in Hi.
rewrite rngl_add_opp_l in Hi.
symmetry in Hi.
rewrite rngl_summation_split_first; [ idtac | apply Nat.le_0_l ].
rewrite Nat.sub_0_r; auto.
Qed.

Theorem series_mul_inv_r : ∀ a,
  (a.[[0] ≠ 0)%L
  → (a * ¹/ a = 1)%ser.
Proof.
intros a Ha.
constructor; intros i; simpl.
destruct i; simpl. {
  unfold convol_mul; simpl.
  rewrite rngl_summation_only_one; simpl.
  rewrite fld_mul_inv_r; [ reflexivity | assumption ].
}
apply convol_mul_inv_r; [ assumption | reflexivity ].
Qed.

End theorems_again.

Definition series_ring_like_op α {R : ring_like_op α} : ring_like_op (power_series α) :=
  {| rngl_zero := series_0;
     rngl_one := series_1;
     rngl_add := series_add;
     rngl_mul := series_mul;
     rngl_opp := series_opp;
     rngl_eq := eq_series;
     rngl_eq_refl := eq_series_refl;
     rngl_eq_sym := eq_series_sym (r := R);
     rngl_eq_trans := eq_series_trans (r := R);
     rngl_add_comm := series_add_comm R;
     rngl_add_assoc := series_add_assoc R;
     rngl_add_0_l := series_add_0_l R;
     rngl_add_opp_l := series_add_opp_l R;
     rngl_add_compat_l := @series_add_compat_l α R;
     rngl_mul_comm := series_mul_comm R;
     rngl_mul_assoc := series_mul_assoc R;
     rngl_mul_1_l := series_mul_1_l R;
     rngl_mul_compat_l := @series_mul_compat_l α R;
     rngl_mul_add_distr_l := series_mul_add_distr_l R |}.

Canonical Structure series_ring_like_op.
