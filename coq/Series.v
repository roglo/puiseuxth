(* $Id: Series.v,v 2.47 2013-11-25 13:28:46 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Nbar.

Set Implicit Arguments.

Record series α :=
  { terms : nat → α;
    stop : Nbar }.

Definition series_nth α n (s : series α) :=
  match stop s with
  | fin st => if lt_dec n st then Some (terms s n) else None
  | ∞ => Some (terms s n)
  end.

Definition series_nth_fld α fld n (s : series α) :=
  if Nbar.lt_dec (fin n) (stop s) then terms s n else Field.zero fld.

Definition series_inf α fld (a : series α) :=
  {| terms i := series_nth_fld fld i a; stop := ∞ |}.

Theorem stop_0_series_nth_None : ∀ α (s : series α),
  stop s = 0%Nbar → series_nth 0 s = None.
Proof.
intros α s Hs.
unfold series_nth.
rewrite Hs; reflexivity.
Qed.

Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%nat (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%nat (at level 70, y at next level).

Section field.
 
Variable α : Type.
Variable fld : Field.t α.
Notation "a ≍ b" := (Field.eq fld a b) (at level 70).
Notation "a ≭ b" := (not (Field.eq fld a b)) (at level 70).

Delimit Scope fld_scope with fld.
Notation "0" := (Field.zero fld) : fld_scope.
Notation "1" := (Field.one fld) : fld_scope.
Notation "a + b" := (Field.add fld a b)
  (left associativity, at level 50) : fld_scope.
Notation "a * b" := (Field.mul fld a b)
  (left associativity, at level 40) : fld_scope.

Definition series_0 := {| terms i := Field.zero fld; stop := 0 |}.
Definition series_1 := {| terms i := Field.one fld; stop := 1 |}.

Inductive eq_series : series α → series α → Prop :=
  eq_series_base : ∀ s₁ s₂,
    (∀ i, series_nth_fld fld i s₁ ≍ series_nth_fld fld i s₂)
    → eq_series s₁ s₂.

Notation "a ≃ b" := (eq_series a b) (at level 70).

Theorem eq_series_refl : reflexive _ eq_series.
Proof.
intros s.
constructor; reflexivity.
Qed.

Theorem eq_series_sym : symmetric _ eq_series.
Proof.
intros s₁ s₂ H.
inversion H; subst.
constructor.
intros i; symmetry; apply H0.
Qed.

Theorem eq_series_trans : transitive _ eq_series.
Proof.
intros s₁ s₂ s₃ H₁ H₂.
inversion H₁; inversion H₂; subst.
constructor.
etransitivity; [ apply H | apply H2 ].
Qed.

(* *)

Lemma series_inf_eq : ∀ a, a ≃ series_inf fld a.
Proof.
intros a.
constructor; intros i.
unfold series_nth_fld; simpl.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin i) ∞) as [H₁| H₁]; [ reflexivity | idtac ].
exfalso; apply H₁; constructor.
Qed.

(* series_add *)

Definition series_add s₁ s₂ :=
  {| terms i :=
       Field.add fld (series_nth_fld fld i s₁) (series_nth_fld fld i s₂);
     stop :=
       Nbar.max (stop s₁) (stop s₂) |}.

Definition series_opp s :=
  {| terms i := Field.opp fld (terms s i); stop := stop s |}.

Theorem series_add_comm : ∀ s₁ s₂,
  series_add s₁ s₂ ≃ series_add s₂ s₁.
Proof.
intros s₁ s₂.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.max_comm.
destruct (Nbar.max (stop s₂) (stop s₁)) as [n| ].
 destruct (Nbar.lt_dec (fin i) (fin n)) as [Hlt| ]; [ idtac | reflexivity ].
 rewrite Field.add_comm; reflexivity.

 destruct (Nbar.lt_dec (fin i) ∞); [ idtac | reflexivity ].
 rewrite Field.add_comm; reflexivity.
Qed.

Theorem series_add_assoc : ∀ s₁ s₂ s₃,
  series_add s₁ (series_add s₂ s₃) ≃ series_add (series_add s₁ s₂) s₃.
Proof.
intros s₁ s₂ s₃.
unfold series_add; simpl.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.max_assoc.
remember (Nbar.lt_dec (fin i) (stop s₁)) as lt₁.
remember (Nbar.lt_dec (fin i) (stop s₂)) as lt₂.
remember (Nbar.lt_dec (fin i) (stop s₃)) as lt₃.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂))) as lt₄.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))) as lt₅.
clear Heqlt₁ Heqlt₂ Heqlt₃ Heqlt₄ Heqlt₅.
remember (Nbar.max (Nbar.max (stop s₁) (stop s₂)) (stop s₃)) as n.
destruct (Nbar.lt_dec (fin i) n) as [Hlt| ]; [ subst n | reflexivity ].
destruct lt₄ as [Hlt₄| Hge₄].
 destruct lt₅ as [Hlt₅| Hge₅].
  destruct lt₁ as [Hlt₁| Hge₁].
   destruct lt₂ as [Hlt₂| Hge₂].
    destruct lt₃ as [Hlt₃| Hge₃]; [ apply Field.add_assoc | idtac ].
    rewrite Field.add_0_r; symmetry.
    rewrite <- Field.add_assoc.
    rewrite Field.add_0_r; reflexivity.

    rewrite <- Field.add_assoc, Field.add_0_l; reflexivity.

   rewrite <- Field.add_assoc, Field.add_0_l; reflexivity.

  rewrite Field.add_0_r; symmetry.
  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₅; clear Hge₅.
   apply Nbar.max_lt_iff; left; assumption.

   rewrite <- Field.add_assoc, Field.add_0_l.
   destruct lt₃ as [Hlt₃| Hge₃].
    exfalso; apply Hge₅; clear Hge₅.
    apply Nbar.max_lt_iff; right; assumption.

    rewrite Field.add_0_r; reflexivity.

 rewrite Field.add_0_l.
 destruct lt₁ as [Hlt₁| Hge₁].
  exfalso; apply Hge₄; clear Hge₄.
  apply Nbar.max_lt_iff; left; assumption.

  rewrite Field.add_0_l.
  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₄; clear Hge₄.
   apply Nbar.max_lt_iff; right; assumption.

   destruct lt₅ as [Hlt₅| Hge₅].
    rewrite Field.add_0_l; reflexivity.

    destruct lt₃ as [Hlt₃| Hge₃]; [ idtac | reflexivity ].
    exfalso; apply Hge₅; clear Hge₅.
    apply Nbar.max_lt_iff; right; assumption.
Qed.

Lemma stop_series_add_0_l : ∀ s, stop (series_add series_0 s) = stop s.
Proof.
intros s; simpl.
destruct (stop s); reflexivity.
Qed.

Lemma series_nth_series_0 : ∀ i, series_nth_fld fld i series_0 ≍ Field.zero fld.
Proof.
intros i.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin i) 0); reflexivity.
Qed.

Theorem series_add_0_l : ∀ s, series_add series_0 s ≃ s.
Proof.
intros s.
constructor; intros i.
unfold series_nth_fld.
rewrite stop_series_add_0_l; simpl.
remember (Nbar.lt_dec (fin i) (stop s)) as d.
destruct d as [H₁| H₁]; [ idtac | reflexivity ].
rewrite series_nth_series_0.
rewrite Field.add_0_l.
unfold series_nth_fld.
rewrite <- Heqd; reflexivity.
Qed.

Theorem series_add_opp : ∀ s, series_add s (series_opp s) ≃ series_0.
Proof.
intros s.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.max_id.
destruct (Nbar.lt_dec (fin i) 0) as [H₁| H₁].
 exfalso; revert H₁; apply Nbar.nlt_0_r.

 clear H₁.
 unfold series_nth_fld; simpl.
 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₁| H₁]; [ idtac | reflexivity ].
 apply Field.add_opp_r.
Qed.

(* series_mul *)

Definition δ i j := if eq_nat_dec i j then Field.one fld else Field.zero fld.

Fixpoint sigma_aux b len f :=
  match len with
  | O => f b
  | S len₁ => (f b + sigma_aux (S b) len₁ f)%fld
  end.

Definition sigma b e f := sigma_aux b (e - b) f.

Notation "'Σ' ( i = b , e ) ' ' f" := (sigma b e (λ i, f))
  (at level 0, i at level 0, b at level 0, e at level 0, f at level 60).

Definition convol_mul a b k :=
  Σ (i = 0, k)   Σ (j = 0, k)  
    (Field.mul fld (δ (i + j) k)
       (Field.mul fld (series_nth_fld fld i a) (series_nth_fld fld j b))).

Definition series_mul a b :=
  {| terms k := convol_mul a b k;
     stop := Nbar.add (stop a) (stop b) |}.

Lemma sigma_aux_compat : ∀ f g b len,
  (∀ i, f i ≍ g i)
  → sigma_aux b len f ≍ sigma_aux b len g.
Proof.
intros f g b len Hfg.
revert b.
induction len; intros; [ apply Hfg | simpl; rewrite Hfg ].
rewrite IHlen; reflexivity.
Qed.

Lemma sigma_compat : ∀ f g k,
  (∀ i, f i ≍ g i)
  → Σ (i = 0, k)  f i ≍ Σ (i = 0, k)   g i.
Proof.
intros f g k Hfg.
apply sigma_aux_compat; assumption.
Qed.

Lemma sigma_sigma_compat : ∀ f g k,
  (∀ i j, f i j ≍ g i j)
  → Σ (i = 0, k)   Σ (j = 0, k)   f i j ≍ Σ (i = 0, k)   Σ (j = 0, k)   g i j.
Proof.
intros f g k Hfg.
unfold sigma.
apply sigma_aux_compat; intros l.
apply sigma_aux_compat; intros m.
apply Hfg.
Qed.

Lemma all_0_sigma_aux_0 : ∀ f b len,
  (∀ i, (b ≤ i ≤ b + len)%nat → f i ≍ 0%fld)
  → sigma_aux b len (λ i, f i) ≍ 0%fld.
Proof.
intros f b len H.
revert b H.
induction len; intros; simpl.
 apply H.
 rewrite Nat.add_0_r; split; reflexivity.

 rewrite H, Field.add_0_l.
  apply IHlen.
  intros i (Hbi, Hib).
  apply H.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l.
  split; [ idtac | assumption ].
  apply Nat.lt_le_incl; assumption.

  split; [ reflexivity | idtac ].
  apply Nat.le_add_r.
Qed.

Lemma all_0_sigma_0 : ∀ f i₁ i₂,
  (∀ i, f i ≍ 0%fld) → Σ (i = i₁, i₂)   f i ≍ 0%fld.
Proof.
intros f i₁ i₂ H.
apply all_0_sigma_aux_0.
intros; apply H.
Qed.

Lemma delta_id : ∀ i, δ i i ≍ 1%fld.
Proof.
intros i; unfold δ.
destruct (eq_nat_dec i i) as [H₁| H₁]; [ reflexivity | idtac ].
exfalso; apply H₁; reflexivity.
Qed.

Lemma delta_neq : ∀ i j, i ≠ j → δ i j ≍ 0%fld.
Proof.
intros i j Hij; unfold δ.
destruct (eq_nat_dec i j) as [H₁| H₁]; [ subst i | reflexivity ].
exfalso; apply Hij; reflexivity.
Qed.

End field.

Add Parametric Relation α (fld : Field.t α) : (series α) (eq_series fld)
 reflexivity proved by (eq_series_refl fld)
 symmetry proved by (eq_series_sym (fld := fld))
 transitivity proved by (eq_series_trans (fld := fld))
 as eq_series_rel.

Add Parametric Morphism α (fld : Field.t α) : (series_mul fld)
with signature eq_series fld ==> eq_series fld ==> eq_series fld
as series_mul_morph.
Proof.
intros a b Hab c d Hcd.
constructor.
intros i.
inversion Hab; subst.
inversion Hcd; subst.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin i) (stop a + stop c)) as [H₁| H₁].
 destruct (Nbar.lt_dec (fin i) (stop b + stop d)) as [H₂| H₂].
  unfold convol_mul.
  rename i into k.
  apply sigma_compat; intros i.
  apply sigma_compat; intros j.
  rewrite H, H0.
  reflexivity.

  unfold convol_mul.
  rename i into k.
  apply all_0_sigma_0; intros i.
  apply all_0_sigma_0; intros j.
  destruct (eq_nat_dec (i + j)%nat k) as [H₃| H₃].
   rewrite H₃, delta_id, Field.mul_1_l, H, H0.
   unfold series_nth_fld; simpl.
   destruct (Nbar.lt_dec (fin i) (stop b)) as [H₄| H₄].
    destruct (Nbar.lt_dec (fin j) (stop d)) as [H₅| H₅].
     exfalso; apply H₂.
     rewrite <- H₃.
     rewrite Nbar.fin_inj_add.
     remember (stop b) as st eqn:Hst .
     symmetry in Hst.
     destruct st as [st| ]; [ idtac | constructor ].
     apply Nbar.lt_trans with (m := (fin st + fin j)%Nbar).
      apply Nbar.add_lt_mono_r; [ idtac | assumption ].
      intros HH; discriminate HH.

      apply Nbar.add_lt_mono_l; [ idtac | assumption ].
      intros HH; discriminate HH.

     rewrite Field.mul_0_r; reflexivity.

    rewrite Field.mul_0_l; reflexivity.

   rewrite delta_neq; [ idtac | assumption ].
   rewrite Field.mul_0_l; reflexivity.

 destruct (Nbar.lt_dec (fin i) (stop b + stop d)) as [H₂| H₂].
  unfold convol_mul.
  rename i into k.
  symmetry.
  apply all_0_sigma_0; intros i.
  apply all_0_sigma_0; intros j.
  destruct (eq_nat_dec (i + j)%nat k) as [H₃| H₃].
   rewrite H₃, delta_id, Field.mul_1_l, <- H, <- H0.
   unfold series_nth_fld; simpl.
   destruct (Nbar.lt_dec (fin i) (stop a)) as [H₄| H₄].
    destruct (Nbar.lt_dec (fin j) (stop c)) as [H₅| H₅].
     exfalso; apply H₁.
     rewrite <- H₃.
     rewrite Nbar.fin_inj_add.
     remember (stop a) as st eqn:Hst .
     symmetry in Hst.
     destruct st as [st| ]; [ idtac | constructor ].
     apply Nbar.lt_trans with (m := (fin st + fin j)%Nbar).
      apply Nbar.add_lt_mono_r; [ idtac | assumption ].
      intros HH; discriminate HH.

      apply Nbar.add_lt_mono_l; [ idtac | assumption ].
      intros HH; discriminate HH.

     rewrite Field.mul_0_r; reflexivity.

    rewrite Field.mul_0_l; reflexivity.

   rewrite delta_neq; [ idtac | assumption ].
   rewrite Field.mul_0_l; reflexivity.

  reflexivity.
Qed.

Section field₂.
 
Variable α : Type.
Variable fld : Field.t α.
Notation "a ≍ b" := (Field.eq fld a b) (at level 70).
Notation "a ≭ b" := (not (Field.eq fld a b)) (at level 70).

Delimit Scope fld_scope with fld.
Notation "0" := (Field.zero fld) : fld_scope.
Notation "1" := (Field.one fld) : fld_scope.
Notation "a + b" := (Field.add fld a b)
  (left associativity, at level 50) : fld_scope.
Notation "a * b" := (Field.mul fld a b)
  (left associativity, at level 40) : fld_scope.

Notation "a ≃ b" := (eq_series fld a b) (at level 70).

Notation "'Σ' ( i = b , e ) ' ' f" := (sigma fld b e (λ i, f))
  (at level 0, i at level 0, b at level 0, e at level 0, f at level 60).

Lemma sigma_aux_sigma_aux_comm : ∀ f g i di j dj,
  (∀ i j, f i j ≍ g i j)
  → sigma_aux fld i di (λ i, sigma_aux fld j dj (λ j, f i j))
    ≍ sigma_aux fld j dj (λ j, sigma_aux fld i di (λ i, g i j)).
Proof.
intros f g i di j dj Hfg.
revert i.
induction di; intros; simpl.
 revert j.
 induction dj; intros; [ apply Hfg | simpl ].
 rewrite Hfg, IHdj; reflexivity.

 rewrite IHdi; clear IHdi.
 revert j.
 induction dj; intros; simpl.
  rewrite Hfg; reflexivity.

  rewrite Hfg.
  rewrite <- IHdj.
  rewrite Field.add_assoc, Field.add_comm; symmetry.
  rewrite Field.add_assoc, Field.add_comm; symmetry.
  rewrite Field.add_shuffle0; reflexivity.
Qed.

Lemma sigma_sigma_comm : ∀ f g i₁ i₂ j₁ j₂,
  (∀ i j, f i j ≍ g i j)
  → Σ (i = i₁, i₂)   Σ (j = j₁, j₂)   (f i j)
    ≍ Σ (j = j₁, j₂)   Σ (i = i₁, i₂)   (g i j).
Proof.
intros f g i₁ i₂ j₁ j₂ Hfg.
apply sigma_aux_sigma_aux_comm; assumption.
Qed.

Theorem series_mul_comm : ∀ a b, series_mul fld a b ≃ series_mul fld b a.
Proof.
intros a b.
constructor; intros k.
unfold series_nth_fld; simpl.
rewrite Nbar.add_comm.
destruct (Nbar.lt_dec (fin k) (stop b + stop a)) as [H₁| H₁].
 unfold convol_mul.
 apply sigma_sigma_comm.
 intros i j.
 rewrite Nat.add_comm.
 do 2 rewrite Field.mul_assoc.
 rewrite Field.mul_shuffle0; reflexivity.

 reflexivity.
Qed.

Lemma stop_series_mul_0_l : ∀ s,
  stop (series_mul fld (series_0 fld) s) = stop s.
Proof.
intros s; simpl.
destruct (stop s); reflexivity.
Qed.

Theorem series_mul_0_l : ∀ s, series_mul fld (series_0 fld) s ≃ series_0 fld.
Proof.
intros s.
constructor; intros i.
unfold series_nth_fld.
rewrite stop_series_mul_0_l; simpl.
destruct (Nbar.lt_dec (fin i) (stop s)) as [H₁| H₁].
 unfold convol_mul.
 rename i into k.
 destruct (Nbar.lt_dec (fin k) 0) as [H₂| H₂].
  apply Nbar.nle_gt in H₂.
  exfalso; apply H₂, Nbar.le_0_l.

  apply all_0_sigma_0; intros i.
  apply all_0_sigma_0; intros j.
  rewrite Field.mul_assoc, Field.mul_shuffle0.
  rewrite Field.mul_comm.
  rewrite series_nth_series_0.
  rewrite Field.mul_0_l.
  reflexivity.

 destruct (Nbar.lt_dec (fin i) 0); reflexivity.
Qed.

Lemma delta_0_succ : ∀ i, δ fld 0 (S i) ≍ 0%fld.
Proof.
intros i; unfold δ.
destruct (eq_nat_dec 0 (S i)) as [H₁|]; [ discriminate H₁ | reflexivity ].
Qed.

Lemma sigma_mul_sigma : ∀ f g k,
  Σ (i = 0, k)   Σ (j = 0, k)   (δ fld (i + j) k * (f i * g i j))%fld
  ≍ Σ (i = 0, k)   (f i * Σ (j = 0, k)   δ fld (i + j) k * g i j)%fld.
Proof.
intros f g k.
apply sigma_compat; intros i.
unfold sigma.
remember (k - 0)%nat as len; clear Heqlen.
remember 0%nat as b; clear Heqb.
revert b k.
induction len; intros; simpl.
 rewrite Field.mul_assoc, Field.mul_shuffle0, Field.mul_comm.
 reflexivity.

 rewrite IHlen.
 rewrite Field.mul_assoc, Field.mul_shuffle0, Field.mul_comm.
 rewrite Field.mul_add_distr_l.
 reflexivity.
Qed.

Lemma sigma_only_one_non_0 : ∀ f b v k,
  (b ≤ v ≤ k)%nat
  → (∀ i, (i ≠ v)%nat → f i ≍ 0)%fld
    → Σ (i = b, k)   f i ≍ f v.
Proof.
intros f b v k (Hbv, Hvk) Hi.
unfold sigma.
remember (k - b)%nat as len.
replace k with (b + len)%nat in * by omega.
clear k Heqlen.
revert b v Hbv Hvk Hi.
induction len; intros; simpl.
 rewrite Nat.add_0_r in Hvk.
 apply Nat.le_antisymm in Hvk; [ idtac | assumption ].
 subst b; reflexivity.

 destruct (eq_nat_dec b v) as [H₁| H₁].
  subst b.
  assert (f v ≍ f v + 0)%fld as H.
   rewrite Field.add_0_r; reflexivity.

   rewrite H in |- * at 2.
   apply Field.add_compat_l.
   clear IHlen Hbv Hvk H.
   apply all_0_sigma_aux_0.
   intros i (Hvi, Hiv).
   apply Hi.
   intros H; subst i.
   apply Nat.nlt_ge in Hvi.
   apply Hvi, Nat.lt_succ_r; reflexivity.

  rewrite Hi; [ idtac | assumption ].
  rewrite Field.add_0_l.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hvk.
  apply IHlen; [ idtac | assumption | assumption ].
  apply Nat.nlt_ge.
  intros H; apply H₁.
  apply Nat.succ_le_mono in H.
  apply Nat.le_antisymm; assumption.
Qed.

Theorem series_mul_1_l : ∀ s, series_mul fld (series_1 fld) s ≃ s.
Proof.
intros s.
constructor; intros i.
unfold series_nth_fld; simpl.
remember (stop s) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ].
 destruct (Nbar.lt_dec (fin i) (fin st)) as [H₁| H₁].
  destruct (Nbar.lt_dec (fin i) (fin (S st))) as [H₂| H₂].
   unfold convol_mul.
   rename i into k.
   rewrite sigma_mul_sigma.
   rewrite sigma_only_one_non_0 with (v := O).
    simpl.
    unfold series_nth_fld at 1; simpl.
    destruct (Nbar.lt_dec 0 1) as [H₃| H₃].
     rewrite Field.mul_1_l.
     rewrite sigma_only_one_non_0 with (v := k).
      rewrite delta_id, Field.mul_1_l.
      unfold series_nth_fld.
      rewrite <- Hst in H₁.
      destruct (Nbar.lt_dec (fin k) (stop s)); [ idtac | contradiction ].
      reflexivity.

      split; [ apply Nat.le_0_l | reflexivity ].

      intros i Hik.
      rewrite delta_neq; [ idtac | assumption ].
      apply Field.mul_0_l.

     exfalso; apply H₃, Nbar.lt_0_1.

    split; [ reflexivity | apply Nat.le_0_l ].

    intros i Hi.
    unfold series_nth_fld at 1; simpl.
    destruct (Nbar.lt_dec (fin i) 1) as [H₃| H₃].
     apply Nbar.fin_lt_mono in H₃.
     apply Nat.lt_1_r in H₃; contradiction.

     apply Field.mul_0_l.

   exfalso; apply H₂.
   eapply Nbar.lt_trans; [ eassumption | idtac ].
   apply Nbar.lt_fin, Nat.lt_succ_r; reflexivity.

  destruct (Nbar.lt_dec (fin i) (fin (S st))) as [H₂| H₂].
   unfold convol_mul.
   rename i into k.
   apply all_0_sigma_0; intros i.
   apply all_0_sigma_0; intros j.
   destruct i; simpl.
    unfold series_nth_fld; simpl.
    destruct (Nbar.lt_dec (fin j) (stop s)) as [H₃| H₃].
     unfold δ.
     destruct (eq_nat_dec j k) as [H₄| H₄].
      subst j.
      rewrite Hst in H₃; contradiction.

      rewrite Field.mul_0_l; reflexivity.

     rewrite Field.mul_assoc, Field.mul_0_r; reflexivity.

    unfold series_nth_fld; simpl.
    destruct (Nbar.lt_dec (fin (S i)) 1) as [H₃| H₃].
     apply Nbar.nle_gt in H₃.
     exfalso; apply H₃.
     apply Nbar.fin_le_mono, le_n_S, Nat.le_0_l.

     rewrite Field.mul_0_l, Field.mul_0_r; reflexivity.

   reflexivity.

 destruct (Nbar.lt_dec (fin i) ∞) as [H₁| ]; [ idtac | reflexivity ].
 unfold convol_mul.
 rename i into k.
 rewrite sigma_mul_sigma.
 rewrite sigma_only_one_non_0 with (v := O).
  simpl.
  unfold series_nth_fld at 1; simpl.
  destruct (Nbar.lt_dec 0 1) as [H₃| H₃].
   rewrite Field.mul_1_l.
   rewrite sigma_only_one_non_0 with (v := k).
    rewrite delta_id, Field.mul_1_l.
    unfold series_nth_fld.
    rewrite <- Hst in H₁.
    destruct (Nbar.lt_dec (fin k) (stop s)); [ idtac | contradiction ].
    reflexivity.

    split; [ apply Nat.le_0_l | reflexivity ].

    intros i Hik.
    rewrite delta_neq; [ idtac | assumption ].
    apply Field.mul_0_l.

   exfalso; apply H₃, Nbar.lt_0_1.

  split; [ reflexivity | apply Nat.le_0_l ].

  intros i Hi.
  unfold series_nth_fld at 1; simpl.
  destruct (Nbar.lt_dec (fin i) 1) as [H₃| H₃].
   apply Nbar.fin_lt_mono in H₃.
   apply Nat.lt_1_r in H₃; contradiction.

   apply Field.mul_0_l.
Qed.

Lemma mul_sigma_aux_inj : ∀ f a b len,
  (a * sigma_aux fld b len (λ i, f i))%fld
   ≍ sigma_aux fld b len (λ i, (a * f i)%fld).
Proof.
intros f a b len.
revert b.
induction len; intros; [ reflexivity | simpl ].
rewrite Field.mul_add_distr_l.
rewrite IHlen; reflexivity.
Qed.

Lemma mul_sigma_inj : ∀ f i₁ i₂ a,
  (a * Σ (i = i₁, i₂)   f i ≍ Σ (i = i₁, i₂)   a * f i)%fld.
Proof.
intros f i₁ i₂ a.
apply mul_sigma_aux_inj.
Qed.

Lemma sigma_aux_extend_0 : ∀ f b len₁ len₂,
  len₁ ≤ len₂
  → (∀ i, b + len₁ < i ≤ b + len₂ → f i ≍ 0%fld)
    → sigma_aux fld b len₁ (λ i, f i)
      ≍ sigma_aux fld b len₂ (λ i, f i).
Proof.
intros f b len₁ len₂ Hlen Hi.
revert b len₁ Hlen Hi.
induction len₂; intros; simpl.
 apply le_n_0_eq in Hlen; subst len₁; reflexivity.

 destruct len₁; simpl.
  rewrite all_0_sigma_aux_0.
   rewrite Field.add_0_r; reflexivity.

   intros i H.
   apply Hi; omega.

  apply Nat.succ_le_mono in Hlen.
  apply Field.add_compat_l.
  apply IHlen₂; [ assumption | idtac ].
  intros i H.
  apply Hi; omega.
Qed.

Lemma sigma_extend_0 : ∀ f i₁ i₂ i₃,
  i₂ ≤ i₃
  → (∀ i, i₂ < i ≤ i₃ → f i ≍ 0%fld)
    → Σ (i = i₁, i₂)   f i ≍ Σ (i = i₁, i₃)   f i.
Proof.
intros f i₁ i₂ i₃ Hi₂₃ Hi.
apply sigma_aux_extend_0; [ omega | idtac ].
intros i (Hi₁, Hi₂).
apply Hi; omega.
Qed.

Lemma series_inf_nth : ∀ s t i,
  s = series_inf fld t
  → series_nth_fld fld i s ≍ terms s i.
Proof.
intros s t i Hs.
subst s; simpl.
unfold series_nth_fld; simpl.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin i) ∞) as [| H]; [ reflexivity | idtac ].
exfalso; apply H; constructor.
Qed.

(* à faire, s'il le faut
Lemma sigma_sigma_compat : ∀ f g k,
  (∀ i j, f i j ≍ g i j)
  → Σ (i = 0, k)   Σ (j = 0, k)   f i j ≍
    Σ (i = 0, k)   Σ (j = 0, k)   g i j.
Proof.
bbb.
*)

Definition convol_mul_inf a b k :=
  Σ (i = 0, k)   Σ (j = 0, k)  
    (δ fld (i + j) k * terms a i * terms b j)%fld.

Definition series_mul_inf a b :=
  {| terms k := convol_mul_inf a b k; stop := ∞ |}.

Lemma series_mul_mul_inf : ∀ a b,
  series_mul fld a b
  ≃ series_mul_inf (series_inf fld a) (series_inf fld b).
Proof.
intros a b.
constructor; intros k.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin k) ∞) as [H₁| H₁]; [ idtac | exfalso ].
 clear H₁.
 destruct (Nbar.lt_dec (fin k) (stop a + stop b)) as [H₁| H₁].
  unfold convol_mul, convol_mul_inf.
  apply sigma_compat; intros i.
  apply sigma_compat; intros j.
  rewrite <- Field.mul_assoc.
  apply Field.mul_compat_l; reflexivity.

  unfold convol_mul_inf.
  symmetry; unfold convol_mul_inf; simpl.
  apply all_0_sigma_0; intros i.
  apply all_0_sigma_0; intros j.
  unfold series_nth_fld.
  destruct (Nbar.lt_dec (fin i) (stop a)) as [H₂| H₂].
   destruct (Nbar.lt_dec (fin j) (stop b)) as [H₃| H₃].
    destruct (eq_nat_dec (i + j) k) as [H₄| H₄].
     rewrite H₄, delta_id, Field.mul_1_l.
     exfalso; apply H₁; subst k.
     rewrite Nbar.fin_inj_add.
     remember (stop a) as st eqn:Hst .
     symmetry in Hst.
     destruct st as [st| ]; [ idtac | constructor ].
     apply Nbar.lt_trans with (m := (fin st + fin j)%Nbar).
      apply Nbar.add_lt_mono_r; [ idtac | assumption ].
      intros HH; discriminate HH.

      apply Nbar.add_lt_mono_l; [ idtac | assumption ].
      intros HH; discriminate HH.

     rewrite delta_neq; [ idtac | assumption ].
     do 2 rewrite Field.mul_0_l; reflexivity.

    rewrite Field.mul_0_r; reflexivity.

   rewrite Field.mul_0_r, Field.mul_0_l; reflexivity.

 apply H₁; constructor.
Qed.

Lemma series_inf_mul : ∀ a b,
  series_inf fld (series_mul fld a b)
  ≃ series_mul_inf (series_inf fld a) (series_inf fld b).
Proof.
intros a b.
rewrite <- series_mul_mul_inf.
rewrite <- series_inf_eq.
reflexivity.
Qed.

Lemma series_nth_mul_inf : ∀ a b i,
  series_nth_fld fld i (series_mul_inf a b)
  ≍ terms (series_mul_inf a b) i.
Proof.
intros a b i.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin i) ∞) as [| H]; [ reflexivity | idtac ].
exfalso; apply H; constructor.
Qed.

Definition sigma_mul_3 aa bb cc m :=
  Σ (i = 0, m)  
  Σ (j = 0, m)  
  Σ (k = 0, m)  
    (δ fld (i + j + k) m * terms aa i * terms bb j * terms cc k)%fld.

Lemma zzz : ∀ aa bb cc m,
  Σ (i = 0, m)  
  Σ (l = 0, m)  
   (δ fld (i + l) m * terms aa i *
    Σ (j = 0, l)  
    Σ (k = 0, l)   δ fld (j + k) l * terms bb j * terms cc k)%fld
  ≍ sigma_mul_3 aa bb cc m.
Proof.
bbb.
*)

Theorem series_mul_assoc : ∀ a b c,
  series_mul fld a (series_mul fld b c)
  ≃ series_mul fld (series_mul fld a b) c.
Proof.
(* expérimentation *)
intros a b c.
pose proof (series_mul_mul_inf b c) as H.
rewrite H; clear H.
pose proof (series_mul_mul_inf a b) as H.
rewrite H; clear H.
rewrite series_mul_mul_inf; symmetry.
rewrite series_mul_mul_inf; symmetry.
remember (series_inf fld a) as aa eqn:Haa .
remember (series_inf fld b) as bb eqn:Hbb .
remember (series_inf fld c) as cc eqn:Hcc .
constructor; intros k.
do 2 rewrite series_nth_mul_inf; simpl.
unfold convol_mul_inf; simpl.
remember
 (λ i j, (δ fld (i + j) k * terms aa i * terms (series_mul_inf bb cc) j)%fld) as f.
rewrite sigma_sigma_compat with (g := f); subst f.
 Focus 2.
 intros i j; rewrite series_nth_mul_inf; reflexivity.

 symmetry.
 remember
  (λ i j, (δ fld (i + j) k * terms (series_mul_inf aa bb) i * terms cc j)%fld) as f.
 rewrite sigma_sigma_compat with (g := f); subst f.
  Focus 2.
  intros i j; rewrite series_nth_mul_inf; reflexivity.

  symmetry.
  unfold series_mul_inf; simpl.
  unfold convol_mul_inf.
  rewrite zzz.
  symmetry.
bbb.

(* version classique *)
intros a b c.
assert (a ≃ series_inf fld a) as H by apply series_inf_eq.
rewrite H; clear H.
assert (b ≃ series_inf fld b) as H by apply series_inf_eq.
rewrite H; clear H.
assert (c ≃ series_inf fld c) as H by apply series_inf_eq.
rewrite H; clear H.
remember (series_inf fld a) as aa eqn:Haa .
remember (series_inf fld b) as bb eqn:Hbb .
remember (series_inf fld c) as cc eqn:Hcc .
constructor; intros k.
unfold series_nth_fld; simpl.
rewrite Nbar.add_assoc.
destruct (Nbar.lt_dec (fin k) (stop aa + stop bb + stop cc)) as [H₁| H₁].
 unfold convol_mul; simpl.
bbb.

intros a b c.
bbb.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.add_assoc.
destruct (Nbar.lt_dec (fin i) (stop a + stop b + stop c)) as [H₁| H₁].
 rename i into k.
bbb.
 apply sigma_compat; intros i.
 apply sigma_compat; intros j.
 destruct (eq_nat_dec (i + j) k) as [H₂| H₂].
  Focus 2.
  rewrite delta_neq; [ idtac | assumption ].
  do 2 rewrite Field.mul_0_l; reflexivity.

  rewrite H₂, delta_id.
  do 2 rewrite Field.mul_1_l.
bbb.
  unfold series_nth_fld; simpl.
  destruct (Nbar.lt_dec (fin i) (stop a)) as [H₃| H₃].
   destruct (Nbar.lt_dec (fin i) (stop a + stop b)) as [H₄| H₄].
    destruct (Nbar.lt_dec (fin j) (stop b + stop c)) as [H₅| H₅].
     destruct (Nbar.lt_dec (fin j) (stop c)) as [H₆| H₆].
      clear H₄ H₅.
bbb.
      unfold convol_mul.
      rename i into i₁.
      rename j into j₁.
      rewrite mul_sigma_inj, Field.mul_comm, mul_sigma_inj.
      rewrite sigma_extend_0 with (i₃ := k).
       symmetry.
       rewrite sigma_extend_0 with (i₃ := k).
        symmetry.
        apply sigma_compat; intros i₂.
        do 2 rewrite mul_sigma_inj.
        rewrite sigma_extend_0 with (i₃ := k).
         symmetry.
         rewrite sigma_extend_0 with (i₃ := k).
          Focus 1.
bbb.
          rewrite sigma_only_one_non_0 with (v := (i₁ - i₂)%nat).
           rewrite sigma_only_one_non_0 with (v := (j₁ - i₂)%nat).
            Focus 1.
            destruct (le_dec i₂ i₁) as [H₇| H₇].
             rewrite <- le_plus_minus; [ idtac | assumption ].
             rewrite delta_id, Field.mul_1_l.
             destruct (le_dec i₂ j₁) as [H₈| H₈].
              rewrite <- le_plus_minus; [ idtac | assumption ].
              rewrite delta_id, Field.mul_1_l.
              Unfocus.
              Unfocus.
              4: omega.

              11: omega.

             12: omega.

            9: omega.

            5: omega.
bbb.

End field.

Notation "a ≍ b" := (Field.eq _ a b) (at level 70).
Notation "a ≭ b" := (not (Field.eq _ a b)) (at level 70).

Add Parametric Morphism α (fld : Field.t α) : (series_add fld) with 
signature eq_series fld ==> eq_series fld ==> eq_series fld
as series_add_morph.
Proof.
intros s₁ s₂ Heq₁ s₃ s₄ Heq₂.
inversion Heq₁; subst.
inversion Heq₂; subst.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
unfold series_nth_fld in H; simpl in H.
unfold series_nth_fld in H0; simpl in H0.
pose proof (H i) as Hi₁.
pose proof (H0 i) as Hi₂.
clear H H0.
unfold series_nth_fld.
remember (Nbar.lt_dec (fin i) (stop s₁)) as lt₁.
remember (Nbar.lt_dec (fin i) (stop s₂)) as lt₂.
remember (Nbar.lt_dec (fin i) (stop s₃)) as lt₃.
remember (Nbar.lt_dec (fin i) (stop s₄)) as lt₄.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₃))) as lt₅.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₄))) as lt₆.
clear Heqlt₁ Heqlt₂ Heqlt₃ Heqlt₄ Heqlt₅ Heqlt₆.
move Hi₁ at bottom.
move Hi₂ at bottom.
destruct lt₅ as [Hlt₅| Hge₅].
 rewrite Hi₁, Hi₂.
 destruct lt₆ as [Hlt₆| Hge₆]; [ reflexivity | idtac ].
 destruct lt₂ as [Hlt₂| Hge₂].
  exfalso; apply Hge₆; clear Hge₆.
  apply Nbar.max_lt_iff; left; assumption.

  destruct lt₄ as [Hlt₄| Hge₄].
   exfalso; apply Hge₆; clear Hge₆.
   apply Nbar.max_lt_iff; right; assumption.

   rewrite Field.add_0_l; reflexivity.

 destruct lt₁ as [Hlt₁| Hge₁].
  exfalso; apply Hge₅; clear Hge₅.
  apply Nbar.max_lt_iff; left; assumption.

  destruct lt₃ as [Hlt₃| Hge₃].
   exfalso; apply Hge₅; clear Hge₅.
   apply Nbar.max_lt_iff; right; assumption.

   destruct lt₆ as [Hlt₆| Hge₆]; [ idtac | reflexivity ].
   rewrite <- Hi₁, <- Hi₂.
   rewrite Field.add_0_l; reflexivity.
Qed.

Add Parametric Morphism α (fld : Field.t α) i : (series_nth_fld fld i) with 
signature (eq_series fld) ==> (Field.eq fld) as series_nth_fld_morph.
Proof.
intros s₁ s₂ Heq.
inversion Heq; subst.
apply H.
Qed.
