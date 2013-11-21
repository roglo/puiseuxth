(* $Id: Series.v,v 2.11 2013-11-21 23:44:54 deraugla Exp $ *)

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
  if Nbar.lt_dec (fin n) (stop s) then terms s n else zero fld.

Theorem stop_0_series_nth_None : ∀ α (s : series α),
  stop s = 0%Nbar → series_nth 0 s = None.
Proof.
intros α s Hs.
unfold series_nth.
rewrite Hs; reflexivity.
Qed.

Section field.
 
Variable α : Type.
Variable fld : field α.
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).

Delimit Scope fld_scope with fld.
Notation "0" := (zero fld) : fld_scope.
Notation "a + b" :=
  (add fld a b) (left associativity, at level 50) : fld_scope.

Definition series_0 := {| terms i := zero fld; stop := 0 |}.
Definition series_1 := {| terms i := one fld; stop := 1 |}.

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

(* series_add *)

Definition series_add s₁ s₂ :=
  {| terms i := add fld (series_nth_fld fld i s₁) (series_nth_fld fld i s₂);
     stop := Nbar.max (stop s₁) (stop s₂) |}.

Definition series_opp s :=
  {| terms i := opp fld (terms s i); stop := stop s |}.

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
 rewrite fld_add_comm; reflexivity.

 destruct (Nbar.lt_dec (fin i) ∞); [ idtac | reflexivity ].
 rewrite fld_add_comm; reflexivity.
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
    destruct lt₃ as [Hlt₃| Hge₃]; [ apply fld_add_assoc | idtac ].
    rewrite fld_add_0_r; symmetry.
    rewrite <- fld_add_assoc.
    rewrite fld_add_0_r; reflexivity.

    rewrite <- fld_add_assoc, fld_add_0_l; reflexivity.

   rewrite <- fld_add_assoc, fld_add_0_l; reflexivity.

  rewrite fld_add_0_r; symmetry.
  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₅; clear Hge₅.
   apply Nbar.max_lt_iff; left; assumption.

   rewrite <- fld_add_assoc, fld_add_0_l.
   destruct lt₃ as [Hlt₃| Hge₃].
    exfalso; apply Hge₅; clear Hge₅.
    apply Nbar.max_lt_iff; right; assumption.

    rewrite fld_add_0_r; reflexivity.

 rewrite fld_add_0_l.
 destruct lt₁ as [Hlt₁| Hge₁].
  exfalso; apply Hge₄; clear Hge₄.
  apply Nbar.max_lt_iff; left; assumption.

  rewrite fld_add_0_l.
  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₄; clear Hge₄.
   apply Nbar.max_lt_iff; right; assumption.

   destruct lt₅ as [Hlt₅| Hge₅].
    rewrite fld_add_0_l; reflexivity.

    destruct lt₃ as [Hlt₃| Hge₃]; [ idtac | reflexivity ].
    exfalso; apply Hge₅; clear Hge₅.
    apply Nbar.max_lt_iff; right; assumption.
Qed.

Lemma stop_series_add_0_l : ∀ s, stop (series_add series_0 s) = stop s.
Proof.
intros s; simpl.
destruct (stop s); reflexivity.
Qed.

Lemma series_nth_series_0 : ∀ i, series_nth_fld fld i series_0 ≍ zero fld.
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
rewrite fld_add_0_l.
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
 apply fld_add_opp_diag_r.
Qed.

(* series_mul *)

Definition δ i j := if eq_nat_dec i j then one fld else zero fld.

Fixpoint sigma_aux b len f :=
  match len with
  | O => f b
  | S len₁ => (f b + sigma_aux (S b) len₁ f)%fld
  end.

Definition sigma b e f := sigma_aux b (e - b) f.

Notation "'Σ' ( i = b ) ' ' e f" := (sigma b e (λ i, f))
  (at level 0, i at level 0, b at level 0, e at level 0, f at level 10).

Definition convol_mul a b k :=
  Σ (i = 0)   k Σ (j = 0)   k
    (mul fld (δ (i + j) k)
       (mul fld (series_nth_fld fld i a) (series_nth_fld fld j b))).

Definition series_mul a b :=
  {| terms k := convol_mul a b k;
     stop := Nbar.add (stop a) (stop b) |}.

Lemma sigma_aux_sigma_aux_comm : ∀ f g i di j dj,
  (∀ i j, f i j ≍ g i j)
  → sigma_aux i di (λ i, sigma_aux j dj (λ j, f i j))
    ≍ sigma_aux j dj (λ j, sigma_aux i di (λ i, g i j)).
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
  rewrite fld_add_assoc, fld_add_comm; symmetry.
  rewrite fld_add_assoc, fld_add_comm; symmetry.
  rewrite fld_add_shuffle0; reflexivity.
Qed.

Lemma sigma_sigma_comm : ∀ f g i₁ i₂ j₁ j₂,
  (∀ i j, f i j ≍ g i j)
  → Σ (i = i₁)   i₂ Σ (j = j₁)   j₂ (f i j)
    ≍ Σ (j = j₁)   j₂ Σ (i = i₁)   i₂ (g i j).
Proof.
intros f g i₁ i₂ j₁ j₂ Hfg.
apply sigma_aux_sigma_aux_comm; assumption.
Qed.

Theorem series_mul_comm : ∀ a b, series_mul a b ≃ series_mul b a.
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
 do 2 rewrite fld_mul_assoc.
 rewrite fld_mul_shuffle0; reflexivity.

 reflexivity.
Qed.

Lemma stop_series_mul_0_l : ∀ s, stop (series_mul series_0 s) = stop s.
Proof.
intros s; simpl.
destruct (stop s); reflexivity.
Qed.

Lemma all_0_sigma_0 : ∀ f i₁ i₂,
  (∀ i, f i ≍ 0%fld) → Σ (i = i₁)   i₂ f i ≍ 0%fld.
Proof.
intros f i₁ i₂ H.
unfold sigma.
remember (i₂ - i₁)%nat as len.
clear i₂ Heqlen.
revert i₁.
induction len; intros; [ apply H | simpl ].
rewrite H, fld_add_0_l.
apply IHlen.
Qed.

Theorem series_mul_0_l : ∀ s, series_mul series_0 s ≃ series_0.
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
  rewrite fld_mul_assoc, fld_mul_shuffle0.
  rewrite fld_mul_comm.
  rewrite series_nth_series_0.
  rewrite fld_mul_0_l.
  reflexivity.

 destruct (Nbar.lt_dec (fin i) 0); reflexivity.
Qed.

Theorem series_mul_1_l : ∀ s, series_mul series_1 s ≃ s.
Proof.
intros s.
constructor; intros i.
unfold series_nth_fld.
destruct (Nbar.lt_dec (fin i) (stop (series_mul series_1 s))) as [H₁| H₁].
 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₂| H₂].
  simpl.
  unfold convol_mul, sigma.
  rewrite Nat.sub_0_r.
  destruct i; simpl.
   unfold δ; simpl.
   rewrite fld_mul_1_l.
   unfold series_nth_fld; simpl.
   destruct (Nbar.lt_dec 0 1) as [H₃| H₃].
    destruct (Nbar.lt_dec 0 (stop s)) as [H₄| H₄]; [ idtac | contradiction ].
    rewrite fld_mul_1_l; reflexivity.

    exfalso; apply H₃, Nbar.lt_0_1.

   destruct i.
    simpl; unfold δ; simpl.
    do 2 rewrite fld_mul_1_l.
    rewrite fld_mul_0_l, fld_add_0_l.
    rewrite fld_mul_0_l, fld_add_0_r.
    unfold series_nth_fld; simpl.
    destruct (Nbar.lt_dec 0 1) as [H₃| H₃].
     rewrite fld_mul_1_l.
     destruct (Nbar.lt_dec 1 (stop s)) as [H₄| H₄]; [ idtac | contradiction ].
     destruct (Nbar.lt_dec 1 1) as [H₅| H₅].
      exfalso; revert H₅; apply Nbar.lt_irrefl.

      rewrite fld_mul_0_l, fld_add_0_r.
      reflexivity.

     exfalso; apply H₃, Nbar.lt_0_1.
bbb.
*)

End field.

Notation "a ≍ b" := (fld_eq _ a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq _ a b)) (at level 70).

Add Parametric Relation α (fld : field α) : (series α) (eq_series fld)
 reflexivity proved by (eq_series_refl fld)
 symmetry proved by (eq_series_sym (fld := fld))
 transitivity proved by (eq_series_trans (fld := fld))
 as eq_series_rel.

Add Parametric Morphism α (fld : field α) : (series_add fld) with 
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

   rewrite fld_add_0_l; reflexivity.

 destruct lt₁ as [Hlt₁| Hge₁].
  exfalso; apply Hge₅; clear Hge₅.
  apply Nbar.max_lt_iff; left; assumption.

  destruct lt₃ as [Hlt₃| Hge₃].
   exfalso; apply Hge₅; clear Hge₅.
   apply Nbar.max_lt_iff; right; assumption.

   destruct lt₆ as [Hlt₆| Hge₆]; [ idtac | reflexivity ].
   rewrite <- Hi₁, <- Hi₂.
   rewrite fld_add_0_l; reflexivity.
Qed.

Add Parametric Morphism α (fld : field α) i : (series_nth_fld fld i) with 
signature (eq_series fld) ==> (fld_eq fld) as series_nth_fld_morph.
Proof.
intros s₁ s₂ Heq.
inversion Heq; subst.
apply H.
Qed.
