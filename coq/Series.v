(* $Id: Series.v,v 2.109 2013-12-12 13:39:52 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Field.
Module Field_inst : Field.FieldType.
  Parameter α : Type.
  Parameter fld : Field.Tdef.f α.
  Let rng := Field.Tdef.ring fld.
End Field_inst.
Module Lfield := Field.Make Field_inst.
Export Field_inst.
Export Lfield.Syntax.


Require Import Nbar.

Set Implicit Arguments.

Record series α :=
  { terms : nat → α;
    stop : Nbar }.

Definition series_nth_opt α n (s : series α) :=
  match stop s with
  | fin st => if lt_dec n st then Some (terms s n) else None
  | ∞ => Some (terms s n)
  end.

Definition series_nth α rng n (s : series α) :=
  if Nbar.lt_dec (fin n) (stop s) then terms s n else Field.Tdef.zero rng.

Definition series_inf α fld (a : series α) :=
  {| terms i := series_nth fld i a; stop := ∞ |}.

Theorem stop_0_series_nth_None : ∀ α (s : series α),
  stop s = 0%Nbar → series_nth_opt 0 s = None.
Proof.
intros α s Hs.
unfold series_nth_opt.
rewrite Hs; reflexivity.
Qed.

Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%nat (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%nat (at level 70, y at next level).
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat (at level 70, y at next level).

Definition series_0 := {| terms i := Lfield.zero rng; stop := 0 |}.
Definition series_1 := {| terms i := Lfield.one rng; stop := 1 |}.
Definition series_const (c : α) := {| terms i := c; stop := 1 |}.

Inductive eq_series : series α → series α → Prop :=
  eq_series_base : ∀ s₁ s₂,
    (∀ i, (series_nth rng i s₁ = series_nth rng i s₂)%rng)
    → eq_series s₁ s₂.

Delimit Scope series_scope with ser.

Notation "0" := series_0 : series_scope.
Notation "1" := series_1 : series_scope.
Notation "a = b" := (eq_series a b) : series_scope.
Notation "a ≠ b" := (not (eq_series a b)) : series_scope.

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

Add Parametric Relation : (series α) eq_series
 reflexivity proved by eq_series_refl
 symmetry proved by eq_series_sym
 transitivity proved by eq_series_trans
 as eq_series_rel.

(* *)

Lemma series_inf_eq : ∀ a, (a = series_inf rng a)%ser.
Proof.
intros a.
constructor; intros i.
unfold series_nth; simpl.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) ∞) as [H₁| H₁]; [ reflexivity | idtac ].
exfalso; apply H₁; constructor.
Qed.

(* series_add *)

Definition series_add s₁ s₂ :=
  {| terms i :=
       Lfield.add rng (series_nth rng i s₁) (series_nth rng i s₂);
     stop :=
       Nbar.max (stop s₁) (stop s₂) |}.

Definition series_opp s :=
  {| terms i := Lfield.opp rng (terms s i); stop := stop s |}.

Notation "- a" := (series_opp a) : series_scope.
Notation "a + b" := (series_add a b) : series_scope.
Notation "a - b" := (series_add a (series_opp b)) : series_scope.

Theorem series_add_comm : ∀ s₁ s₂, (s₁ + s₂ = s₂ + s₁)%ser.
Proof.
intros s₁ s₂.
constructor; simpl.
intros i.
unfold series_nth; simpl.
rewrite Nbar.max_comm.
destruct (Nbar.max (stop s₂) (stop s₁)) as [n| ].
 destruct (Nbar.lt_dec (fin i) (fin n)) as [Hlt| ]; [ idtac | reflexivity ].
 rewrite Lfield.add_comm; reflexivity.

 destruct (Nbar.lt_dec (fin i) ∞); [ idtac | reflexivity ].
 rewrite Lfield.add_comm; reflexivity.
Qed.

Theorem series_add_assoc : ∀ s₁ s₂ s₃, (s₁ + (s₂ + s₃) = (s₁ + s₂) + s₃)%ser.
Proof.
intros s₁ s₂ s₃.
unfold series_add; simpl.
constructor; simpl.
intros i.
unfold series_nth; simpl.
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
    destruct lt₃ as [Hlt₃| Hge₃]; [ apply Lfield.add_assoc | idtac ].
    rewrite Lfield.add_0_r; symmetry.
    rewrite <- Lfield.add_assoc.
    rewrite Lfield.add_0_r; reflexivity.

    rewrite <- Lfield.add_assoc, Lfield.add_0_l; reflexivity.

   rewrite <- Lfield.add_assoc, Lfield.add_0_l; reflexivity.

  rewrite Lfield.add_0_r; symmetry.
  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₅; clear Hge₅.
   apply Nbar.max_lt_iff; left; assumption.

   rewrite <- Lfield.add_assoc, Lfield.add_0_l.
   destruct lt₃ as [Hlt₃| Hge₃].
    exfalso; apply Hge₅; clear Hge₅.
    apply Nbar.max_lt_iff; right; assumption.

    rewrite Lfield.add_0_r; reflexivity.

 rewrite Lfield.add_0_l.
 destruct lt₁ as [Hlt₁| Hge₁].
  exfalso; apply Hge₄; clear Hge₄.
  apply Nbar.max_lt_iff; left; assumption.

  rewrite Lfield.add_0_l.
  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₄; clear Hge₄.
   apply Nbar.max_lt_iff; right; assumption.

   destruct lt₅ as [Hlt₅| Hge₅].
    rewrite Lfield.add_0_l; reflexivity.

    destruct lt₃ as [Hlt₃| Hge₃]; [ idtac | reflexivity ].
    exfalso; apply Hge₅; clear Hge₅.
    apply Nbar.max_lt_iff; right; assumption.
Qed.

Lemma stop_series_add_0_l : ∀ s, stop (series_add series_0 s) = stop s.
Proof.
intros s; simpl.
destruct (stop s); reflexivity.
Qed.

Lemma series_nth_series_0 : ∀ i,
  (series_nth rng i series_0 = Lfield.zero rng)%rng.
Proof.
intros i.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) 0); reflexivity.
Qed.

Theorem series_add_0_l : ∀ s, (0 + s = s)%ser.
Proof.
intros s.
constructor; intros i.
unfold series_nth.
rewrite stop_series_add_0_l; simpl.
remember (Nbar.lt_dec (fin i) (stop s)) as d.
destruct d as [H₁| H₁]; [ idtac | reflexivity ].
rewrite series_nth_series_0.
rewrite Lfield.add_0_l.
unfold series_nth.
rewrite <- Heqd; reflexivity.
Qed.

Theorem series_add_opp_r : ∀ s, (s - s = 0)%ser.
Proof.
intros s.
constructor; intros i.
unfold series_nth; simpl.
rewrite Nbar.max_id.
destruct (Nbar.lt_dec (fin i) 0) as [H₁| H₁].
 exfalso; revert H₁; apply Nbar.nlt_0_r.

 clear H₁.
 unfold series_nth; simpl.
 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₁| H₁]; [ idtac | reflexivity ].
 apply Lfield.add_opp_r.
Qed.

Theorem series_add_opp_l : ∀ s, (- s + s = 0)%ser.
Proof.
intros s.
rewrite series_add_comm.
apply series_add_opp_r.
Qed.

(* series_mul *)

Definition δ i j := if eq_nat_dec i j then Lfield.one rng else Lfield.zero rng.

Fixpoint sigma_aux b len f :=
  match len with
  | O => 0%rng
  | S len₁ => (f b + sigma_aux (S b) len₁ f)%rng
  end.

Definition sigma b e f := sigma_aux b (S e - b) f.

Notation "'Σ' ( i = b , e ) ' ' f" := (sigma b e (λ i, f))
  (at level 0, i at level 0, b at level 60, e at level 60, f at level 40).

Definition convol_mul a b k :=
  Σ (i = 0, k)   Σ (j = 0, k)  
    (Lfield.mul rng (δ (i + j) k)
       (Lfield.mul rng (series_nth rng i a) (series_nth rng j b))).

Definition series_mul a b :=
  {| terms k := convol_mul a b k;
     stop := Nbar.add (stop a) (stop b) |}.

Notation "a * b" := (series_mul a b) : series_scope.

Lemma sigma_aux_compat : ∀ f g b₁ b₂ len,
  (∀ i, 0 ≤ i < len → (f (b₁ + i)%nat = g (b₂ + i)%nat)%rng)
  → (sigma_aux b₁ len f = sigma_aux b₂ len g)%rng.
Proof.
intros f g b₁ b₂ len Hfg.
revert b₁ b₂ Hfg.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen.
 apply Lfield.add_compat_r.
 assert (0 ≤ 0 < S len) as H.
  split; [ reflexivity | apply Nat.lt_0_succ ].

  apply Hfg in H.
  do 2 rewrite Nat.add_0_r in H; assumption.

 intros i Hi.
 do 2 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hfg.
 split; [ apply Nat.le_0_l | idtac ].
 apply lt_n_S.
 destruct Hi; assumption.
Qed.

Lemma sigma_compat : ∀ f g b k,
  (∀ i, b ≤ i ≤ k → (f i = g i)%rng)
  → (Σ (i = b, k)  f i = Σ (i = b, k)   g i)%rng.
Proof.
intros f g b k Hfg.
apply sigma_aux_compat.
intros i (_, Hi).
apply Hfg.
split; [ apply Nat.le_add_r | omega ].
Qed.

Lemma sigma_sigma_compat : ∀ f g b₁ k₁ b₂ k₂,
  (∀ i j, (f i j = g i j)%rng)
  → (Σ (i = b₁, k₁)   Σ (j = b₂, k₂)   f i j
     = Σ (i = b₁, k₁)   Σ (j = b₂, k₂)   g i j)%rng.
Proof.
intros f g b₁ k₁ b₂ k₂ Hfg.
apply sigma_aux_compat; intros l Hl.
apply sigma_aux_compat; intros m Hm.
apply Hfg.
Qed.

Lemma sigma_mul_comm : ∀ f g b k,
  (Σ (i = b, k)   f i * g i
   = Σ (i = b, k)   g i * f i)%rng.
Proof.
intros f g b len.
apply sigma_compat; intros i Hi.
apply Lfield.mul_comm.
Qed.

Lemma sigma_mul_assoc : ∀ f g h b k,
  (Σ (i = b, k)   f i * (g i * h i)
   = Σ (i = b, k)   (f i * g i) * h i)%rng.
Proof.
intros f g h b k.
apply sigma_compat; intros i Hi.
apply Lfield.mul_assoc.
Qed.

Lemma sigma_sigma_mul_comm : ∀ f g b₁ k₁ b₂ k₂,
  (Σ (i = b₁, k₁)   Σ (j = b₂, k₂)   f i j * g i j
   = Σ (i = b₁, k₁)   Σ (j = b₂, k₂)   g i j * f i j)%rng.
Proof.
intros f g b₁ k₁ b₂ k₂.
apply sigma_sigma_compat; intros i j.
apply Lfield.mul_comm.
Qed.

Lemma sigma_sigma_mul_assoc : ∀ f g h b₁ k₁ b₂ k₂,
  (Σ (i = b₁, k₁)   Σ (j = b₂, k₂)   f i j * (g i j * h i j)
   = Σ (i = b₁, k₁)   Σ (j = b₂, k₂)   (f i j * g i j) * h i j)%rng.
Proof.
intros f g h b₁ k₁ b₂ k₂.
apply sigma_sigma_compat; intros i j.
apply Lfield.mul_assoc.
Qed.

Lemma all_0_sigma_aux_0 : ∀ f b len,
  (∀ i, (b ≤ i < b + len)%nat → (f i = 0)%rng)
  → (sigma_aux b len (λ i, f i) = 0)%rng.
Proof.
intros f b len H.
revert b H.
induction len; intros; [ reflexivity | simpl ].
rewrite H; [ idtac | omega ].
rewrite Lfield.add_0_l, IHlen; [ reflexivity | idtac ].
intros i Hi; apply H; omega.
Qed.

Lemma all_0_sigma_0 : ∀ f i₁ i₂,
  (∀ i, i₁ ≤ i ≤ i₂ → (f i = 0)%rng) → (Σ (i = i₁, i₂)   f i = 0)%rng.
Proof.
intros f i₁ i₂ H.
apply all_0_sigma_aux_0.
intros i (H₁, H₂).
apply H.
split; [ assumption | omega ].
Qed.

Lemma delta_id : ∀ i, (δ i i = 1)%rng.
Proof.
intros i; unfold δ.
destruct (eq_nat_dec i i) as [H₁| H₁]; [ reflexivity | idtac ].
exfalso; apply H₁; reflexivity.
Qed.

Lemma delta_neq : ∀ i j, i ≠ j → (δ i j = 0)%rng.
Proof.
intros i j Hij; unfold δ.
destruct (eq_nat_dec i j) as [H₁| H₁]; [ subst i | reflexivity ].
exfalso; apply Hij; reflexivity.
Qed.

Add Parametric Morphism : series_mul
with signature eq_series ==> eq_series ==> eq_series
as series_mul_morph.
Proof.
intros a b Hab c d Hcd.
constructor.
intros i.
inversion Hab; subst.
inversion Hcd; subst.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) (stop a + stop c)) as [H₁| H₁].
 destruct (Nbar.lt_dec (fin i) (stop b + stop d)) as [H₂| H₂].
  unfold convol_mul.
  rename i into k.
  apply sigma_compat; intros i Hi.
  apply sigma_compat; intros j Hj.
  rewrite H, H0.
  reflexivity.

  unfold convol_mul.
  rename i into k.
  apply all_0_sigma_0; intros i Hi.
  apply all_0_sigma_0; intros j Hj.
  destruct (eq_nat_dec (i + j)%nat k) as [H₃| H₃].
   rewrite H₃, delta_id, Lfield.mul_1_l, H, H0.
   unfold series_nth; simpl.
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

     rewrite Lfield.mul_0_r; reflexivity.

    rewrite Lfield.mul_0_l; reflexivity.

   rewrite delta_neq; [ idtac | assumption ].
   rewrite Lfield.mul_0_l; reflexivity.

 destruct (Nbar.lt_dec (fin i) (stop b + stop d)) as [H₂| H₂].
  unfold convol_mul.
  rename i into k.
  symmetry.
  apply all_0_sigma_0; intros i Hi.
  apply all_0_sigma_0; intros j Hj.
  destruct (eq_nat_dec (i + j)%nat k) as [H₃| H₃].
   rewrite H₃, delta_id, Lfield.mul_1_l, <- H, <- H0.
   unfold series_nth; simpl.
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

     rewrite Lfield.mul_0_r; reflexivity.

    rewrite Lfield.mul_0_l; reflexivity.

   rewrite delta_neq; [ idtac | assumption ].
   rewrite Lfield.mul_0_l; reflexivity.

  reflexivity.
Qed.

Lemma sigma_aux_sigma_aux_comm : ∀ f i di j dj,
  (sigma_aux i di (λ i, sigma_aux j dj (λ j, f i j))
   = sigma_aux j dj (λ j, sigma_aux i di (λ i, f i j)))%rng.
Proof.
intros f i di j dj; revert i.
induction di; intros; simpl.
 symmetry; apply all_0_sigma_aux_0.
 intros; reflexivity.

 rewrite IHdi; clear IHdi.
 revert j.
 induction dj; intros; simpl.
  apply Lfield.add_0_r.

  rewrite <- IHdj.
  do 2 rewrite <- Lfield.add_assoc.
  apply Lfield.add_compat_l.
  rewrite Lfield.add_comm, <- Lfield.add_assoc.
  apply Lfield.add_compat_l, Lfield.add_comm.
Qed.

Lemma sigma_sigma_comm : ∀ f i₁ i₂ j₁ j₂,
  (Σ (i = i₁, i₂)   Σ (j = j₁, j₂)   f i j
   = Σ (j = j₁, j₂)   Σ (i = i₁, i₂)   f i j)%rng.
Proof.
intros f i₁ i₂ j₁ j₂.
apply sigma_aux_sigma_aux_comm; assumption.
Qed.

Lemma sigma_aux_sigma_aux_sigma_aux_comm : ∀ f i di j dj k dk,
  (sigma_aux i di
     (λ i,
      sigma_aux j dj
        (λ j, sigma_aux k dk (λ k, f i j k)))
   = sigma_aux i di
       (λ i,
        sigma_aux k dk
          (λ k, sigma_aux j dj (λ j, f i j k))))%rng.
Proof.
intros f i di j dj k dk; revert i.
induction di; intros; [ reflexivity | simpl ].
rewrite IHdi.
apply Lfield.add_compat_r.
apply sigma_aux_sigma_aux_comm.
Qed.

Lemma sigma_sigma_sigma_comm : ∀ f i₁ i₂ j₁ j₂ k₁ k₂,
  (Σ (i = i₁, i₂)   Σ (j = j₁, j₂)   Σ (k = k₁, k₂)   f i j k
   = Σ (i = i₁, i₂)   Σ (k = k₁, k₂)   Σ (j = j₁, j₂)   f i j k)%rng.
Proof.
intros f i₁ i₂ j₁ j₂ k₁ k₂.
apply sigma_aux_sigma_aux_sigma_aux_comm; assumption.
Qed.

Theorem series_mul_comm : ∀ a b, (a * b = b * a)%ser.
Proof.
intros a b.
constructor; intros k.
unfold series_nth; simpl.
rewrite Nbar.add_comm.
destruct (Nbar.lt_dec (fin k) (stop b + stop a)) as [H₁| H₁].
 unfold convol_mul.
 rewrite sigma_sigma_comm.
 apply sigma_compat; intros i Hi.
 apply sigma_compat; intros j Hj.
 rewrite Nat.add_comm.
 do 2 rewrite Lfield.mul_assoc.
 rewrite Lfield.mul_shuffle0; reflexivity.

 reflexivity.
Qed.

Lemma stop_series_mul_0_l : ∀ s, stop (series_mul series_0 s) = stop s.
Proof.
intros s; simpl.
destruct (stop s); reflexivity.
Qed.

Theorem series_mul_0_l : ∀ s, (0 * s = 0)%ser.
Proof.
intros s.
constructor; intros i.
unfold series_nth.
rewrite stop_series_mul_0_l; simpl.
destruct (Nbar.lt_dec (fin i) (stop s)) as [H₁| H₁].
 unfold convol_mul.
 rename i into k.
 destruct (Nbar.lt_dec (fin k) 0) as [H₂| H₂].
  apply Nbar.nle_gt in H₂.
  exfalso; apply H₂, Nbar.le_0_l.

  apply all_0_sigma_0; intros i Hi.
  apply all_0_sigma_0; intros j Hj.
  rewrite Lfield.mul_assoc, Lfield.mul_shuffle0.
  rewrite Lfield.mul_comm.
  rewrite series_nth_series_0.
  rewrite Lfield.mul_0_l.
  reflexivity.

 destruct (Nbar.lt_dec (fin i) 0); reflexivity.
Qed.

Lemma delta_0_succ : ∀ i, (δ 0 (S i) = 0)%rng.
Proof.
intros i; unfold δ.
destruct (eq_nat_dec 0 (S i)) as [H₁|]; [ discriminate H₁ | reflexivity ].
Qed.

Lemma sigma_aux_mul_swap : ∀ a f b len,
  (sigma_aux b len (λ i, a * f i) = a * sigma_aux b len f)%rng.
Proof.
intros a f b len; revert b.
induction len; intros; simpl.
 rewrite Lfield.mul_0_r; reflexivity.

 rewrite IHlen, Lfield.mul_add_distr_l.
 reflexivity.
Qed.

Lemma sigma_mul_swap : ∀ a f b k,
  (Σ (i = b, k)   a * f i = a * Σ (i = b, k)   f i)%rng.
Proof.
intros a f b k.
apply sigma_aux_mul_swap.
Qed.

Lemma sigma_aux_sigma_aux_mul_swap : ∀ f g h b₁ b₂ len,
  (sigma_aux b₁ len
     (λ i, sigma_aux b₂ (f i) (λ j, g i * h i j))
   = sigma_aux b₁ len
       (λ i, (g i * sigma_aux b₂ (f i) (λ j, h i j))))%rng.
Proof.
intros f g h b₁ b₂ len.
revert b₁ b₂.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen.
apply Lfield.add_compat_r.
apply sigma_aux_mul_swap.
Qed.

Lemma sigma_sigma_mul_swap : ∀ f g h k,
  (Σ (i = 0, k)   Σ (j = 0, f i)   g i * h i j
   = Σ (i = 0, k)   g i * Σ (j = 0, f i)   h i j)%rng.
Proof.
intros f g h k.
apply sigma_aux_sigma_aux_mul_swap.
Qed.

Lemma glop : ∀ f g h k,
  (Σ (i = 0, k)   Σ (j = 0, k)   g i j * (f i * h i j)
   = Σ (i = 0, k)   f i * Σ (j = 0, k)   g i j * h i j)%rng.
Proof.
intros f g h k.
apply sigma_compat; intros i Hi.
rewrite <- sigma_mul_swap.
apply sigma_compat; intros j Hj.
rewrite Lfield.mul_comm, Lfield.mul_shuffle0, Lfield.mul_assoc.
reflexivity.
Qed.

Lemma sigma_only_one_non_0 : ∀ f b v k,
  (b ≤ v ≤ k)%nat
  → (∀ i, (b ≤ i ≤ k)%nat → (i ≠ v)%nat → (f i = 0)%rng)
    → (Σ (i = b, k)   f i = f v)%rng.
Proof.
intros f b v k (Hbv, Hvk) Hi.
unfold sigma.
rewrite Nat.sub_succ_l; [ idtac | etransitivity; eassumption ].
remember (k - b)%nat as len.
replace k with (b + len)%nat in * by omega.
clear k Heqlen.
revert b v Hbv Hvk Hi.
induction len; intros.
 simpl.
 rewrite Lfield.add_0_r.
 replace b with v ; [ reflexivity | idtac ].
 rewrite Nat.add_0_r in Hvk.
 apply Nat.le_antisymm; assumption.

 remember (S len) as x; simpl; subst x.
 destruct (eq_nat_dec b v) as [H₁| H₁].
  subst b.
  rewrite all_0_sigma_aux_0.
   rewrite Lfield.add_0_r; reflexivity.

   intros j Hj.
   apply Hi; omega.

  rewrite Hi; [ idtac | omega | assumption ].
  rewrite Lfield.add_0_l.
  apply IHlen.
   omega.

   rewrite Nat.add_succ_l, <- Nat.add_succ_r; assumption.

   intros j Hjb Hj.
   apply Hi; [ omega | assumption ].
Qed.

Theorem series_mul_1_l : ∀ s, (1 * s = s)%ser.
Proof.
intros s.
constructor; intros i.
unfold series_nth; simpl.
remember (stop s) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ].
 destruct (Nbar.lt_dec (fin i) (fin st)) as [H₁| H₁].
  destruct (Nbar.lt_dec (fin i) (fin (S st))) as [H₂| H₂].
   unfold convol_mul.
   rename i into k.
   rewrite glop.
   rewrite sigma_only_one_non_0 with (v := O).
    simpl.
    unfold series_nth at 1; simpl.
    destruct (Nbar.lt_dec 0 1) as [H₃| H₃].
     rewrite Lfield.mul_1_l.
     rewrite sigma_only_one_non_0 with (v := k).
      rewrite delta_id, Lfield.mul_1_l.
      unfold series_nth.
      rewrite <- Hst in H₁.
      destruct (Nbar.lt_dec (fin k) (stop s)); [ idtac | contradiction ].
      reflexivity.

      split; [ apply Nat.le_0_l | reflexivity ].

      intros i Hik Hi.
      rewrite delta_neq; [ idtac | assumption ].
      apply Lfield.mul_0_l.

     exfalso; apply H₃, Nbar.lt_0_1.

    split; [ reflexivity | apply Nat.le_0_l ].

    intros i Hik Hi.
    unfold series_nth at 1; simpl.
    destruct (Nbar.lt_dec (fin i) 1) as [H₃| H₃].
     apply Nbar.fin_lt_mono in H₃.
     apply Nat.lt_1_r in H₃; contradiction.

     apply Lfield.mul_0_l.

   exfalso; apply H₂.
   eapply Nbar.lt_trans; [ eassumption | idtac ].
   apply Nbar.lt_fin, Nat.lt_succ_r; reflexivity.

  destruct (Nbar.lt_dec (fin i) (fin (S st))) as [H₂| H₂].
   unfold convol_mul.
   rename i into k.
   apply all_0_sigma_0; intros i Hi.
   apply all_0_sigma_0; intros j Hj.
   destruct i; simpl.
    unfold series_nth; simpl.
    destruct (Nbar.lt_dec (fin j) (stop s)) as [H₃| H₃].
     unfold δ.
     destruct (eq_nat_dec j k) as [H₄| H₄].
      subst j.
      rewrite Hst in H₃; contradiction.

      rewrite Lfield.mul_0_l; reflexivity.

     rewrite Lfield.mul_assoc, Lfield.mul_0_r; reflexivity.

    unfold series_nth; simpl.
    destruct (Nbar.lt_dec (fin (S i)) 1) as [H₃| H₃].
     apply Nbar.nle_gt in H₃.
     exfalso; apply H₃.
     apply Nbar.fin_le_mono, le_n_S, Nat.le_0_l.

     rewrite Lfield.mul_0_l, Lfield.mul_0_r; reflexivity.

   reflexivity.

 destruct (Nbar.lt_dec (fin i) ∞) as [H₁| ]; [ idtac | reflexivity ].
 unfold convol_mul.
 rename i into k.
 rewrite glop.
 rewrite sigma_only_one_non_0 with (v := O).
  simpl.
  unfold series_nth at 1; simpl.
  destruct (Nbar.lt_dec 0 1) as [H₃| H₃].
   rewrite Lfield.mul_1_l.
   rewrite sigma_only_one_non_0 with (v := k).
    rewrite delta_id, Lfield.mul_1_l.
    unfold series_nth.
    rewrite <- Hst in H₁.
    destruct (Nbar.lt_dec (fin k) (stop s)); [ idtac | contradiction ].
    reflexivity.

    split; [ apply Nat.le_0_l | reflexivity ].

    intros i Hik Hi.
    rewrite delta_neq; [ idtac | assumption ].
    apply Lfield.mul_0_l.

   exfalso; apply H₃, Nbar.lt_0_1.

  split; [ reflexivity | apply Nat.le_0_l ].

  intros i Hik Hi.
  unfold series_nth at 1; simpl.
  destruct (Nbar.lt_dec (fin i) 1) as [H₃| H₃].
   apply Nbar.fin_lt_mono in H₃.
   apply Nat.lt_1_r in H₃; contradiction.

   apply Lfield.mul_0_l.
Qed.

Lemma mul_sigma_aux_inj : ∀ f a b len,
  (a * sigma_aux b len f = sigma_aux b len (λ i, a * f i))%rng.
Proof.
intros f a b len; revert b.
induction len; intros; simpl.
 rewrite Lfield.mul_0_r; reflexivity.

 rewrite <- IHlen.
 apply Lfield.mul_add_distr_l.
Qed.

Lemma mul_sigma_inj : ∀ f i₁ i₂ a,
  (a * Σ (i = i₁, i₂)   f i = Σ (i = i₁, i₂)   a * f i)%rng.
Proof.
intros f i₁ i₂ a.
apply mul_sigma_aux_inj.
Qed.

Lemma sigma_aux_extend_0 : ∀ f b len₁ len₂,
  len₁ ≤ len₂
  → (∀ i, (b + len₁ ≤ i)%nat → (f i = 0)%rng)
    → (sigma_aux b len₁ f = sigma_aux b len₂ f)%rng.
Proof.
intros f b len₁ len₂ Hlen Hi.
revert b len₁ Hlen Hi.
induction len₂; intros; simpl.
 apply le_n_0_eq in Hlen; subst len₁; reflexivity.

 destruct len₁; simpl.
  rewrite all_0_sigma_aux_0.
   symmetry; rewrite Lfield.add_0_r.
   apply Hi.
   rewrite Nat.add_0_r; reflexivity.

   intros i H.
   apply Hi; omega.

  apply Nat.succ_le_mono in Hlen.
  apply Lfield.add_compat_l.
  apply IHlen₂; [ assumption | idtac ].
  intros i H.
  apply Hi; rewrite Nat.add_succ_r, <- Nat.add_succ_l; assumption.
Qed.

Lemma sigma_extend_0 : ∀ f i₁ i₂ i₃,
  i₂ ≤ i₃
  → (∀ i, (i₂ < i)%nat → (f i = 0)%rng)
    → (Σ (i = i₁, i₂)   f i = Σ (i = i₁, i₃)   f i)%rng.
Proof.
intros f i₁ i₂ i₃ Hi₂₃ Hi.
apply sigma_aux_extend_0; [ omega | idtac ].
intros i Hi₁.
apply Hi; omega.
Qed.

Lemma series_inf_nth : ∀ s t i,
  s = series_inf rng t
  → (series_nth rng i s = terms s i)%rng.
Proof.
intros s t i Hs.
subst s; simpl.
unfold series_nth; simpl.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) ∞) as [| H]; [ reflexivity | idtac ].
exfalso; apply H; constructor.
Qed.

Lemma series_nth_inf : ∀ a i,
  (series_nth rng i (series_inf rng a) = terms (series_inf rng a) i)%rng.
Proof.
intros a i.
rewrite series_inf_nth; reflexivity.
Qed.

Definition convol_mul_inf a b k :=
  Σ (i = 0, k)   Σ (j = 0, k)  
    (δ (i + j) k * terms a i * terms b j)%rng.

Definition series_mul_inf a b :=
  {| terms k := convol_mul_inf a b k; stop := ∞ |}.

Lemma series_mul_mul_inf : ∀ a b,
  (a * b = series_mul_inf (series_inf rng a) (series_inf rng b))%ser.
Proof.
intros a b.
constructor; intros k.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin k) ∞) as [H₁| H₁]; [ idtac | exfalso ].
 clear H₁.
 destruct (Nbar.lt_dec (fin k) (stop a + stop b)) as [H₁| H₁].
  unfold convol_mul, convol_mul_inf.
  apply sigma_compat; intros i Hi.
  apply sigma_compat; intros j Hj.
  rewrite <- Lfield.mul_assoc.
  apply Lfield.mul_compat_l; reflexivity.

  unfold convol_mul_inf.
  symmetry; unfold convol_mul_inf; simpl.
  apply all_0_sigma_0; intros i Hi.
  apply all_0_sigma_0; intros j Hj.
  unfold series_nth.
  destruct (Nbar.lt_dec (fin i) (stop a)) as [H₂| H₂].
   destruct (Nbar.lt_dec (fin j) (stop b)) as [H₃| H₃].
    destruct (eq_nat_dec (i + j) k) as [H₄| H₄].
     rewrite H₄, delta_id, Lfield.mul_1_l.
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
     do 2 rewrite Lfield.mul_0_l; reflexivity.

    rewrite Lfield.mul_0_r; reflexivity.

   rewrite Lfield.mul_0_r, Lfield.mul_0_l; reflexivity.

 apply H₁; constructor.
Qed.

Lemma series_inf_mul : ∀ a b,
  (series_inf rng (a * b) =
   series_mul_inf (series_inf rng a) (series_inf rng b))%ser.
Proof.
intros a b.
rewrite <- series_mul_mul_inf.
rewrite <- series_inf_eq.
reflexivity.
Qed.

Lemma series_nth_mul_inf : ∀ a b i,
  (series_nth rng i (series_mul_inf a b)
   = terms (series_mul_inf a b) i)%rng.
Proof.
intros a b i.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) ∞) as [| H]; [ reflexivity | idtac ].
exfalso; apply H; constructor.
Qed.

Lemma sigma_aux_sigma_aux_extend_0 : ∀ f g b₁ b₂ len₁ len₂,
  (∀ i, b₁ ≤ i < b₁ + len₁ → g i ≤ len₂)
  → (∀ i j, (b₂ + g i ≤ j)%nat → (f i j = 0)%rng)
    → (sigma_aux b₁ len₁ (λ i, sigma_aux b₂ (g i) (λ j, f i j))
       = sigma_aux b₁ len₁ (λ i, sigma_aux b₂ len₂ (λ j, f i j)))%rng.
Proof.
intros f g b₁ b₂ len₁ len₂ Hg Hfg.
apply sigma_aux_compat; intros i Hi.
apply sigma_aux_extend_0.
 apply Hg; omega.

 intros j Hj.
 apply Hfg; assumption.
Qed.

Lemma sigma_sigma_extend_0 : ∀ f m,
  (∀ i j, (i < j)%nat → (f i j = 0)%rng)
  → (Σ (i = 0, m)   Σ (j = 0, i)   f i j
     = Σ (i = 0, m)   Σ (j = 0, m)   f i j)%rng.
Proof.
intros f m Hf.
apply sigma_aux_sigma_aux_extend_0; [ idtac | assumption ].
intros i Hi; omega.
Qed.

Definition sigma_mul_3 aa bb cc m :=
  Σ (i = 0, m)  
  Σ (j = 0, m)  
  Σ (k = 0, m)  
    (δ (i + j + k) m * terms aa i * terms bb j * terms cc k)%rng.

Lemma convol_mul_assoc_1 : ∀ aa bb cc m,
  (Σ (i = 0, m)  
   Σ (l = 0, m)  
    δ (i + l) m * terms aa i *
    Σ (j = 0, l)  
    Σ (k = 0, l)   δ (j + k) l * terms bb j * terms cc k
   = sigma_mul_3 aa bb cc m)%rng.
Proof.
(* à nettoyer *)
intros a b c m.
unfold sigma_mul_3.
apply sigma_compat; intros i Hi.
rewrite <- sigma_mul_assoc, sigma_mul_comm, <- sigma_mul_assoc.
rewrite sigma_mul_swap; symmetry.
do 2 rewrite <- sigma_sigma_mul_assoc.
rewrite sigma_sigma_mul_comm.
rewrite <- sigma_sigma_mul_assoc.
rewrite sigma_sigma_mul_swap, sigma_mul_swap.
apply Lfield.mul_compat_l.
symmetry.
rewrite sigma_mul_comm.
rewrite <- sigma_sigma_mul_swap.
rewrite sigma_sigma_extend_0.
 Focus 2.
 intros u j Huhm.
 rewrite all_0_sigma_0.
  rewrite Lfield.mul_0_r; reflexivity.

  intros k.
  rewrite delta_neq.
   rewrite Lfield.mul_0_l, Lfield.mul_0_l; reflexivity.

   intros H; subst u.
   apply Nat.nle_gt in Huhm.
   apply Huhm, le_plus_l.

 rewrite sigma_sigma_comm.
 apply sigma_compat; intros j Hj.
 rewrite <- sigma_sigma_mul_swap.
 rewrite sigma_sigma_extend_0.
  rewrite sigma_sigma_comm.
  apply sigma_compat; intros k Hk.
  destruct (le_dec (j + k) m) as [H₁| H₁].
   rewrite sigma_only_one_non_0 with (v := (j + k)%nat).
    rewrite delta_id, Lfield.mul_1_l.
    rewrite Nat.add_assoc, Lfield.mul_comm.
    reflexivity.

    split; [ apply Nat.le_0_l | assumption ].

    intros l Hlk Hl.
    rewrite Lfield.mul_comm.
    apply Nat.neq_sym in Hl.
    rewrite delta_neq; [ idtac | assumption ].
    do 3 rewrite Lfield.mul_0_l; reflexivity.

   rewrite all_0_sigma_0.
    rewrite delta_neq.
     rewrite Lfield.mul_0_r; reflexivity.

     omega.

    intros l.
    destruct (eq_nat_dec (i + l) m) as [H₂| H₂].
     rewrite H₂, delta_id, Lfield.mul_1_l.
     destruct (eq_nat_dec (j + k) l) as [H₃| H₃].
      exfalso; omega.

      rewrite delta_neq; [ idtac | assumption ].
      rewrite Lfield.mul_0_l, Lfield.mul_0_l; reflexivity.

     rewrite delta_neq; [ idtac | assumption ].
     rewrite Lfield.mul_0_l; reflexivity.

  intros l k Hlk.
  destruct (eq_nat_dec (i + l) m) as [H₂| H₂].
   rewrite H₂, delta_id, Lfield.mul_1_l.
   destruct (eq_nat_dec (j + k) l) as [H₃| H₃].
    exfalso; omega.

    rewrite delta_neq; [ idtac | assumption ].
    rewrite Lfield.mul_0_l, Lfield.mul_0_l; reflexivity.

   rewrite delta_neq; [ idtac | assumption ].
   rewrite Lfield.mul_0_l; reflexivity.
Qed.

Lemma convol_mul_assoc_2 : ∀ aa bb cc k,
  (Σ (i = 0, k)  
   Σ (j = 0, k)  
    δ (i + j) k *
    (Σ (i0 = 0, i)  
     Σ (j0 = 0, i)   (δ (i0 + j0) i * terms aa i0 * terms bb j0)) *
    terms cc j = sigma_mul_3 aa bb cc k)%rng.
Proof.
intros a b c m.
unfold sigma_mul_3.
rewrite sigma_sigma_comm; symmetry.
rewrite sigma_sigma_sigma_comm.
rewrite sigma_sigma_comm.
apply sigma_compat; intros k Hk.
rewrite sigma_sigma_mul_comm.
rewrite sigma_sigma_mul_swap.
rewrite sigma_mul_swap; symmetry.
rewrite sigma_mul_comm.
rewrite sigma_mul_swap; symmetry.
apply Lfield.mul_compat_l.
rewrite <- sigma_sigma_mul_swap.
symmetry.
rewrite sigma_sigma_extend_0.
 rewrite sigma_sigma_comm.
 apply sigma_compat; intros i Hi.
 rewrite <- sigma_sigma_mul_swap.
 rewrite sigma_sigma_extend_0.
  rewrite sigma_sigma_comm.
  apply sigma_compat; intros j Hj.
  rewrite sigma_mul_assoc, sigma_mul_comm.
  rewrite sigma_mul_swap; symmetry.
  rewrite Lfield.mul_comm.
  apply Lfield.mul_compat_l.
  rewrite Lfield.mul_comm; symmetry.
  rewrite sigma_mul_assoc, sigma_mul_comm.
  rewrite sigma_mul_swap.
  apply Lfield.mul_compat_l.
  destruct (eq_nat_dec (i + j + k) m) as [H₁| H₁].
   rewrite H₁, delta_id.
   destruct (le_dec (i + j) m) as [H₂| H₂].
    rewrite sigma_only_one_non_0 with (v := (i + j)%nat).
     rewrite H₁.
     do 2 rewrite delta_id.
     rewrite Lfield.mul_1_r; reflexivity.

     split; [ apply Nat.le_0_l | assumption ].

     intros l Hlk Hl.
     rewrite Lfield.mul_comm.
     apply Nat.neq_sym in Hl.
     rewrite delta_neq; [ idtac | assumption ].
     rewrite Lfield.mul_0_l; reflexivity.

    exfalso; omega.

   rewrite delta_neq; [ idtac | assumption ].
   apply all_0_sigma_0.
   intros l.
   destruct (eq_nat_dec (i + j) l) as [H₂| H₂].
    destruct (eq_nat_dec (l + k) m) as [H₃| H₃].
     rewrite <- H₂ in H₃; contradiction.

     rewrite delta_neq; [ idtac | assumption ].
     rewrite Lfield.mul_0_l; reflexivity.

    rewrite Lfield.mul_comm, delta_neq; [ idtac | assumption ].
    rewrite Lfield.mul_0_l; reflexivity.

  intros l j Hj.
  rewrite Lfield.mul_comm.
  rewrite delta_neq; [ idtac | omega ].
  do 3 rewrite Lfield.mul_0_l; reflexivity.

 intros l i Hil.
 rewrite all_0_sigma_0.
  rewrite Lfield.mul_0_r; reflexivity.

  intros j.
  rewrite delta_neq; [ idtac | omega ].
  do 2 rewrite Lfield.mul_0_l; reflexivity.
Qed.

Theorem series_mul_assoc : ∀ a b c, (a * (b * c) = (a * b) * c)%ser.
Proof.
intros a b c.
pose proof (series_mul_mul_inf b c) as H.
rewrite H; clear H.
pose proof (series_mul_mul_inf a b) as H.
rewrite H; clear H.
rewrite series_mul_mul_inf; symmetry.
rewrite series_mul_mul_inf; symmetry.
remember (series_inf rng a) as aa eqn:Haa .
remember (series_inf rng b) as bb eqn:Hbb .
remember (series_inf rng c) as cc eqn:Hcc .
constructor; intros k.
do 2 rewrite series_nth_mul_inf; simpl.
unfold convol_mul_inf; simpl.
remember
 (λ i j, (δ (i + j) k * terms aa i * terms (series_mul_inf bb cc) j)%rng) as f.
rewrite sigma_sigma_compat with (g := f); subst f.
 Focus 2.
 intros i j; rewrite series_nth_mul_inf; reflexivity.

 symmetry.
 remember
  (λ i j, (δ (i + j) k * terms (series_mul_inf aa bb) i * terms cc j)%rng) as f.
 rewrite sigma_sigma_compat with (g := f); subst f.
  Focus 2.
  intros i j; rewrite series_nth_mul_inf; reflexivity.

  symmetry.
  unfold series_mul_inf; simpl.
  unfold convol_mul_inf.
  rewrite convol_mul_assoc_1; symmetry.
  apply convol_mul_assoc_2.
Qed.

Lemma sigma_aux_add : ∀ f g b len,
  (sigma_aux b len f + sigma_aux b len g =
   sigma_aux b len (λ i, f i + g i))%rng.
Proof.
intros f g b len.
revert b.
induction len; intros; simpl; [ apply Lfield.add_0_l | idtac ].
rewrite Lfield.add_shuffle0.
do 3 rewrite <- Lfield.add_assoc.
do 2 apply Lfield.add_compat_l.
rewrite Lfield.add_comm.
apply IHlen.
Qed.

Lemma sigma_add : ∀ f g b e,
  (Σ (i = b, e)   f i + Σ (i = b, e)   g i = Σ (i = b, e)   (f i + g i))%rng.
Proof.
intros f g b e.
apply sigma_aux_add.
Qed.

Lemma sigma_only_one : ∀ f n, (Σ (i = n, n)   f i = f n)%rng.
Proof.
intros f n.
unfold sigma.
rewrite Nat.sub_succ_l; [ idtac | reflexivity ].
rewrite Nat.sub_diag; simpl.
rewrite Lfield.add_0_r; reflexivity.
Qed.

Lemma series_nth_add : ∀ a b i,
  (series_nth rng i (a + b)%ser =
   series_nth rng i a + series_nth rng i b)%rng.
Proof.
intros a b i.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) (Nbar.max (stop a) (stop b))) as [H₁| H₁].
 reflexivity.

 destruct (Nbar.lt_dec (fin i) (stop a)) as [H₂| H₂].
  exfalso; apply H₁.
  apply Nbar.max_lt_iff; left; assumption.

  destruct (Nbar.lt_dec (fin i) (stop b)) as [H₃| H₃].
   exfalso; apply H₁.
   apply Nbar.max_lt_iff; right; assumption.

   rewrite Lfield.add_0_l; reflexivity.
Qed.

Lemma convol_mul_add_distr_l : ∀ a b c i,
  (convol_mul a (b + c)%ser i = convol_mul a b i + convol_mul a c i)%rng.
Proof.
intros a b c k.
unfold convol_mul.
rewrite sigma_add.
apply sigma_compat; intros i Hi.
rewrite sigma_add.
apply sigma_compat; intros j Hj.
rewrite series_nth_add.
do 2 rewrite Lfield.mul_add_distr_l.
reflexivity.
Qed.

Lemma add_le_convol_mul_is_0 : ∀ a b i,
  (stop a + stop b ≤ fin i)%Nbar → (convol_mul a b i = 0)%rng.
Proof.
intros a b k Habk.
unfold convol_mul.
apply all_0_sigma_0; intros i Hi.
apply all_0_sigma_0; intros j Hj.
destruct (eq_nat_dec (i + j) k) as [H₁| H₁].
 destruct (Nbar.lt_dec (fin i) (stop a)) as [H₂| H₂].
  rewrite Lfield.mul_assoc.
  apply Lfield.mul_eq_0; right.
  unfold series_nth.
  destruct (Nbar.lt_dec (fin j) (stop b)) as [H₃| H₃].
   exfalso; apply Nbar.nlt_ge in Habk; apply Habk.
   rewrite <- H₁, Nbar.fin_inj_add.
   remember (stop b) as st eqn:Hst .
   symmetry in Hst.
   destruct st as [st| ].
    apply Nbar.lt_trans with (m := (fin i + fin st)%Nbar).
     apply Nbar.add_lt_mono_l; [ intros H; discriminate H | assumption ].

     apply Nbar.add_lt_mono_r; [ intros H; discriminate H | assumption ].

    simpl; rewrite Nbar.add_comm; constructor.

   reflexivity.

  rewrite Lfield.mul_assoc, Lfield.mul_shuffle0.
  apply Lfield.mul_eq_0; right.
  unfold series_nth.
  destruct (Nbar.lt_dec (fin i) (stop a)); [ contradiction | idtac ].
  reflexivity.

 rewrite delta_neq; [ idtac | assumption ].
 rewrite Lfield.mul_0_l; reflexivity.
Qed.

Theorem series_mul_add_distr_l : ∀ a b c, (a * (b + c) = a * b + a * c)%ser.
Proof.
intros a b c.
constructor; intros k.
unfold series_nth; simpl.
remember (stop a + Nbar.max (stop b) (stop c))%Nbar as x.
destruct (Nbar.lt_dec (fin k) x) as [H₁| H₁]; subst x.
 rewrite convol_mul_add_distr_l.
 remember (Nbar.max (stop a + stop b) (stop a + stop c)) as x.
 destruct (Nbar.lt_dec (fin k) x) as [H₂| H₂]; subst x.
  unfold series_nth; simpl.
  destruct (Nbar.lt_dec (fin k) (stop a + stop b)) as [H₃| H₃].
   apply Lfield.add_compat_l.
   destruct (Nbar.lt_dec (fin k) (stop a + stop c)) as [H₄| H₄].
    reflexivity.

    apply add_le_convol_mul_is_0, Nbar.nlt_ge; assumption.

   destruct (Nbar.lt_dec (fin k) (stop a + stop c)) as [H₄| H₄].
    apply Lfield.add_compat_r.
    apply add_le_convol_mul_is_0, Nbar.nlt_ge; assumption.

    apply Nbar.max_lt_iff in H₂.
    destruct H₂; contradiction.

  rewrite Nbar.add_max_distr_l in H₂.
  contradiction.

 remember (Nbar.max (stop a + stop b) (stop a + stop c)) as x.
 destruct (Nbar.lt_dec (fin k) x) as [H₂| H₂]; subst x.
  rewrite Nbar.add_max_distr_l in H₂.
  contradiction.

  reflexivity.
Qed.

Add Parametric Morphism : series_add
with  signature eq_series ==> eq_series ==> eq_series
as series_add_morph.
Proof.
intros s₁ s₂ Heq₁ s₃ s₄ Heq₂.
inversion Heq₁; subst.
inversion Heq₂; subst.
constructor; simpl.
intros i.
unfold series_nth; simpl.
unfold series_nth in H; simpl in H.
unfold series_nth in H0; simpl in H0.
pose proof (H i) as Hi₁.
pose proof (H0 i) as Hi₂.
clear H H0.
unfold series_nth.
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

   rewrite Lfield.add_0_l; reflexivity.

 destruct lt₁ as [Hlt₁| Hge₁].
  exfalso; apply Hge₅; clear Hge₅.
  apply Nbar.max_lt_iff; left; assumption.

  destruct lt₃ as [Hlt₃| Hge₃].
   exfalso; apply Hge₅; clear Hge₅.
   apply Nbar.max_lt_iff; right; assumption.

   destruct lt₆ as [Hlt₆| Hge₆]; [ idtac | reflexivity ].
   rewrite <- Hi₁, <- Hi₂.
   rewrite Lfield.add_0_l; reflexivity.
Qed.

Add Parametric Morphism : (series_nth rng)
with signature eq ==> eq_series ==> (Lfield.eq rng)
as series_nth_morph.
Proof.
intros s₁ s₂ i Heq.
inversion Heq; subst.
apply H.
Qed.

Lemma eq_series_eq : ∀ a b, a = b → eq_series a b.
Proof. intros; subst a; reflexivity. Qed.

Theorem series_add_compat_l : ∀ a b c, (a = b)%ser → (c + a = c + b)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_compat_l : ∀ a b c, (a = b)%ser → (c * a = c * b)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_compat_r : ∀ a b c, (a = b)%ser → (a * c = b * c)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_add_distr_r : ∀ a b c, ((a + b) * c = a * c + b * c)%ser.
Proof.
intros a b c.
rewrite series_mul_comm, series_mul_add_distr_l.
rewrite series_mul_comm.
apply series_add_compat_l.
apply series_mul_comm.
Qed.

Theorem series_neq_1_0 : (1 ≠ 0)%ser.
Proof.
intros H.
inversion_clear H.
pose proof (H0 O) as H.
rewrite series_nth_series_0 in H.
unfold series_nth in H.
simpl in H.
destruct (Nbar.lt_dec 0 1) as [H₁| H₁].
 revert H; apply Lfield.neq_1_0.

 apply H₁, Nbar.lt_0_1.
Qed.

Definition series_ring : Lfield.r (series α) :=
  {| Lfield.zero := series_0;
     Lfield.one := series_1;
     Lfield.add := series_add;
     Lfield.mul := series_mul;
     Lfield.opp := series_opp;
     Lfield.eq := eq_series;
     Lfield.eq_refl := eq_series_refl;
     Lfield.eq_sym := eq_series_sym;
     Lfield.eq_trans := eq_series_trans;
     Lfield.neq_1_0 := series_neq_1_0;
     Lfield.add_comm := series_add_comm;
     Lfield.add_assoc := series_add_assoc;
     Lfield.add_0_l := series_add_0_l;
     Lfield.add_opp_l := series_add_opp_l;
     Lfield.add_compat_l := series_add_compat_l;
     Lfield.mul_comm := series_mul_comm;
     Lfield.mul_assoc := series_mul_assoc;
     Lfield.mul_1_l := series_mul_1_l;
     Lfield.mul_compat_l := series_mul_compat_l;
     Lfield.mul_add_distr_l := series_mul_add_distr_l |}.

Fixpoint term_inv c s n :=
  if zerop n then Lfield.inv fld (series_nth rng O s)
  else
    match c with
    | O => Lfield.zero rng
    | S c₁ =>
        (- Lfield.inv fld (series_nth rng 0 s) *
         Σ (i = 1, n)   series_nth rng i s * term_inv c₁ s (n - i)%nat)%rng
    end.

Definition series_inv s :=
  {| terms i := term_inv i s i;
     stop := ∞ |}.

Notation "s [ i ]" := (series_nth rng i s) (at level 1) : ring_scope.

(**)
Lemma zzz : ∀ k a a',
  a' = series_inv a
  → (convol_mul a a' (S k) =
      Lfield.inv fld a[0] *
       (a [S k] -
        Σ (i = 1, S k)   Σ (j = 0, i - 1)   a [i-j] * a [S k-i] * a'[j]))%rng.
Proof.
bbb.
*)

(**)
Theorem series_mul_inv_r : ∀ a,
  (series_nth rng 0 a ≠ 0)%rng
  → (a * series_inv a = 1)%ser.
Proof.
intros a Ha.
constructor; intros i.
unfold series_nth; simpl.
rewrite Nbar.add_comm; simpl.
destruct (Nbar.lt_dec (fin i) ∞) as [H₁| H₁].
 destruct (Nbar.lt_dec (fin i) 1) as [H₂| H₂].
  apply Nbar.fin_lt_mono in H₂.
  apply Nat.lt_1_r in H₂; subst i.
  unfold convol_mul.
  do 2 rewrite sigma_only_one.
  rewrite delta_id, Lfield.mul_1_l.
  unfold series_nth; simpl.
  clear H₁.
  destruct (Nbar.lt_dec 0 ∞) as [H₁| H₁].
   destruct (Nbar.lt_dec 0 (stop a)) as [H₂| H₂].
    unfold series_nth; simpl.
    unfold series_nth in Ha.
    destruct (Nbar.lt_dec 0 (stop a)) as [H₃| H₃].
     unfold rng.
     rewrite Lfield.mul_inv_r; [ reflexivity | idtac ].
     intros H; apply Ha; clear Ha.
     assumption.

     exfalso; apply Ha; reflexivity.

    exfalso; apply Ha.
    unfold series_nth; simpl.
    destruct (Nbar.lt_dec 0 (stop a)) as [H₃| H₃].
     contradiction.

     reflexivity.

   exfalso; apply H₁; constructor.

  clear H₁.
  destruct i; [ exfalso; apply H₂, Nbar.lt_0_1 | idtac ].
  clear H₂.
  rename i into k.
  rewrite zzz; [ idtac | reflexivity ].
bbb.
  induction i as (k, IHk) using Misc.all_lt_all.
  destruct k.
   unfold convol_mul.
   unfold sigma; simpl.
   rewrite delta_neq; [ idtac | intros H; discriminate H ].
   rewrite delta_id.
   rewrite delta_neq; [ idtac | intros H; discriminate H ].
   do 2 rewrite Lfield.mul_0_l.
   do 2 rewrite Lfield.mul_1_l.
   do 2 rewrite Lfield.add_0_l.
   do 3 rewrite Lfield.add_0_r.
   unfold series_nth.
   destruct (Nbar.lt_dec 0 (stop (series_inv a))) as [H₁| H₁]; simpl in H₁.
    destruct (Nbar.lt_dec 1 (stop a)) as [H₂| H₂].
     destruct (Nbar.lt_dec 1 (stop (series_inv a))) as [H₃| H₃]; simpl in H₃.
      destruct (Nbar.lt_dec 0 (stop a)) as [H₄| H₄].
       simpl.
       rewrite sigma_only_one; simpl.
       unfold series_nth.
       destruct (Nbar.lt_dec 0 (stop a)) as [H₅| H₅].
        destruct (Nbar.lt_dec 1 (stop a)) as [H₆| H₆].
         do 2 rewrite <- Lfield.mul_assoc.
         unfold rng.
         rewrite Lfield.mul_inv_l.
          rewrite Lfield.mul_1_r.
          rewrite Lfield.mul_opp_l.
          unfold rng.
          rewrite Lfield.add_opp_r.
          reflexivity.

          intros H.
          apply Ha.
          unfold series_nth.
          destruct (Nbar.lt_dec 0 (stop a)) as [H₇| H₇].
           assumption.

           reflexivity.

         contradiction.

        contradiction.

       exfalso; apply H₄.
       eapply Nbar.lt_trans; [ idtac | eassumption ].
       apply Nbar.lt_0_1.

      exfalso; apply H₃; constructor.

     destruct (Nbar.lt_dec 1 (stop (series_inv a))) as [H₃| H₃]; simpl in H₃.
      destruct (Nbar.lt_dec 0 (stop a)) as [H₄| H₄].
       rewrite Lfield.mul_0_r, Lfield.add_0_l.
       simpl.
       rewrite sigma_only_one; simpl.
       unfold series_nth; simpl.
       destruct (Nbar.lt_dec 1 (stop a)) as [H₅| H₅].
        contradiction.

        rewrite Lfield.mul_0_l, Lfield.mul_0_r.
        rewrite Lfield.mul_0_l; reflexivity.

       do 2 rewrite Lfield.mul_0_r.
       rewrite Lfield.add_0_l; reflexivity.

      exfalso; apply H₃; constructor.

    exfalso; apply H₁; constructor.

   assert (k < S k)%nat as IH by omega.
   apply IHk in IH.
   unfold convol_mul in IH |- *.
   rewrite zzz.
   rewrite yyy.

bbb.
*)
