(* $Id: Ps_mul.v,v 2.10 2013-12-03 18:46:24 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Nbar.
Require Import Misc.
Require Import Series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_add_compat.

Set Implicit Arguments.

(* ps_mul *)

Definition nz_mul nz₁ nz₂ :=
  {| nz_terms :=
       series_mul
         (series_stretch (cm_factor nz₁ nz₂) (nz_terms nz₁))
         (series_stretch (cm_factor nz₂ nz₁) (nz_terms nz₂));
     nz_valnum :=
       (nz_valnum nz₁ * ' nz_comden nz₂ + nz_valnum nz₂ * ' nz_comden nz₁)%Z;
     nz_comden :=
       cm nz₁ nz₂ |}.

Definition ps_mul (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => NonZero (nz_mul nz₁ nz₂)
      | Zero => ps₂
      end
  | Zero => ps₁
  end.

Delimit Scope ps_scope with ps.
Notation "a + b" := (ps_add a b) : ps_scope.
Notation "a ₊ b" := (ps_add₂ a b) (at level 50) : ps_scope.
Notation "a * b" := (ps_mul a b) : ps_scope.

Delimit Scope nz_scope with nz.
Notation "a + b" := (nz_add a b) : nz_scope.
Notation "a ₊ b" := (nz_add₂ a b) (at level 50) : nz_scope.
Notation "a * b" := (nz_mul a b) : nz_scope.
Notation "a = b" := (eq_nz a b) : nz_scope.

Lemma nz_norm_mul_comm : ∀ nz₁ nz₂,
  normalise_nz (nz_mul nz₁ nz₂) ≐ normalise_nz (nz_mul nz₂ nz₁).
Proof.
intros nz₁ nz₂.
unfold normalise_nz; simpl.
remember (series_stretch (cm_factor nz₁ nz₂) (nz_terms nz₁)) as s₁ eqn:Hs₁ .
remember (series_stretch (cm_factor nz₂ nz₁) (nz_terms nz₂)) as s₂ eqn:Hs₂ .
rewrite series_mul_comm.
remember (null_coeff_range_length rng (series_mul s₂ s₁) 0) as n eqn:Hn .
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; constructor; simpl.
 unfold gcd_nz; simpl.
 rewrite series_mul_comm.
 f_equal; [ f_equal; apply Z.add_comm | f_equal ].
 f_equal; [ f_equal; apply Z.add_comm | idtac ].
 unfold cm; rewrite Pos.mul_comm; reflexivity.

 unfold cm; rewrite Pos.mul_comm, series_mul_comm.
 unfold gcd_nz; simpl.
 do 3 f_equal.
 f_equal; [ f_equal; apply Z.add_comm | idtac ].
 unfold cm; rewrite Pos.mul_comm; reflexivity.

 unfold gcd_nz; simpl.
 unfold cm; rewrite Pos.mul_comm, series_mul_comm.
 remember (nz_valnum nz₁ * ' nz_comden nz₂)%Z as x eqn:Hx .
 remember (nz_valnum nz₂ * ' nz_comden nz₁)%Z as y eqn:Hy .
 replace (x + y)%Z with (y + x)%Z by apply Z.add_comm.
 reflexivity.
Qed.

Theorem ps_mul_comm : ∀ ps₁ ps₂, ps_mul ps₁ ps₂ ≈ ps_mul ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_mul; simpl.
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
 constructor.
 apply nz_norm_mul_comm.

 destruct ps₂; reflexivity.
Qed.

Lemma fold_series_1 :
  {| terms := λ _, Lfield.one rng; stop := 1 |} = series_1.
Proof. reflexivity. Qed.

Lemma stretch_series_1 : ∀ k, series_stretch k series_1 ≃ series_1.
Proof.
intros k.
constructor; intros i.
unfold series_nth_rng; simpl.
rewrite Nat.add_0_r.
destruct (Nbar.lt_dec (fin i) (fin (Pos.to_nat k))) as [H₁| H₁].
 destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂].
  unfold series_nth_rng; simpl.
  apply Nat.mod_divides in H₂; auto.
  destruct H₂ as (c, Hc); rewrite Hc.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; auto.
  destruct (Nbar.lt_dec (fin c) 1) as [H₂| H₂].
   apply Nbar.fin_lt_mono in H₂.
   apply lt_n_Sm_le, Nat.le_0_r in H₂; subst c.
   rewrite Nat.mul_0_l.
   destruct (Nbar.lt_dec 0 1) as [H₂| H₂]; [ reflexivity | idtac ].
   exfalso; apply H₂, Nbar.lt_0_1.

   destruct (Nbar.lt_dec (fin (c * Pos.to_nat k)) 1) as [H₃| H₃].
    exfalso; apply H₂.
    apply Nbar.fin_lt_mono in H₃.
    apply Nbar.fin_lt_mono.
    apply lt_n_Sm_le, Nat.le_0_r in H₃.
    apply Nat.eq_mul_0_l in H₃; auto.
    subst c; apply Nat.lt_0_1.

    reflexivity.

  destruct (Nbar.lt_dec (fin i) 1) as [H₃| H₃].
   apply Nbar.fin_lt_mono in H₃.
   destruct i.
    rewrite Nat.mod_0_l in H₂; auto.
    exfalso; revert H₂; apply Nat.lt_irrefl.

    apply lt_S_n in H₃.
    apply Nat.nlt_ge in H₃.
    exfalso; apply H₃, Nat.lt_0_succ.

   reflexivity.

 destruct (Nbar.lt_dec (fin i) 1) as [H₂| H₂].
  apply Nbar.fin_lt_mono in H₂.
  apply lt_n_Sm_le, Nat.le_0_r in H₂; subst i.
  exfalso; apply H₁, Nbar.fin_lt_mono.
  apply Pos2Nat.is_pos.

  reflexivity.
Qed.

Theorem ps_mul_1_l : ∀ ps, ps_mul ps_one ps ≈ ps.
Proof.
intros ps; simpl.
destruct ps as [nz| ]; [ constructor | reflexivity ].
unfold normalise_nz; simpl.
unfold cm_factor; simpl.
rewrite fold_series_1, series_stretch_1.
rewrite stretch_series_1, series_mul_1_l.
remember (null_coeff_range_length rng (nz_terms nz) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; constructor; simpl.
 rewrite stretch_series_1, series_stretch_1, series_mul_1_l.
 unfold gcd_nz; simpl.
 rewrite Z.mul_1_r; reflexivity.

 rewrite stretch_series_1, series_stretch_1, series_mul_1_l.
 unfold gcd_nz; simpl.
 rewrite Z.mul_1_r; reflexivity.

 rewrite stretch_series_1, series_stretch_1, series_mul_1_l.
 unfold gcd_nz; simpl.
 rewrite Z.mul_1_r; reflexivity.
Qed.

Theorem ps_mul_1_r : ∀ ps, ps_mul ps ps_one ≈ ps.
Proof. intros ps. rewrite ps_mul_comm. apply ps_mul_1_l. Qed.

Theorem ps_mul_0_l : ∀ ps, ps_mul ps_zero ps ≈ ps_zero.
Proof. intros ps; constructor. Qed.

Theorem ps_mul_0_r : ∀ ps, ps_mul ps ps_zero ≈ ps_zero.
Proof. intros ps. rewrite ps_mul_comm. apply ps_mul_0_l. Qed.

Theorem ps_neq_1_0 : not (ps_one ≈ ps_zero).
Proof.
intros H.
inversion_clear H.
inversion_clear H0.
pose proof (H O) as H₁.
unfold series_nth_rng in H₁.
simpl in H₁.
destruct (Nbar.lt_dec 0 0) as [H₂| H₂].
 revert H₂; apply Nbar.lt_irrefl.

 destruct (Nbar.lt_dec 0 1) as [H₃| H₃].
  apply Lfield.neq_1_0 in H₁; contradiction.

  apply H₃, Nbar.lt_0_1.
Qed.

Lemma sigma_aux_add : ∀ f b k₁ k₂,
  sigma_aux b (k₁ + k₂) f ≍ (sigma_aux b k₁ f + sigma_aux (b + k₁) k₂ f)%rng.
Proof.
intros f b k₁ k₂.
revert b k₁.
induction k₂; intros.
 simpl.
 rewrite Nat.add_0_r, Lfield.add_0_r; reflexivity.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 rewrite IHk₂; simpl.
 rewrite <- Nat.add_succ_r.
 rewrite Lfield.add_assoc.
 apply Lfield.add_compat_r.
 clear k₂ IHk₂.
 revert b.
 induction k₁; intros; simpl.
  rewrite Nat.add_0_r.
  apply Lfield.add_comm.

  rewrite <- Lfield.add_assoc.
  rewrite IHk₁.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l; reflexivity.
Qed.

Lemma sigma_add : ∀ f k₁ k₂,
  Σ (i = 0, k₁ + k₂)   f i
  ≍ (Σ (i = 0, k₁)   f i + Σ (i = S k₁, k₁ + k₂)   f i)%rng.
Proof.
intros f k₁ k₂.
unfold sigma.
do 2 rewrite Nat.sub_0_r.
rewrite <- Nat.add_succ_l.
rewrite sigma_aux_add; simpl.
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Lemma sigma_aux_succ : ∀ f b k,
  sigma_aux b (S k) f ≍ (f b + sigma_aux (S b) k f)%rng.
Proof. reflexivity. Qed.

Lemma sigma_aux_twice_twice : ∀ f n k,
  sigma_aux (n + n)%nat (k + k)%nat f
  ≍ sigma_aux n k (λ i, f (i + i)%nat + f (i + i + 1)%nat)%rng.
Proof.
intros f n k.
revert n; induction k; intros; [ reflexivity | simpl ].
rewrite <- Lfield.add_assoc.
apply Lfield.add_compat_l.
rewrite Nat.add_succ_r; simpl.
rewrite Nat.add_1_r.
apply Lfield.add_compat_l.
rewrite <- Nat.add_succ_r, <- Nat.add_succ_l.
apply IHk.
Qed.

Lemma sigma_aux_mul_sigma_aux_sigma_aux : ∀ f k n,
  sigma_aux 0 (S k * S n) f
  ≍ sigma_aux 0 (S k) (λ i, sigma_aux 0 (S n) (λ j, f (i * S n + j)%nat)).
Proof.
intros f k n.
revert n; induction k; intros.
 simpl; rewrite Nat.add_0_r, Lfield.add_0_r; reflexivity.

 remember (S n) as x.
 remember (S k) as y.
 simpl; subst x y.
 rewrite Nat.add_comm.
 rewrite sigma_aux_add, IHk.
 symmetry; rewrite Lfield.add_comm.
 symmetry.
 rewrite sigma_aux_succ.
 rewrite Lfield.add_shuffle0, Lfield.add_comm.
 symmetry.
 replace (S k) with (k + 1)%nat by omega.
 rewrite sigma_aux_add.
 rewrite <- Lfield.add_assoc.
 apply Lfield.add_compat_l.
 simpl.
 rewrite Lfield.add_comm.
 apply Lfield.add_compat_l.
 symmetry; rewrite Nat.add_comm; simpl.
 rewrite Nat.add_0_r, Lfield.add_0_r.
 apply Lfield.add_compat_l.
 apply sigma_aux_compat; intros i Hi; simpl.
 rewrite Nat.add_succ_r; reflexivity.
Qed.

Lemma sigma_mul_sigma_sigma : ∀ f n k,
  (0 < n)%nat
  → (0 < k)%nat
    → Σ (i = 0, k * n - 1)   f i
      ≍ Σ (i = 0, k - 1)   Σ (j = 0, n - 1)   f (i * n + j)%nat.
Proof.
intros f n k Hn Hk.
unfold sigma.
do 2 rewrite Nat.sub_0_r.
destruct n; [ exfalso; revert Hn; apply Nat.lt_irrefl | clear Hn ].
destruct k; [ exfalso; revert Hk; apply Nat.lt_irrefl | clear Hk ].
rewrite Nat.sub_succ, Nat.sub_0_r.
rewrite <- Nat.sub_succ_l, Nat.sub_succ, Nat.sub_0_r.
 rewrite sigma_aux_mul_sigma_aux_sigma_aux.
 apply sigma_aux_compat; intros i Hi.
 rewrite Nat.sub_succ, Nat.sub_0_r, Nat.sub_0_r.
 reflexivity.

 simpl; apply le_n_S, Nat.le_0_l.
Qed.

Lemma sigma_only_one : ∀ f n, Σ (i = n, n)   f i ≍ f n.
Proof.
intros f n.
unfold sigma.
rewrite Nat.sub_succ_l; [ idtac | reflexivity ].
rewrite Nat.sub_diag; simpl.
rewrite Lfield.add_0_r; reflexivity.
Qed.

Lemma inserted_0_sigma : ∀ f g k n,
  n ≠ O
  → (∀ i, i mod n ≠ O → f i ≍ 0%rng)
    → (∀ i, f (n * i)%nat ≍ g i)
      → Σ (i = 0, k * n)   f i ≍ Σ (i = 0, k)   g i.
Proof.
intros f g k n Hn Hf Hfg.
destruct k.
 rewrite Nat.mul_0_l.
 apply sigma_compat; intros i (_, Hi).
 apply Nat.le_0_r in Hi; subst i.
 rewrite <- Hfg, Nat.mul_0_r; reflexivity.

 destruct n; [ exfalso; apply Hn; reflexivity | clear Hn ].
 replace (S k * S n)%nat with (S k * S n - 1 + 1)%nat .
  rewrite sigma_add.
  rewrite sigma_mul_sigma_sigma; try apply Nat.lt_0_succ.
  rewrite Nat_sub_succ_1, Nat.add_comm, sigma_only_one.
  symmetry.
  rewrite <- Nat.add_1_r, sigma_add, Nat.add_1_r.
  rewrite sigma_only_one, Lfield.add_comm, <- Hfg.
  symmetry.
  rewrite Lfield.add_comm.
  rewrite Nat.add_sub_assoc.
   rewrite Nat.add_comm, Nat.add_sub, Nat.mul_comm.
   apply Lfield.add_compat_l, sigma_compat; intros i Hi.
   rewrite Nat_sub_succ_1.
   rewrite <- Hfg.
   rewrite Nat.mul_comm.
   rewrite sigma_only_one_non_0 with (v := O).
    rewrite Nat.add_0_r, Nat.mul_comm.
    reflexivity.

    split; [ reflexivity | apply Nat.le_0_l ].

    intros j Hjn Hj.
    rewrite Hf; [ reflexivity | idtac ].
    rewrite Nat.add_comm.
    rewrite Nat.mul_comm, Nat.mod_add; auto.
    intros H; apply Hj; clear Hj.
    apply Nat.mod_divides in H; auto.
    destruct H as (c, Hc).
    destruct c.
     rewrite Nat.mul_0_r in Hc; assumption.

     rewrite Hc in Hjn.
     rewrite Nat.mul_comm in Hjn.
     simpl in Hjn.
     destruct Hjn as (_, H).
     apply Nat.nlt_ge in H.
     exfalso; apply H.
     apply le_n_S, Nat.le_add_r.

   simpl; apply le_n_S, Nat.le_0_l.

  simpl.
  rewrite Nat.sub_0_r.
  rewrite Nat.add_comm; reflexivity.
Qed.

Lemma delta_mul_cancel_r : ∀ a b c, c ≠ O → δ (a * c) (b * c) ≍ δ a b.
Proof.
intros a b c Hc.
destruct (eq_nat_dec a b) as [H₁| H₁].
 subst a.
 do 2 rewrite delta_id; reflexivity.

 rewrite delta_neq.
  rewrite delta_neq; [ reflexivity | assumption ].

  intros H; apply H₁.
  apply Nat.mul_cancel_r in H; assumption.

Qed.

Lemma series_stretch_mul : ∀ a b k,
  series_stretch k (series_mul a b)
  ≃ series_mul (series_stretch k a) (series_stretch k b).
Proof.
intros a b k.
constructor; intros i.
unfold series_nth_rng; simpl.
rewrite <- Nbar.mul_add_distr_r.
remember ((stop a + stop b) * fin (Pos.to_nat k))%Nbar as x.
destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁]; [ subst x | reflexivity ].
destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂].
 apply Nat.mod_divides in H₂; auto.
 destruct H₂ as (c, Hc).
 rewrite Hc.
 rewrite Nat.mul_comm.
 rewrite Nat.div_mul; auto.
 unfold series_nth_rng; simpl.
 destruct (Nbar.lt_dec (fin c) (stop a + stop b)) as [H₂| H₂].
  unfold convol_mul; simpl.
  rename k into n, i into k.
  symmetry.
  apply inserted_0_sigma; auto.
   intros i Hi.
   apply all_0_sigma_0; intros j.
   rewrite shifted_in_stretched.
    rewrite Lfield.mul_0_l, Lfield.mul_0_r; reflexivity.

    apply neq_0_lt, Nat.neq_sym; assumption.

   intros i.
   apply inserted_0_sigma; auto.
    intros j Hj.
    rewrite delta_neq.
     rewrite Lfield.mul_0_l; reflexivity.

     intros H.
     apply Hj.
     apply Nat.mod_divides; auto.
     exists (c - i)%nat.
     rewrite Nat.mul_sub_distr_l.
     symmetry; apply Nat.add_sub_eq_l.
     symmetry; rewrite Nat.mul_comm; symmetry; assumption.

    intros j.
    rewrite <- Nat.mul_add_distr_l, Nat.mul_comm.
    rewrite delta_mul_cancel_r; auto.
    apply Lfield.mul_compat_l.
    rewrite series_nth_rng_mul_stretch.
    rewrite series_nth_rng_mul_stretch.
    reflexivity.

  exfalso; apply H₂.
  subst i.
  rewrite Nat.mul_comm in H₁.
  rewrite Nbar.fin_inj_mul in H₁.
  apply Nbar.mul_lt_mono_pos_r in H₁; auto.
   apply Nbar.fin_lt_mono, Pos2Nat.is_pos.

   intros H; discriminate H.

   intros H; discriminate H.

 unfold convol_mul.
 symmetry.
 apply all_0_sigma_0; intros j Hj.
 apply all_0_sigma_0; intros l Hl.
 destruct (eq_nat_dec (j + l) i) as [H₃| H₃].
  destruct (zerop (j mod Pos.to_nat k)) as [H₄| H₄].
   destruct (zerop (l mod Pos.to_nat k)) as [H₅| H₅].
    apply Nat.mod_divides in H₄; auto.
    apply Nat.mod_divides in H₅; auto.
    destruct H₄ as (c, Hc).
    destruct H₅ as (d, Hd).
    subst j l.
    subst i.
    rewrite <- Nat.mul_add_distr_l in H₂; auto.
    rewrite Nat.mul_comm in H₂.
    rewrite Nat.mod_mul in H₂; auto.
    exfalso; revert H₂; apply Nat.lt_irrefl.

    rewrite Lfield.mul_assoc, Lfield.mul_shuffle0.
    rewrite shifted_in_stretched; [ idtac | assumption ].
    rewrite Lfield.mul_0_r, Lfield.mul_0_l; reflexivity.

   rewrite Lfield.mul_assoc.
   rewrite shifted_in_stretched; [ idtac | assumption ].
   rewrite Lfield.mul_0_r, Lfield.mul_0_l; reflexivity.

  rewrite delta_neq; [ idtac | assumption ].
  rewrite Lfield.mul_0_l; reflexivity.
Qed.

Theorem ps_mul_assoc : ∀ ps₁ ps₂ ps₃,
  ps_mul ps₁ (ps_mul ps₂ ps₃) ≈ ps_mul (ps_mul ps₁ ps₂) ps₃.
Proof.
intros ps₁ ps₂ ps₃.
unfold ps_mul; simpl.
destruct ps₁ as [nz₁| ]; [ idtac | reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
destruct ps₃ as [nz₃| ]; [ constructor | reflexivity ].
unfold normalise_nz; simpl.
rewrite series_stretch_mul; symmetry.
rewrite series_stretch_mul; symmetry.
do 4 rewrite <- series_stretch_stretch.
unfold cm, cm_factor; simpl.
rewrite series_mul_assoc.
remember (nz_comden nz₂ * nz_comden nz₃)%positive as c₂₃ eqn:Hc₂₃ .
remember (nz_comden nz₃ * nz_comden nz₁)%positive as c₃₁ eqn:Hc₃₁ .
remember (nz_comden nz₁ * nz_comden nz₂)%positive as c₁₂ eqn:Hc₁₂ .
rewrite Pos.mul_comm in Hc₂₃; rewrite <- Hc₂₃.
rewrite Pos.mul_comm in Hc₃₁; rewrite <- Hc₃₁.
remember (series_stretch c₂₃ (nz_terms nz₁)) as s₁ eqn:Hs₁ .
remember (series_stretch c₃₁ (nz_terms nz₂)) as s₂ eqn:Hs₂ .
remember (series_stretch c₁₂ (nz_terms nz₃)) as s₃ eqn:Hs₃ .
remember (series_mul (series_mul s₁ s₂) s₃) as s₁₂₃ eqn:Hs₁₂₃ .
remember (null_coeff_range_length rng s₁₂₃ 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
unfold gcd_nz; simpl.
unfold cm; simpl.
unfold cm; simpl.
do 2 rewrite Z.mul_add_distr_r.
do 6 rewrite Pos2Z.inj_mul.
do 3 rewrite Z.mul_assoc.
do 2 rewrite Z.add_assoc.
constructor; constructor; simpl.
 f_equal.
  f_equal.
  f_equal.
   f_equal.
    rewrite Hc₂₃, Pos2Z.inj_mul, Z.mul_assoc, Z.mul_shuffle0.
    reflexivity.

    rewrite Z.mul_shuffle0; reflexivity.

   rewrite Hc₁₂, Pos2Z.inj_mul, Z.mul_assoc, Z.mul_shuffle0.
   reflexivity.

  f_equal.
   do 2 f_equal.
   f_equal; [ f_equal | idtac ]; apply Z.mul_shuffle0.

   do 2 rewrite series_stretch_mul.
   do 4 rewrite <- series_stretch_stretch.
   rewrite <- Hc₁₂, <- Hc₂₃, <- Hc₃₁.
   rewrite Pos.mul_comm, <- Hc₃₁.
   rewrite <- Hs₁, <- Hs₂, <- Hs₃.
   rewrite series_mul_assoc; reflexivity.

 do 2 f_equal.
 f_equal.
  do 2 f_equal.
  f_equal; [ f_equal | idtac ]; apply Z.mul_shuffle0.

  do 2 rewrite series_stretch_mul.
  do 4 rewrite <- series_stretch_stretch.
  rewrite <- Hc₁₂, <- Hc₂₃, <- Hc₃₁.
  rewrite Pos.mul_comm, <- Hc₃₁.
  rewrite <- Hs₁, <- Hs₂, <- Hs₃.
  rewrite series_mul_assoc; reflexivity.

 constructor; intros i.
 do 2 rewrite series_stretch_mul.
 do 4 rewrite <- series_stretch_stretch.
 rewrite <- Hc₁₂, <- Hc₂₃, <- Hc₃₁.
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul, Pos.mul_comm, <- Hc₂₃.
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul, Pos.mul_comm, <- Hc₃₁.
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul, Pos.mul_comm, <- Hc₁₂.
 symmetry.
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul, <- Hc₃₁.
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul, <- Hc₁₂.
 rewrite series_mul_assoc.
 rewrite <- Hs₁, <- Hs₂, <- Hs₃.
 reflexivity.
Qed.

Lemma eq_nz_mul_compat_r : ∀ nz₁ nz₂ nz₃,
  eq_nz nz₁ nz₂
  → eq_nz (nz_mul nz₁ nz₃) (nz_mul nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃ Heq.
induction Heq.
constructor; simpl.
 rewrite H, H0; reflexivity.

 unfold cm; simpl.
 rewrite H0; reflexivity.

 unfold cm_factor.
 rewrite H0, H1.
 reflexivity.
Qed.

Lemma eq_nz_mul_compat_l : ∀ nz₁ nz₂ nz₃,
  eq_nz nz₁ nz₂
  → eq_nz (nz_mul nz₃ nz₁) (nz_mul nz₃ nz₂).
Proof.
intros nz₁ nz₂ nz₃ Heq.
induction Heq.
constructor; simpl.
 rewrite H, H0; reflexivity.

 unfold cm; simpl.
 rewrite H0; reflexivity.

 unfold cm_factor.
 rewrite H0, H1.
 reflexivity.
Qed.

Lemma series_mul_stretch_mul_inf : ∀ a b k,
  series_mul (series_stretch k a) b
  ≃ series_mul_inf (series_stretch k (series_inf rng a))
      (series_inf rng b).
Proof.
intros a b l.
constructor; intros k.
unfold series_nth_rng; simpl.
destruct (Nbar.lt_dec (fin k) ∞) as [H| H]; [ clear H | exfalso ].
 remember (stop a * fin (Pos.to_nat l) + stop b)%Nbar as x.
 destruct (Nbar.lt_dec (fin k) x) as [H₁| H₁]; subst x.
  unfold convol_mul, convol_mul_inf.
  apply sigma_compat; intros i Hi.
  apply sigma_compat; intros j Hj.
  rewrite <- Lfield.mul_assoc.
  destruct (eq_nat_dec (i + j) k) as [H₂| H₂].
   rewrite H₂, delta_id.
   do 2 rewrite Lfield.mul_1_l.
   simpl.
   destruct (zerop (i mod Pos.to_nat l)) as [H₃| H₃].
    apply Nat.mod_divides in H₃; auto.
    destruct H₃ as (c, Hc).
    rewrite Hc.
    rewrite series_nth_rng_mul_stretch.
    rewrite Nat.mul_comm.
    rewrite Nat.div_mul; auto.
    rewrite series_nth_inf.
    reflexivity.

    rewrite shifted_in_stretched; [ reflexivity | assumption ].

   rewrite delta_neq; [ idtac | assumption ].
   do 2 rewrite Lfield.mul_0_l; reflexivity.

  symmetry.
  apply Nbar.nlt_ge in H₁.
  unfold convol_mul_inf.
  apply all_0_sigma_0; intros i Hi.
  apply all_0_sigma_0; intros j Hj.
  destruct (eq_nat_dec (i + j) k) as [H₂| H₂].
   rewrite H₂, delta_id.
   rewrite Lfield.mul_1_l.
   simpl.
   destruct (zerop (i mod Pos.to_nat l)) as [H₃| H₃].
    apply Nat.mod_divides in H₃; auto.
    destruct H₃ as (c, Hc).
    rewrite Hc.
    rewrite Nat.mul_comm.
    rewrite Nat.div_mul; auto.
    rewrite series_nth_inf.
    simpl.
    unfold series_nth_rng; simpl.
    destruct (Nbar.lt_dec (fin c) (stop a)) as [H₃| H₃].
     destruct (Nbar.lt_dec (fin j) (stop b)) as [H₄| H₄].
      rewrite <- H₂ in H₁.
      rewrite Nbar.fin_inj_add in H₁.
      apply Nbar.nlt_ge in H₁.
      exfalso; apply H₁.
      apply Nbar.lt_trans with (m := (fin i + stop b)%Nbar).
       apply Nbar.add_lt_mono_l; [ idtac | assumption ].
       intros H; discriminate H.

       remember (stop b) as st eqn:Hst .
       symmetry in Hst.
       destruct st as [st| ].
        apply Nbar.add_lt_mono_r; [ intros H; discriminate H | idtac ].
        rewrite Hc.
        rewrite Nbar.fin_inj_mul.
        rewrite Nbar.mul_comm.
        apply Nbar.mul_lt_mono_pos_r.
         apply Nbar.fin_lt_mono, Pos2Nat.is_pos.

         intros H; discriminate H.

         intros H; discriminate H.

         assumption.

        exfalso; apply H₁; simpl.
        rewrite Nbar.add_comm; constructor.

      rewrite Lfield.mul_0_r; reflexivity.

     rewrite Lfield.mul_0_l; reflexivity.

    rewrite Lfield.mul_0_l; reflexivity.

   rewrite delta_neq; [ idtac | assumption ].
   do 2 rewrite Lfield.mul_0_l; reflexivity.

 apply H; constructor.
Qed.

Lemma series_nth_lt_shift : ∀ a i n,
  (i < n)%nat
  → series_nth_rng rng i (series_shift n a) ≍ 0%rng.
Proof.
intros a i n Hin.
unfold series_nth_rng; simpl.
destruct (Nbar.lt_dec (fin i) (stop a + fin n)) as [H₁| H₁].
 destruct (lt_dec i n) as [| H₂]; [ reflexivity | contradiction ].

 reflexivity.
Qed.

Lemma sigma_add_add_sub : ∀ f b k n,
  Σ (i = b, k)   f i ≍ Σ (i = b + n, k + n)   f (i - n)%nat.
Proof.
intros f b k n.
unfold sigma.
replace (S (k + n) - (b + n))%nat with (S k - b)%nat by omega.
apply sigma_aux_compat.
intros i Hi.
replace (b + n + i - n)%nat with (b + i)%nat by omega.
reflexivity.
Qed.

Lemma series_shift_mul : ∀ a b n,
  series_shift n (series_mul a b) ≃ series_mul (series_shift n a) b.
Proof.
(* à nettoyer *)
intros a b n.
constructor; intros k.
unfold series_nth_rng; simpl.
rewrite Nbar.add_shuffle0.
destruct (Nbar.lt_dec (fin k) (stop a + fin n + stop b)) as [H₁| H₁].
 destruct (lt_dec k n) as [H₂| H₂].
  symmetry; unfold convol_mul; simpl.
  apply all_0_sigma_0; intros i Hi.
  apply all_0_sigma_0; intros j Hj.
  destruct (eq_nat_dec (i + j) k) as [H₃| H₃].
   rewrite series_nth_lt_shift.
    rewrite Lfield.mul_0_l, Lfield.mul_0_r; reflexivity.

    eapply le_lt_trans; [ idtac | eassumption ].
    rewrite <- H₃; apply Nat.le_add_r.

   rewrite delta_neq; [ idtac | assumption ].
   rewrite Lfield.mul_0_l; reflexivity.

  unfold convol_mul; simpl.
  apply Nat.nlt_ge in H₂.
  symmetry.
  destruct n.
   rewrite Nat.sub_0_r.
   apply sigma_compat; intros i Hi.
   apply sigma_compat; intros j Hj.
   rewrite series_shift_0; reflexivity.

   assert (k = (n + (k - n))%nat) as H by omega.
   rewrite H in |- * at 1; clear H.
   rewrite sigma_add.
   rewrite Lfield.add_comm.
   rewrite Nat.add_sub_assoc; [ idtac | omega ].
   rewrite Nat.add_comm, Nat.add_sub.
   rewrite Lfield.add_comm.
   rewrite all_0_sigma_0.
    Focus 2.
    intros i Hi.
    rewrite all_0_sigma_0; [ reflexivity | idtac ].
    intros j Hj.
    rewrite series_nth_lt_shift; [ idtac | omega ].
    rewrite Lfield.mul_0_l, Lfield.mul_0_r; reflexivity.

    rewrite Lfield.add_0_l.
    symmetry.
    rewrite sigma_add_add_sub with (n := S n).
    rewrite Nat.add_0_l, Nat.sub_add; [ idtac | assumption ].
    apply sigma_compat; intros i Hi.
    symmetry.
    assert (k = (k - S n + S n)%nat) as H by omega.
    rewrite H in |- * at 1; clear H.
    rewrite sigma_add.
    rewrite Lfield.add_comm.
    rewrite Nat.sub_add; [ idtac | assumption ].
    rewrite all_0_sigma_0.
     rewrite Lfield.add_0_l.
     apply sigma_compat; intros j Hj.
     assert (i = i - S n + S n)%nat as H by omega.
     rewrite H in |- * at 2.
     rewrite series_nth_add_shift.
     apply Lfield.mul_compat_r.
     rewrite <- Nat.add_sub_swap; [ idtac | destruct Hi; assumption ].
     destruct (eq_nat_dec (i + j) k) as [H₃| H₃].
      rewrite H₃.
      do 2 rewrite delta_id; reflexivity.

      rewrite delta_neq; [ idtac | assumption ].
      rewrite delta_neq; [ reflexivity | idtac ].
      clear H.
      intros H; apply H₃.
      omega.

     intros j Hj.
     rewrite delta_neq.
      rewrite Lfield.mul_0_l; reflexivity.

      intros H.
      omega.

 reflexivity.
Qed.

Lemma normalise_nz_mul_adjust_l : ∀ nz₁ nz₂ n k,
  normalise_nz (nz_mul nz₁ nz₂) ≐
  normalise_nz (nz_mul (adjust_nz n k nz₁) nz₂).
Proof.
intros nz₁ nz₂ n k.
remember (Pos.to_nat (nz_comden nz₂) * n)%nat as m eqn:Hm .
rewrite nz_adjust_eq with (n := m) (k := k); subst m.
unfold nz_mul; simpl.
unfold adjust_nz; simpl.
unfold cm, cm_factor; simpl.
rewrite Pos2Z.inj_mul, Z.mul_assoc.
rewrite Z.mul_sub_distr_r.
rewrite Z.mul_shuffle0.
rewrite <- Z.add_sub_swap.
rewrite <- Z.mul_add_distr_r.
rewrite Nat.mul_comm.
rewrite Nat2Z.inj_mul.
rewrite positive_nat_Z.
rewrite Pos_mul_shuffle0.
rewrite series_stretch_mul.
rewrite stretch_shift_series_distr.
do 3 rewrite <- series_stretch_stretch.
rewrite series_shift_mul.
rewrite Pos.mul_comm.
rewrite series_mul_comm, Pos.mul_comm, series_mul_comm.
reflexivity.
Qed.

Lemma nz_norm_mul_compat_r : ∀ nz₁ nz₂ nz₃,
  normalise_nz nz₁ ≐ normalise_nz nz₂
  → normalise_nz (nz_mul nz₁ nz₃) ≐ normalise_nz (nz_mul nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃ Heq.
remember (normalise_nz nz₁) as ps₁ eqn:Hps₁ .
remember (normalise_nz nz₂) as ps₂ eqn:Hps₂ .
symmetry in Hps₁, Hps₂.
destruct ps₁ as [nz'₁| ].
 destruct ps₂ as [nz'₂| ]; [ idtac | inversion Heq ].
 apply normalised_exists_adjust in Hps₁.
 apply normalised_exists_adjust in Hps₂.
 destruct Hps₁ as (n₁, (k₁, Hps₁)).
 destruct Hps₂ as (n₂, (k₂, Hps₂)).
 inversion Heq; subst.
 apply eq_nz_mul_compat_r with (nz₃ := nz₃) in Hps₁.
 apply eq_nz_mul_compat_r with (nz₃ := nz₃) in Hps₂.
 rewrite Hps₁, Hps₂.
 rewrite <- normalise_nz_mul_adjust_l.
 rewrite <- normalise_nz_mul_adjust_l.
 apply eq_nz_mul_compat_r with (nz₃ := nz₃) in H1.
 rewrite H1; reflexivity.

 destruct ps₂ as [nz'₂| ]; [ inversion Heq | idtac ].
 apply eq_nz_adjust_zero_neg_zero in Hps₁.
 apply eq_nz_adjust_zero_neg_zero in Hps₂.
 destruct Hps₁ as (n₁, (n₂, (k₁, (k₂, Hps₁)))).
 destruct Hps₂ as (n₃, (n₄, (k₃, (k₄, Hps₂)))).
 apply eq_nz_mul_compat_r with (nz₃ := nz₃) in Hps₁.
 apply eq_nz_mul_compat_r with (nz₃ := nz₃) in Hps₂.
 rewrite normalise_nz_mul_adjust_l with (n := n₁) (k := k₁).
 rewrite Hps₁; symmetry.
 rewrite normalise_nz_mul_adjust_l with (n := n₃) (k := k₃).
 rewrite Hps₂; symmetry.
 rewrite <- normalise_nz_mul_adjust_l.
 rewrite <- normalise_nz_mul_adjust_l.
 reflexivity.
Qed.

Lemma ps_mul_0_l_compat_r : ∀ nz₁ nz₂,
  NonZero nz₁ ≈ Zero α
  → NonZero (nz_mul nz₁ nz₂) ≈ Zero α.
Proof.
intros nz₁ nz₂ Heq.
constructor.
inversion Heq; subst.
unfold nz_mul; simpl.
rewrite H0.
rewrite series_stretch_series_0.
rewrite series_mul_0_l.
reflexivity.
Qed.

Theorem ps_mul_compat_r : ∀ ps₁ ps₂ ps₃,
  ps₁ ≈ ps₂
  → (ps₁ * ps₃)%ps ≈ (ps₂ * ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ H₁₂.
destruct ps₃ as [nz₃| ]; [ idtac | do 2 rewrite ps_mul_0_r; reflexivity ].
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ]; [ idtac | simpl ].
  constructor.
  apply nz_norm_mul_compat_r.
  inversion H₁₂; assumption.

  apply ps_mul_0_l_compat_r; assumption.

 destruct ps₂ as [nz₂| ]; [ simpl | reflexivity ].
 symmetry; apply ps_mul_0_l_compat_r.
 symmetry; assumption.
Qed.

Theorem ps_mul_compat_l : ∀ ps₁ ps₂ ps₃,
  ps₁ ≈ ps₂
  → (ps₃ * ps₁)%ps ≈ (ps₃ * ps₂)%ps.
Proof.
intros ps₁ ps₂ ps₃ Heq.
rewrite ps_mul_comm; symmetry.
rewrite ps_mul_comm; symmetry.
apply ps_mul_compat_r; assumption.
Qed.

Add Parametric Morphism : nz_mul
  with signature eq_nz ==> eq_nz ==> eq_nz
  as nz_mul_morph.
Proof.
intros nz₁ nz₃ Heq₁ nz₂ nz₄ Heq₂.
rewrite eq_nz_mul_compat_l; [ idtac | eassumption ].
rewrite eq_nz_mul_compat_r; [ idtac | eassumption ].
reflexivity.
Qed.

Lemma normalise_nz_mul_add_adjust_l : ∀ nz₁ nz₂ nz₃ n k,
  normalise_nz (nz₁ * (nz₂ + nz₃))%nz
  ≐ normalise_nz (nz₁ * (adjust_nz n k nz₂ + nz₃))%nz.
Proof.
bbb.

Theorem ps_mul_add_distr_l : ∀ ps₁ ps₂ ps₃,
  (ps₁ * (ps₂ + ps₃))%ps ≈ (ps₁ * ps₂ + ps₁ * ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃.
destruct ps₁ as [nz₁| ]; [ simpl | reflexivity ].
destruct ps₂ as [nz₂| ]; [ simpl | reflexivity ].
destruct ps₃ as [nz₃| ]; [ simpl | reflexivity ].
constructor.
remember (normalise_nz nz₁) as ps₁ eqn:Hps₁ .
remember (normalise_nz nz₂) as ps₂ eqn:Hps₂ .
remember (normalise_nz nz₃) as ps₃ eqn:Hps₃ .
symmetry in Hps₁, Hps₂, Hps₃.
destruct ps₁ as [nz'₁| ].
 destruct ps₂ as [nz'₂| ].
  destruct ps₃ as [nz'₃| ].
   apply normalised_exists_adjust in Hps₁.
   apply normalised_exists_adjust in Hps₂.
   apply normalised_exists_adjust in Hps₃.
   destruct Hps₁ as (n₁, (k₁, Hps₁)).
   destruct Hps₂ as (n₂, (k₂, Hps₂)).
   destruct Hps₃ as (n₃, (k₃, Hps₃)).
   rewrite Hps₁, Hps₂, Hps₃.
   rewrite <- normalise_nz_mul_adjust_l.
   rewrite <- normalise_nz_mul_add_adjust_l.
   rewrite nz_add_comm.
   rewrite <- normalise_nz_mul_add_adjust_l.
   rewrite nz_add_comm.
bbb.

intros ps₁ ps₂ ps₃.
destruct ps₁ as [nz₁| ]; [ simpl | reflexivity ].
destruct ps₂ as [nz₂| ]; [ simpl | reflexivity ].
destruct ps₃ as [nz₃| ]; [ simpl | reflexivity ].
constructor.
pose proof (eq_nz_norm_add_add₂ nz₂ nz₃) as H.
rewrite nz_norm_mul_comm.
rewrite nz_norm_mul_compat_r; [ clear H | eassumption ].
rewrite eq_nz_norm_add_add₂.
rewrite nz_norm_mul_comm.
bbb.
remember (normalise_nz (nz₁ * (nz₂ ₊ nz₃))%nz) as ps₁ eqn:Hps₁ .
remember (normalise_nz (nz₁ * nz₂ ₊ nz₁ * nz₃)%nz) as ps₂ eqn:Hps₂ .
symmetry in Hps₁, Hps₂.
destruct ps₁ as [nz'₁| ].
 destruct ps₂ as [nz'₂| ].
  apply normalised_exists_adjust in Hps₁.
  apply normalised_exists_adjust in Hps₂.
  destruct Hps₁ as (n₁, (k₁, Hps₁)).
  destruct Hps₂ as (n₂, (k₂, Hps₂)).
  constructor.
  inversion Hps₁; subst.
  inversion Hps₂; subst.
  constructor; simpl.
   Focus 2.
   move H0 at bottom.
   move H3 at bottom.
   simpl in H0, H3.
   unfold cm in H0, H3.
   simpl in H0, H3.
   unfold cm_factor in H0.
   rewrite Pos.mul_assoc in H0.
   rewrite Pos.mul_assoc, Pos_mul_shuffle0 in H3.
   rewrite H0 in H3.
bbb.

intros ps₁ ps₂ ps₃.
destruct ps₁ as [nz₁| ]; [ simpl | reflexivity ].
destruct ps₂ as [nz₂| ]; [ simpl | reflexivity ].
destruct ps₃ as [nz₃| ]; [ simpl | reflexivity ].
constructor.
bbb.

Definition ps_rng : Lfield.r (puiseux_series α) :=
  {| Lfield.zero := ps_zero;
     Lfield.one := ps_one;
     Lfield.add := ps_add;
     Lfield.mul := ps_mul;
     Lfield.opp := ps_opp;
     Lfield.eq := eq_ps;
     Lfield.eq_refl := eq_ps_refl;
     Lfield.eq_sym := eq_ps_sym;
     Lfield.eq_trans := eq_ps_trans;
     Lfield.neq_1_0 := ps_neq_1_0;
     Lfield.add_comm := ps_add_comm;
     Lfield.add_assoc := ps_add_assoc;
     Lfield.add_0_l := ps_add_0_l;
     Lfield.add_opp_l := ps_add_opp_l;
     Lfield.add_compat_l := ps_add_compat_l;
     Lfield.mul_comm := ps_mul_comm;
     Lfield.mul_assoc := ps_mul_assoc;
     Lfield.mul_1_l := ps_mul_1_l;
     Lfield.mul_compat_l := ps_mul_compat_l;
     Lfield.mul_add_distr_l := ps_mul_add_distr_l |}.

Add Parametric Morphism : ps_mul
  with signature eq_ps ==> eq_ps ==> eq_ps
  as ps_mul_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
bbb.
