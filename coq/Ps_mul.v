(* $Id: Ps_mul.v,v 2.87 2013-12-19 19:25:10 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Nbar.
Require Import Misc.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_add_compat.
Require Power_series.
Import Power_series.M.

Set Implicit Arguments.

(* ps_mul *)

Definition ps_mul ps₁ ps₂ :=
  {| ps_terms :=
       series_mul
         (series_stretch (cm_factor ps₁ ps₂) (ps_terms ps₁))
         (series_stretch (cm_factor ps₂ ps₁) (ps_terms ps₂));
     ps_valnum :=
       (ps_valnum ps₁ * ' ps_polord ps₂ + ps_valnum ps₂ * ' ps_polord ps₁)%Z;
     ps_polord :=
       cm ps₁ ps₂ |}.

Notation "a * b" := (ps_mul a b) : ps_scope.

Lemma ps_canon_mul_comm : ∀ ps₁ ps₂,
  canonic_ps (ps_mul ps₁ ps₂) ≐ canonic_ps (ps_mul ps₂ ps₁).
Proof.
intros ps₁ ps₂.
unfold canonic_ps; simpl.
remember (series_stretch (cm_factor ps₁ ps₂) (ps_terms ps₁)) as s₁ eqn:Hs₁ .
remember (series_stretch (cm_factor ps₂ ps₁) (ps_terms ps₂)) as s₂ eqn:Hs₂ .
rewrite series_mul_comm.
remember (null_coeff_range_length rng (series_mul s₂ s₁) 0) as n eqn:Hn .
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; simpl.
 unfold gcd_ps; simpl.
 rewrite series_mul_comm.
 f_equal; [ f_equal; apply Z.add_comm | f_equal ].
 f_equal; [ f_equal; apply Z.add_comm | idtac ].
 unfold cm; rewrite Pos.mul_comm; reflexivity.

 unfold cm; rewrite Pos.mul_comm, series_mul_comm.
 unfold gcd_ps; simpl.
 do 3 f_equal.
 f_equal; [ f_equal; apply Z.add_comm | idtac ].
 unfold cm; rewrite Pos.mul_comm; reflexivity.

 unfold gcd_ps; simpl.
 unfold cm; rewrite Pos.mul_comm, series_mul_comm.
 remember (ps_valnum ps₁ * ' ps_polord ps₂)%Z as x eqn:Hx .
 remember (ps_valnum ps₂ * ' ps_polord ps₁)%Z as y eqn:Hy .
 replace (x + y)%Z with (y + x)%Z by apply Z.add_comm.
 reflexivity.
Qed.

Theorem ps_mul_comm : ∀ ps₁ ps₂, (ps₁ * ps₂ = ps₂ * ps₁)%ps.
Proof.
intros ps₁ ps₂.
constructor.
apply ps_canon_mul_comm.
Qed.

Lemma fold_series_1 : {| terms := λ _, 1%rng; stop := 1 |} = 1%ser.
Proof. reflexivity. Qed.

Lemma stretch_series_1 : ∀ k, (series_stretch k 1 = 1)%ser.
Proof.
intros k.
constructor; intros i.
unfold series_nth; simpl.
rewrite Nat.add_0_r.
destruct (Nbar.lt_dec (fin i) (fin (Pos.to_nat k))) as [H₁| H₁].
 destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂].
  unfold series_nth; simpl.
  apply Nat.mod_divides in H₂; auto.
  destruct H₂ as (c, Hc); rewrite Hc.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; auto.
  destruct (Nbar.lt_dec (fin c) 1) as [H₂| H₂].
   apply Nbar.fin_lt_mono in H₂.
   apply lt_n_Sm_le, Nat.le_0_r in H₂; subst c.
   rewrite Nat.mul_0_l.
   rewrite if_lt_dec_0_1; reflexivity.

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

Theorem ps_mul_1_l : ∀ ps, (1 * ps = ps)%ps.
Proof.
intros ps; simpl.
constructor.
unfold canonic_ps; simpl.
unfold cm_factor; simpl.
rewrite fold_series_1, series_stretch_1.
rewrite stretch_series_1, series_mul_1_l.
remember (null_coeff_range_length rng (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; simpl.
 rewrite stretch_series_1, series_stretch_1, series_mul_1_l.
 unfold gcd_ps; simpl.
 rewrite Z.mul_1_r; reflexivity.

 rewrite stretch_series_1, series_stretch_1, series_mul_1_l.
 unfold gcd_ps; simpl.
 rewrite Z.mul_1_r; reflexivity.

 rewrite stretch_series_1, series_stretch_1, series_mul_1_l.
 unfold gcd_ps; simpl.
 rewrite Z.mul_1_r; reflexivity.
Qed.

Theorem ps_mul_1_r : ∀ ps, (ps * 1 = ps)%ps.
Proof. intros ps. rewrite ps_mul_comm. apply ps_mul_1_l. Qed.

Lemma null_coeff_range_length_series_0 :
  null_coeff_range_length rng series_0 0 = ∞.
Proof.
apply null_coeff_range_length_iff; simpl.
apply series_nth_series_0.
Qed.

Theorem ps_mul_0_l : ∀ ps, (0 * ps = 0)%ps.
Proof.
intros ps.
constructor.
unfold canonic_ps; simpl.
unfold cm_factor; simpl.
rewrite series_stretch_series_0.
rewrite series_mul_0_l.
rewrite null_coeff_range_length_series_0.
reflexivity.
Qed.

Theorem ps_mul_0_r : ∀ ps, (ps * 0 = 0)%ps.
Proof. intros ps. rewrite ps_mul_comm. apply ps_mul_0_l. Qed.

Theorem ps_neq_1_0 : (1 ≠ 0)%ps.
Proof.
intros H.
apply null_coeff_range_length_inf_iff in H.
apply null_coeff_range_length_iff in H.
simpl in H.
pose proof (H O) as Hi.
unfold series_nth in Hi.
simpl in Hi.
rewrite if_lt_dec_0_1 in Hi.
revert Hi; apply Lfield.neq_1_0.
Qed.

Lemma sigma_aux_add : ∀ f b k₁ k₂,
  (sigma_aux b (k₁ + k₂) f = sigma_aux b k₁ f + sigma_aux (b + k₁) k₂ f)%rng.
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
  (Σ (i = 0, k₁ + k₂) _ f i
   = Σ (i = 0, k₁) _ f i + Σ (i = S k₁, k₁ + k₂) _ f i)%rng.
Proof.
intros f k₁ k₂.
unfold sigma.
do 2 rewrite Nat.sub_0_r.
rewrite <- Nat.add_succ_l.
rewrite sigma_aux_add; simpl.
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Lemma sigma_aux_succ : ∀ f b k,
  (sigma_aux b (S k) f = f b + sigma_aux (S b) k f)%rng.
Proof. reflexivity. Qed.

Lemma sigma_aux_mul_sigma_aux_sigma_aux : ∀ f k n,
  (sigma_aux 0 (S k * S n) f
   = sigma_aux 0 (S k)
       (λ i, sigma_aux 0 (S n) (λ j, f (i * S n + j)%nat)))%rng.
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
    → (Σ (i = 0, k * n - 1) _ f i
       = Σ (i = 0, k - 1) _ Σ (j = 0, n - 1) _ f (i * n + j)%nat)%rng.
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

Lemma inserted_0_sigma : ∀ f g k n,
  n ≠ O
  → (∀ i, i mod n ≠ O → (f i = 0)%rng)
    → (∀ i, (f (n * i)%nat = g i)%rng)
      → (Σ (i = 0, k * n) _ f i = Σ (i = 0, k) _ g i)%rng.
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

(*
Lemma delta_mul_cancel_r : ∀ a b c, c ≠ O → (δ (a * c) (b * c) = δ a b)%rng.
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
*)

Lemma series_stretch_mul : ∀ a b k,
  (series_stretch k (a * b) = series_stretch k a * series_stretch k b)%ser.
Proof.
intros a b k.
constructor; intros i.
unfold series_nth; simpl.
rewrite <- Nbar.mul_add_distr_r.
remember ((stop a + stop b) * fin (Pos.to_nat k))%Nbar as x.
destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁]; [ subst x | reflexivity ].
destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂].
 apply Nat.mod_divides in H₂; auto.
 destruct H₂ as (c, Hc).
 rewrite Hc.
 rewrite Nat.mul_comm.
 rewrite Nat.div_mul; auto.
 unfold series_nth; simpl.
 destruct (Nbar.lt_dec (fin c) (stop a + stop b)) as [H₂| H₂].
  unfold convol_mul; simpl.
  rename k into n, i into k.
  symmetry.
  apply inserted_0_sigma; auto.
   intros i Hi.
   rewrite shifted_in_stretched.
    rewrite Lfield.mul_0_l; reflexivity.

    apply neq_0_lt, Nat.neq_sym; assumption.

   intros i.
   rewrite Nat.mul_comm.
   rewrite <- Nat.mul_sub_distr_r.
   rewrite Nat.mul_comm.
   rewrite series_nth_mul_stretch.
   rewrite Nat.mul_comm.
   rewrite series_nth_mul_stretch.
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
 destruct (zerop (j mod Pos.to_nat k)) as [H₄| H₄].
  destruct (zerop ((i - j) mod Pos.to_nat k)) as [H₅| H₅].
   apply Nat.mod_divides in H₄; auto.
   apply Nat.mod_divides in H₅; auto.
   destruct H₄ as (c, Hc).
   destruct H₅ as (d, Hd).
   subst j.
   apply Nat.add_sub_eq_nz in Hd.
    subst i.
    rewrite <- Nat.mul_add_distr_l in H₂; auto.
    rewrite Nat.mul_comm in H₂.
    rewrite Nat.mod_mul in H₂; auto.
    exfalso; revert H₂; apply Nat.lt_irrefl.

    intros H.
    rewrite H in Hd.
    apply Nat.sub_0_le in Hd.
    destruct Hj as (_, Hj).
    apply Nat.le_antisymm in Hd; auto.
    rewrite <- Hd in H₂.
    rewrite Nat.mul_comm in H₂.
    rewrite Nat.mod_mul in H₂; auto.
    exfalso; revert H₂; apply Nat.lt_irrefl.

   rewrite Lfield.mul_comm.
   rewrite shifted_in_stretched; [ idtac | assumption ].
   rewrite Lfield.mul_0_l; reflexivity.

  rewrite shifted_in_stretched; [ idtac | assumption ].
  rewrite Lfield.mul_0_l; reflexivity.
Qed.

Theorem ps_mul_assoc : ∀ ps₁ ps₂ ps₃,
  (ps₁ * (ps₂ * ps₃) = (ps₁ * ps₂) * ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃.
constructor.
unfold canonic_ps; simpl.
rewrite series_stretch_mul; symmetry.
rewrite series_stretch_mul; symmetry.
do 4 rewrite <- series_stretch_stretch.
unfold cm, cm_factor; simpl.
rewrite series_mul_assoc.
remember (ps_polord ps₂ * ps_polord ps₃)%positive as c₂₃ eqn:Hc₂₃ .
remember (ps_polord ps₃ * ps_polord ps₁)%positive as c₃₁ eqn:Hc₃₁ .
remember (ps_polord ps₁ * ps_polord ps₂)%positive as c₁₂ eqn:Hc₁₂ .
rewrite Pos.mul_comm in Hc₂₃; rewrite <- Hc₂₃.
rewrite Pos.mul_comm in Hc₃₁; rewrite <- Hc₃₁.
remember (series_stretch c₂₃ (ps_terms ps₁)) as s₁ eqn:Hs₁ .
remember (series_stretch c₃₁ (ps_terms ps₂)) as s₂ eqn:Hs₂ .
remember (series_stretch c₁₂ (ps_terms ps₃)) as s₃ eqn:Hs₃ .
remember (series_mul (series_mul s₁ s₂) s₃) as s₁₂₃ eqn:Hs₁₂₃ .
remember (null_coeff_range_length rng s₁₂₃ 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
unfold gcd_ps; simpl.
unfold cm; simpl.
unfold cm; simpl.
do 2 rewrite Z.mul_add_distr_r.
do 6 rewrite Pos2Z.inj_mul.
do 3 rewrite Z.mul_assoc.
do 2 rewrite Z.add_assoc.
constructor; simpl.
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

Lemma eq_strong_ps_mul_compat_r : ∀ ps₁ ps₂ ps₃,
  eq_ps_strong ps₁ ps₂
  → eq_ps_strong (ps_mul ps₁ ps₃) (ps_mul ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃ Heq.
induction Heq.
constructor; simpl.
 rewrite H, H0; reflexivity.

 unfold cm; simpl.
 rewrite H0; reflexivity.

 unfold cm_factor.
 rewrite H0, H1.
 reflexivity.
Qed.

Lemma eq_strong_ps_mul_compat_l : ∀ ps₁ ps₂ ps₃,
  eq_ps_strong ps₁ ps₂
  → eq_ps_strong (ps_mul ps₃ ps₁) (ps_mul ps₃ ps₂).
Proof.
intros ps₁ ps₂ ps₃ Heq.
induction Heq.
constructor; simpl.
 rewrite H, H0; reflexivity.

 unfold cm; simpl.
 rewrite H0; reflexivity.

 unfold cm_factor.
 rewrite H0, H1.
 reflexivity.
Qed.

Lemma series_nth_lt_shift : ∀ a i n,
  (i < n)%nat
  → (series_nth rng i (series_shift n a) = 0)%rng.
Proof.
intros a i n Hin.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) (stop a + fin n)) as [H₁| H₁].
 destruct (lt_dec i n) as [| H₂]; [ reflexivity | contradiction ].

 reflexivity.
Qed.

Lemma sigma_add_add_sub : ∀ f b k n,
  (Σ (i = b, k) _ f i = Σ (i = b + n, k + n) _ f (i - n)%nat)%rng.
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
  (series_shift n (a * b) = series_shift n a * b)%ser.
Proof.
intros a b n.
constructor; intros k.
unfold series_nth; simpl.
rewrite Nbar.add_shuffle0.
destruct (Nbar.lt_dec (fin k) (stop a + fin n + stop b)) as [H₁| H₁].
 destruct (lt_dec k n) as [H₂| H₂].
  symmetry; unfold convol_mul; simpl.
  apply all_0_sigma_0; intros i Hi.
  rewrite series_nth_lt_shift.
   rewrite Lfield.mul_0_l; reflexivity.

   eapply le_lt_trans; [ idtac | eassumption ].
   destruct Hi; assumption.

  unfold convol_mul; simpl.
  apply Nat.nlt_ge in H₂.
  symmetry.
  destruct n.
   rewrite Nat.sub_0_r.
   apply sigma_compat; intros i Hi.
   rewrite series_shift_0; reflexivity.

   assert (k = (n + (k - n))%nat) as H by omega.
   rewrite H in |- * at 1; clear H.
   rewrite sigma_add.
   rewrite Lfield.add_comm.
   rewrite Nat.add_sub_assoc; [ idtac | omega ].
   rewrite Nat.add_comm, Nat.add_sub.
   rewrite Lfield.add_comm.
   rewrite all_0_sigma_0.
    rewrite Lfield.add_0_l.
    symmetry.
    rewrite sigma_add_add_sub with (n := S n).
    rewrite Nat.add_0_l, Nat.sub_add; [ idtac | assumption ].
    apply sigma_compat; intros i Hi.
    assert (i = i - S n + S n)%nat as H by omega.
    rewrite H in |- * at 3.
    rewrite series_nth_add_shift.
    rewrite <- Nat.sub_add_distr.
    rewrite Nat.add_comm.
    rewrite Nat.sub_add; [ reflexivity | idtac ].
    destruct Hi; assumption.

    intros i Hi.
    rewrite series_nth_lt_shift; [ idtac | omega ].
    rewrite Lfield.mul_0_l; reflexivity.

 reflexivity.
Qed.

Lemma canonic_ps_mul_adjust_l : ∀ ps₁ ps₂ n k,
  canonic_ps (ps_mul ps₁ ps₂) ≐
  canonic_ps (ps_mul (adjust_ps n k ps₁) ps₂).
Proof.
intros ps₁ ps₂ n k.
remember (Pos.to_nat (ps_polord ps₂) * n)%nat as m eqn:Hm .
rewrite ps_canon_adjust_eq with (n := m) (k := k); subst m.
unfold ps_mul; simpl.
unfold adjust_ps; simpl.
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

Lemma ps_canon_mul_compat_r : ∀ ps₁ ps₂ ps₃,
  canonic_ps ps₁ ≐ canonic_ps ps₂
  → canonic_ps (ps_mul ps₁ ps₃) ≐ canonic_ps (ps_mul ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃ Heq.
remember Heq as Heqv; clear HeqHeqv.
remember (canonic_ps ps₁) as nps₁ eqn:Hps₁  in Heq.
remember (canonic_ps ps₂) as nps₂ eqn:Hps₂  in Heq.
symmetry in Hps₁, Hps₂.
remember (null_coeff_range_length rng (ps_terms ps₁) 0) as m₁ eqn:Hm₁ .
remember (null_coeff_range_length rng (ps_terms ps₂) 0) as m₂ eqn:Hm₂ .
symmetry in Hm₁, Hm₂.
destruct m₁ as [m₁| ].
 apply canonified_exists_adjust in Hps₁.
  destruct m₂ as [m₂| ].
   apply canonified_exists_adjust in Hps₂.
    destruct Hps₁ as (n₁, (k₁, Hps₁)).
    destruct Hps₂ as (n₂, (k₂, Hps₂)).
    apply eq_strong_ps_mul_compat_r with (ps₃ := ps₃) in Hps₁.
    apply eq_strong_ps_mul_compat_r with (ps₃ := ps₃) in Hps₂.
    rewrite Hps₁, Hps₂.
    rewrite <- canonic_ps_mul_adjust_l.
    rewrite <- canonic_ps_mul_adjust_l.
    apply eq_strong_ps_mul_compat_r with (ps₃ := ps₃) in Heq.
    rewrite Heq; reflexivity.

    intros H; rewrite Hm₂ in H; discriminate H.

   symmetry in Heqv.
   eapply null_coeff_range_length_inf_compat in Hm₂; [ idtac | eassumption ].
   rewrite Hm₁ in Hm₂; discriminate Hm₂.

  intros H; rewrite Hm₁ in H; discriminate H.

 clear Hm₂.
 remember Hm₁ as Hm₂; clear HeqHm₂.
 eapply null_coeff_range_length_inf_compat in Hm₂; [ idtac | eassumption ].
 apply eq_strong_ps_adjust_zero_neg_zero in Hm₁.
 apply eq_strong_ps_adjust_zero_neg_zero in Hm₂.
 destruct Hm₁ as (n₁, (n₂, (k₁, (k₂, Hm₁)))).
 destruct Hm₂ as (n₃, (n₄, (k₃, (k₄, Hm₂)))).
 apply eq_strong_ps_mul_compat_r with (ps₃ := ps₃) in Hm₁.
 apply eq_strong_ps_mul_compat_r with (ps₃ := ps₃) in Hm₂.
 rewrite canonic_ps_mul_adjust_l with (n := n₁) (k := k₁).
 rewrite Hm₁; symmetry.
 rewrite canonic_ps_mul_adjust_l with (n := n₃) (k := k₃).
 rewrite Hm₂; symmetry.
 rewrite <- canonic_ps_mul_adjust_l.
 rewrite <- canonic_ps_mul_adjust_l.
 reflexivity.
Qed.

Theorem ps_mul_compat_r : ∀ ps₁ ps₂ ps₃,
  (ps₁ = ps₂)%ps
  → (ps₁ * ps₃ = ps₂ * ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ H₁₂.
constructor.
apply ps_canon_mul_compat_r.
inversion H₁₂; assumption.
Qed.

Theorem ps_mul_compat_l : ∀ ps₁ ps₂ ps₃,
  (ps₁ = ps₂)%ps
  → (ps₃ * ps₁ = ps₃ * ps₂)%ps.
Proof.
intros ps₁ ps₂ ps₃ Heq.
rewrite ps_mul_comm; symmetry.
rewrite ps_mul_comm; symmetry.
apply ps_mul_compat_r; assumption.
Qed.

Add Parametric Morphism : ps_mul
  with signature eq_ps_strong ==> eq_ps_strong ==> eq_ps_strong
  as ps_canon_mul_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
rewrite eq_strong_ps_mul_compat_l; [ idtac | eassumption ].
rewrite eq_strong_ps_mul_compat_r; [ idtac | eassumption ].
reflexivity.
Qed.

Add Parametric Morphism : ps_mul
  with signature eq_ps ==> eq_ps ==> eq_ps
  as ps_mul_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
rewrite ps_mul_compat_l; [ idtac | eassumption ].
rewrite ps_mul_compat_r; [ idtac | eassumption ].
reflexivity.
Qed.

Theorem canonic_ps_eq : ∀ ps, (canonic_ps ps = ps)%ps.
Proof.
intros ps.
unfold canonic_ps.
unfold canonic_ps.
remember (null_coeff_range_length rng (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; constructor.
 remember (greatest_series_x_power rng (ps_terms ps) n) as x.
 remember (gcd_ps n x ps) as g eqn:Hg .
 pose proof (gcd_ps_is_pos n x ps) as Hgp; subst x.
 rewrite <- Hg in Hgp.
 unfold gcd_ps in Hg; simpl in Hg.
 remember (ps_valnum ps + Z.of_nat n)%Z as x eqn:Hx .
 rewrite <- Z.gcd_assoc in Hg.
 remember (greatest_series_x_power rng (ps_terms ps) n) as z.
 remember (Z.gcd (' ps_polord ps) (Z.of_nat z)) as y eqn:Hy ; subst z.
 rewrite ps_canon_adjust_eq with (k := Z.to_pos g) (n := n).
 unfold adjust_ps; simpl.
 unfold canonify_series.
 rewrite series_stretch_shrink.
  rewrite series_shift_left_shift; [ idtac | assumption ].
  rewrite <- positive_nat_Z.
  rewrite Pos2Nat_to_pos; [ idtac | assumption ].
  rewrite Z2Nat.id; [ idtac | apply Z.lt_le_incl; assumption ].
  rewrite Z.mul_comm.
  assert (x mod g = 0)%Z as Hxk.
   apply Z.mod_divide.
    intros H; revert Hgp; rewrite H; apply Z.lt_irrefl.

    rewrite Hg; apply Z.gcd_divide_l.

   apply Z.div_exact in Hxk.
    rewrite <- Hxk, Hx, Z.add_simpl_r.
    rewrite Hy, Z.gcd_comm, <- Z.gcd_assoc in Hg.
    remember (greatest_series_x_power rng (ps_terms ps) n) as z.
    pose proof (Z.gcd_divide_l (' ps_polord ps) (Z.gcd (Z.of_nat z) x)) as Hgc.
    rewrite <- Hg in Hgc.
    destruct Hgc as (c, Hc).
    rewrite Hc.
    rewrite Z.div_mul.
     rewrite <- Z2Pos.inj_mul; [ idtac | idtac | assumption ].
      rewrite <- Hc; simpl.
      destruct ps; reflexivity.

      destruct c as [| c| c].
       exfalso; revert Hc; apply Pos2Z_ne_0.

       apply Pos2Z.is_pos.

       simpl in Hc.
       destruct g as [| g| g].
        exfalso; revert Hc; apply Pos2Z_ne_0.

        rewrite <- Pos2Z.opp_pos in Hc.
        apply Z.add_move_0_r in Hc.
        rewrite <- Pos2Z.inj_add in Hc.
        exfalso; revert Hc; apply Pos2Z_ne_0.

        apply Z.nle_gt in Hgp.
        exfalso; apply Hgp; apply Pos2Z.neg_is_nonpos.

     intros H; revert Hgp; rewrite H; apply Z.lt_irrefl.

    intros H; revert Hgp; rewrite H; apply Z.lt_irrefl.

  rewrite greatest_series_x_power_left_shift, Nat.add_0_r.
  rewrite Pos2Nat_to_pos; [ idtac | assumption ].
  remember (greatest_series_x_power rng (ps_terms ps) n) as t.
  rewrite Hy in Hg.
  rewrite Z.gcd_assoc in Hg.
  remember (Z.gcd x (' ps_polord ps)) as u.
  pose proof (Z.gcd_divide_r u (Z.of_nat t)) as H.
  rewrite <- Hg in H.
  destruct H as (c, Hc).
  exists (Z.to_nat c).
  rewrite <- Z2Nat.inj_mul.
   rewrite <- Hc.
   rewrite Nat2Z.id; reflexivity.

   apply Z.mul_le_mono_pos_r with (p := g); [ assumption | idtac ].
   rewrite <- Hc; simpl.
   apply Nat2Z.is_nonneg.

   apply Z.lt_le_incl; assumption.

 unfold canonic_ps; simpl.
 rewrite null_coeff_range_length_series_0, Hn.
 reflexivity.
Qed.

Lemma ps_valnum_canonic : ∀ ps n p vn,
  null_coeff_range_length rng (ps_terms ps) 0 = fin n
  → p = greatest_series_x_power rng (ps_terms ps) n
    → vn = (ps_valnum ps + Z.of_nat n)%Z
      → ps_valnum (canonic_ps ps) =
          (vn / Z.gcd vn (Z.gcd (' ps_polord ps) (Z.of_nat p)))%Z.
Proof.
intros ps n p vn Hn Hp Hvn.
unfold canonic_ps; simpl.
rewrite Hn; simpl.
rewrite <- Hp.
unfold gcd_ps; simpl.
rewrite <- Z.gcd_assoc.
rewrite <- Hvn.
reflexivity.
Qed.

Lemma ps_polord_canonic : ∀ ps n p vn,
  null_coeff_range_length rng (ps_terms ps) 0 = fin n
  → p = greatest_series_x_power rng (ps_terms ps) n
    → vn = (ps_valnum ps + Z.of_nat n)%Z
      → ps_polord (canonic_ps ps) =
        Z.to_pos
          (' ps_polord ps / Z.gcd (' ps_polord ps) (Z.gcd (Z.of_nat p) vn)).
Proof.
intros ps n p vn Hn Hp Hvn.
unfold canonic_ps; simpl.
rewrite Hn; simpl.
rewrite <- Hp.
unfold gcd_ps; simpl.
rewrite <- Z.gcd_assoc, Z.gcd_comm, <- Z.gcd_assoc.
rewrite <- Hvn.
reflexivity.
Qed.

Lemma ps_terms_canonic : ∀ ps n p vn,
  null_coeff_range_length rng (ps_terms ps) 0 = fin n
  → p = greatest_series_x_power rng (ps_terms ps) n
    → vn = (ps_valnum ps + Z.of_nat n)%Z
      → ps_terms (canonic_ps ps) =
        canonify_series n
          (Z.to_pos (Z.gcd vn (Z.gcd (' ps_polord ps) (Z.of_nat p))))
          (ps_terms ps).
Proof.
intros ps n p vn Hn Hp Hvn.
unfold canonic_ps; simpl.
rewrite Hn; simpl.
rewrite <- Hp.
unfold gcd_ps; simpl.
rewrite <- Z.gcd_assoc.
rewrite <- Hvn.
reflexivity.
Qed.

Lemma null_range_length_mul_add₂_distr_l : ∀ ps₁ ps₂ ps₃,
   null_coeff_range_length rng
     (ps_terms (adjust_ps 0 (ps_polord ps₁) (ps₁ * ps_add₂ ps₂ ps₃)%ps)) 0 =
   null_coeff_range_length rng
     (ps_terms (adjust_ps 0 1 (ps_add₂ (ps₁ * ps₂)%ps (ps₁ * ps₃)%ps))) 0.
Proof.
intros ps₁ ps₂ ps₃; simpl.
unfold cm, cm_factor; simpl.
do 2 rewrite series_shift_0.
rewrite series_stretch_1.
remember (ps_valnum ps₁) as v₁.
remember (ps_polord ps₂) as c₂.
remember (ps_valnum ps₂) as v₂.
remember (ps_polord ps₁) as c₁.
remember (ps_valnum ps₃) as v₃.
remember (ps_polord ps₃) as c₃.
do 3 rewrite series_stretch_mul.
do 6 rewrite <- series_stretch_stretch.
rewrite series_stretch_add_distr.
do 2 rewrite stretch_shift_series_distr.
do 2 rewrite <- series_stretch_stretch.
symmetry.
rewrite series_mul_comm.
rewrite series_shift_mul.
rewrite series_add_comm.
rewrite series_mul_comm.
rewrite series_shift_mul.
rewrite series_add_comm.
replace (c₁ * c₃ * c₂)%positive with (c₁ * c₂ * c₃)%positive
 by apply Pos_mul_shuffle0.
rewrite <- series_mul_add_distr_r.
rewrite series_mul_comm.
do 2 rewrite Pos2Z.inj_mul, Z.mul_assoc.
do 4 rewrite Z.mul_add_distr_r.
remember (v₁ * ' c₂ * ' c₁ * ' c₃)%Z as x eqn:Hx .
replace (v₁ * ' c₃ * ' c₁ * ' c₂)%Z with x by (subst x; ring).
do 2 rewrite Z.add_min_distr_l.
do 2 rewrite Z.add_add_simpl_l_l.
clear x Hx.
do 2 rewrite <- Z2Nat_inj_mul_pos_r.
rewrite Pos2Z.inj_mul; do 2 rewrite Z.mul_assoc.
do 4 rewrite Z.mul_sub_distr_r.
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite Pos.mul_assoc.
do 2 f_equal.
f_equal.
 rewrite Pos_mul_shuffle0.
 do 2 f_equal.
 f_equal; [ ring | idtac ].
 f_equal; ring.

 rewrite Pos_mul_shuffle0.
 do 2 f_equal.
 f_equal; [ ring | idtac ].
 f_equal; ring.
Qed.

Lemma ps_valnum_adjust_mul_add₂_distr_l : ∀ ps₁ ps₂ ps₃,
  ps_valnum (adjust_ps 0 (ps_polord ps₁) (ps₁ * ps_add₂ ps₂ ps₃)%ps) =
  ps_valnum (adjust_ps 0 1 (ps_add₂ (ps₁ * ps₂)%ps (ps₁ * ps₃)%ps)).
Proof.
intros ps₁ ps₂ ps₃; simpl.
unfold cm; simpl.
unfold cm_factor.
f_equal.
rewrite Z.mul_1_r.
remember (ps_valnum ps₁) as v₁.
remember (ps_polord ps₂) as c₂.
remember (ps_valnum ps₂) as v₂.
remember (ps_polord ps₁) as c₁.
remember (ps_valnum ps₃) as v₃.
remember (ps_polord ps₃) as c₃.
do 3 rewrite Pos2Z.inj_mul.
do 3 rewrite Z.mul_assoc.
rewrite Z.mul_sub_distr_r.
do 3 rewrite <- positive_nat_Z.
do 5 rewrite Z.mul_add_distr_r.
rewrite Z.mul_sub_distr_r.
do 2 rewrite <- Nat2Z.inj_mul.
do 2 rewrite <- Z2Nat_inj_mul_pos_r.
do 2 rewrite Z.mul_sub_distr_r.
do 3 rewrite positive_nat_Z.
rewrite Z.add_sub_assoc.
f_equal.
 rewrite Z.mul_shuffle0.
 apply Z.add_cancel_l.
 rewrite <- Z.mul_assoc, Z.mul_shuffle0, Z.mul_assoc.
 reflexivity.

 do 2 f_equal.
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 remember (v₁ * ' c₃ * ' c₁ * ' c₂)%Z as x.
 replace (v₁ * ' c₂ * ' c₁ * ' c₃)%Z with x by (subst; ring).
 rewrite Z.add_min_distr_l.
 rewrite Z.add_add_simpl_l_l.
 clear x Heqx.
 f_equal; [ ring | idtac ].
 f_equal; ring.
Qed.

Lemma ps_polord_adjust_mul_add₂_distr_l : ∀ ps₁ ps₂ ps₃,
  ps_polord (adjust_ps 0 (ps_polord ps₁) (ps₁ * ps_add₂ ps₂ ps₃)%ps) =
  ps_polord (adjust_ps 0 1 (ps_add₂ (ps₁ * ps₂)%ps (ps₁ * ps₃)%ps)).
Proof.
intros ps₁ ps₂ ps₃; simpl.
unfold cm; simpl.
unfold cm_factor.
rewrite Pos.mul_1_r.
do 2 rewrite Pos.mul_assoc.
rewrite Pos_mul_shuffle0.
reflexivity.
Qed.

Lemma ps_terms_adjust_mul_add₂_distr_l : ∀ ps₁ ps₂ ps₃,
  (ps_terms (adjust_ps 0 (ps_polord ps₁) (ps₁ * ps_add₂ ps₂ ps₃)%ps) =
   ps_terms (adjust_ps 0 1 (ps_add₂ (ps₁ * ps₂)%ps (ps₁ * ps₃)%ps)))%ser.
Proof.
intros ps₁ ps₂ ps₃; simpl.
unfold cm; simpl.
unfold cm_factor.
do 2 rewrite series_shift_0.
rewrite series_stretch_1.
remember (ps_valnum ps₁) as v₁.
remember (ps_polord ps₂) as c₂.
remember (ps_valnum ps₂) as v₂.
remember (ps_polord ps₁) as c₁.
remember (ps_valnum ps₃) as v₃.
remember (ps_polord ps₃) as c₃.
do 3 rewrite series_stretch_mul.
do 6 rewrite <- series_stretch_stretch.
rewrite series_stretch_add_distr.
rewrite series_mul_add_distr_l.
symmetry.
rewrite series_mul_comm, series_shift_mul, series_mul_comm.
rewrite series_add_comm.
rewrite series_mul_comm, series_shift_mul, series_mul_comm.
do 2 rewrite Pos2Z.inj_mul.
do 2 rewrite Z.mul_assoc.
do 4 rewrite Z.mul_add_distr_r.
remember (v₁ * ' c₃ * ' c₁ * ' c₂)%Z as x.
replace (v₁ * ' c₂ * ' c₁ * ' c₃)%Z with x by (subst x; ring).
do 2 rewrite Z.add_min_distr_l.
do 2 rewrite Z.add_add_simpl_l_l.
clear x Heqx.
do 2 rewrite stretch_shift_series_distr.
do 2 rewrite <- Z2Nat_inj_mul_pos_r.
rewrite Pos2Z.inj_mul.
do 2 rewrite Z.mul_assoc.
do 4 rewrite Z.mul_sub_distr_r.
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite series_add_comm.
do 2 rewrite <- series_stretch_stretch.
rewrite Pos.mul_assoc.
rewrite Pos_mul_shuffle0.
remember (v₂ * ' c₁ * ' c₁ * ' c₃)%Z as x.
replace (v₂ * ' c₃ * ' c₁ * ' c₁)%Z with x by (subst; ring).
subst x.
remember (v₃ * ' c₁ * ' c₁ * ' c₂)%Z as x.
replace (v₃ * ' c₂ * ' c₁ * ' c₁)%Z with x by (subst; ring).
subst x.
remember (c₁ * c₃ * c₁)%positive as x.
rewrite Pos_mul_shuffle0 in Heqx.
subst x.
remember (c₁ * c₂ * c₁)%positive as x.
rewrite Pos_mul_shuffle0 in Heqx.
subst x.
reflexivity.
Qed.

Lemma ps_valnum_adjust_canonic_mul_add₂_distr_l : ∀ ps₁ ps₂ ps₃ ps₄ ps₅ n,
  ps₄ = adjust_ps 0 (ps_polord ps₁) (ps₁ * ps_add₂ ps₂ ps₃)%ps
  → ps₅ = adjust_ps 0 1 (ps_add₂ (ps₁ * ps₂)%ps (ps₁ * ps₃)%ps)
    → null_coeff_range_length rng (ps_terms ps₄) 0 = fin n
      → null_coeff_range_length rng (ps_terms ps₅) 0 = fin n
        → ps_valnum (canonic_ps ps₄) = ps_valnum (canonic_ps ps₅).
Proof.
intros ps₁ ps₂ ps₃ ps₄ ps₅ n Hps₄ Hps₅ Hn₄ Hn₅.
erewrite ps_valnum_canonic; try reflexivity; try eassumption.
erewrite ps_valnum_canonic; try reflexivity; try eassumption.
rewrite Hps₄, Hps₅.
rewrite ps_valnum_adjust_mul_add₂_distr_l.
rewrite ps_polord_adjust_mul_add₂_distr_l.
rewrite ps_terms_adjust_mul_add₂_distr_l.
reflexivity.
Qed.

Lemma ps_polord_adjust_canonic_mul_add₂_distr_l : ∀ ps₁ ps₂ ps₃ ps₄ ps₅ n,
  ps₄ = adjust_ps 0 (ps_polord ps₁) (ps₁ * ps_add₂ ps₂ ps₃)%ps
  → ps₅ = adjust_ps 0 1 (ps_add₂ (ps₁ * ps₂)%ps (ps₁ * ps₃)%ps)
    → null_coeff_range_length rng (ps_terms ps₄) 0 = fin n
      → null_coeff_range_length rng (ps_terms ps₅) 0 = fin n
        → ps_polord (canonic_ps ps₄) = ps_polord (canonic_ps ps₅).
Proof.
intros ps₁ ps₂ ps₃ ps₄ ps₅ n Hps₄ Hps₅ Hn₄ Hn₅.
erewrite ps_polord_canonic; try reflexivity; try eassumption.
erewrite ps_polord_canonic; try reflexivity; try eassumption.
rewrite Hps₄, Hps₅.
rewrite ps_valnum_adjust_mul_add₂_distr_l.
rewrite ps_polord_adjust_mul_add₂_distr_l.
rewrite ps_terms_adjust_mul_add₂_distr_l.
reflexivity.
Qed.

Lemma ps_terms_adjust_canonic_mul_add₂_distr_l : ∀ ps₁ ps₂ ps₃ ps₄ ps₅ n,
  ps₄ = adjust_ps 0 (ps_polord ps₁) (ps₁ * ps_add₂ ps₂ ps₃)%ps
  → ps₅ = adjust_ps 0 1 (ps_add₂ (ps₁ * ps₂)%ps (ps₁ * ps₃)%ps)
    → null_coeff_range_length rng (ps_terms ps₄) 0 = fin n
      → null_coeff_range_length rng (ps_terms ps₅) 0 = fin n
        → (ps_terms (canonic_ps ps₄) = ps_terms (canonic_ps ps₅))%ser.
Proof.
intros ps₁ ps₂ ps₃ ps₄ ps₅ n Hps₄ Hps₅ Hn₄ Hn₅.
erewrite ps_terms_canonic; try reflexivity; try eassumption.
erewrite ps_terms_canonic; try reflexivity; try eassumption.
rewrite Hps₄, Hps₅.
rewrite ps_valnum_adjust_mul_add₂_distr_l.
rewrite ps_polord_adjust_mul_add₂_distr_l.
rewrite ps_terms_adjust_mul_add₂_distr_l.
reflexivity.
Qed.

Theorem ps_mul_add_distr_l : ∀ ps₁ ps₂ ps₃,
  (ps₁ * (ps₂ + ps₃) = ps₁ * ps₂ + ps₁ * ps₃)%ps.
Proof.
intros ips₁ ips₂ ips₃.
rewrite <- (canonic_ps_eq ips₁).
rewrite <- (canonic_ps_eq ips₂).
rewrite <- (canonic_ps_eq ips₃).
remember (canonic_ps ips₁) as ps₁ eqn:Hps₁ .
remember (canonic_ps ips₂) as ps₂ eqn:Hps₂ .
remember (canonic_ps ips₃) as ps₃ eqn:Hps₃ .
remember (ps_valnum ps₁ * ' ps_polord ps₂ * ' ps_polord ps₃)%Z as vcc.
remember (' ps_polord ps₁ * ps_valnum ps₂ * ' ps_polord ps₃)%Z as cvc.
remember (' ps_polord ps₁ * ' ps_polord ps₂ * ps_valnum ps₃)%Z as ccv.
remember ((vcc + Z.min cvc ccv) * ' ps_polord ps₁)%Z as n₁.
remember ((vcc + Z.min cvc ccv) * ' ps_polord ps₁)%Z as n₂.
do 2 rewrite eq_ps_add_add₂.
rewrite ps_adjust_eq with (n := O) (k := ps_polord ps₁); symmetry.
rewrite ps_adjust_eq with (n := O) (k := xH); symmetry.
remember (adjust_ps 0 (ps_polord ps₁) (ps₁ * ps_add₂ ps₂ ps₃))%ps as ps₄
 eqn:Hps₄ .
remember (adjust_ps 0 1 (ps_add₂ (ps₁ * ps₂) (ps₁ * ps₃)))%ps as ps₅ eqn:Hps₅ .
remember (null_coeff_range_length rng (ps_terms ps₄) 0) as n₄ eqn:Hn₄ .
remember (null_coeff_range_length rng (ps_terms ps₅) 0) as n₅ eqn:Hn₅ .
symmetry in Hn₄, Hn₅.
assert (n₄ = n₅) as H by (subst; apply null_range_length_mul_add₂_distr_l).
move H at top; subst n₅.
destruct n₄ as [n₄| ].
 constructor; constructor; simpl.
  eapply ps_valnum_adjust_canonic_mul_add₂_distr_l; eassumption.

  eapply ps_polord_adjust_canonic_mul_add₂_distr_l; eassumption.

  eapply ps_terms_adjust_canonic_mul_add₂_distr_l; eassumption.

 rewrite null_coeff_range_length_inf_iff in Hn₄.
 rewrite null_coeff_range_length_inf_iff in Hn₅.
 rewrite Hn₄, Hn₅; reflexivity.
Qed.

Definition ps_ring : Lfield.r (puiseux_series α) :=
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
