(* $Id: SandBox.v,v 2.153 2013-12-02 11:01:45 deraugla Exp $ *)

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
Notation "a + b" := (ps_add fld a b) : ps_scope.
Notation "a * b" := (ps_mul a b) : ps_scope.

Lemma nz_norm_mul_comm : ∀ nz₁ nz₂,
  normalise_nz (nz_mul nz₁ nz₂) ≐ normalise_nz (nz_mul nz₂ nz₁).
Proof.
intros nz₁ nz₂.
unfold normalise_nz; simpl.
remember (series_stretch (cm_factor nz₁ nz₂) (nz_terms nz₁)) as s₁ eqn:Hs₁ .
remember (series_stretch (cm_factor nz₂ nz₁) (nz_terms nz₂)) as s₂ eqn:Hs₂ .
rewrite series_mul_comm.
remember (null_coeff_range_length fld (series_mul s₂ s₁) 0) as n eqn:Hn .
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
  {| terms := λ _, Lfield.one fld; stop := 1 |} = series_1.
Proof. reflexivity. Qed.

Lemma stretch_series_1 : ∀ k, series_stretch k series_1 ≃ series_1.
Proof.
intros k.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite Nat.add_0_r.
destruct (Nbar.lt_dec (fin i) (fin (Pos.to_nat k))) as [H₁| H₁].
 destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂].
  unfold series_nth_fld; simpl.
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
remember (null_coeff_range_length fld (nz_terms nz) 0) as n eqn:Hn .
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
unfold series_nth_fld in H₁.
simpl in H₁.
destruct (Nbar.lt_dec 0 0) as [H₂| H₂].
 revert H₂; apply Nbar.lt_irrefl.

 destruct (Nbar.lt_dec 0 1) as [H₃| H₃].
  apply Lfield.neq_1_0 in H₁; contradiction.

  apply H₃, Nbar.lt_0_1.
Qed.

Lemma sigma_aux_add : ∀ f b k₁ k₂,
  sigma_aux b (k₁ + k₂) f ≍ (sigma_aux b k₁ f + sigma_aux (b + k₁) k₂ f)%fld.
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
  ≍ (Σ (i = 0, k₁)   f i + Σ (i = S k₁, k₁ + k₂)   f i)%fld.
Proof.
intros f k₁ k₂.
unfold sigma.
do 2 rewrite Nat.sub_0_r.
rewrite <- Nat.add_succ_l.
rewrite sigma_aux_add; simpl.
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Lemma sigma_aux_succ : ∀ f b k,
  sigma_aux b (S k) f ≍ (f b + sigma_aux (S b) k f)%fld.
Proof. reflexivity. Qed.

Lemma sigma_aux_twice_twice : ∀ f n k,
  sigma_aux (n + n)%nat (k + k)%nat f
  ≍ sigma_aux n k (λ i, f (i + i)%nat + f (i + i + 1)%nat)%fld.
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
  → (∀ i, i mod n ≠ O → f i ≍ 0%fld)
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
  rewrite Nat_sub_succ_1.
  rewrite Nat.add_comm.
  rewrite sigma_only_one.
bbb.
*)

Lemma zzz : ∀ a b k,
  series_stretch k (series_mul a b)
  ≃ series_mul (series_stretch k a) (series_stretch k b).
Proof.
intros a b k.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite <- Nbar.mul_add_distr_r.
remember ((stop a + stop b) * fin (Pos.to_nat k))%Nbar as x.
destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁]; [ subst x | reflexivity ].
destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂].
 apply Nat.mod_divides in H₂.
  destruct H₂ as (c, Hc).
  rewrite Hc.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; auto.
  unfold series_nth_fld; simpl.
  destruct (Nbar.lt_dec (fin c) (stop a + stop b)) as [H₂| H₂].
   unfold convol_mul; simpl.
   rename k into n, i into k.
   symmetry.
   apply inserted_0_sigma.
    intros i Hi.
    apply all_0_sigma_0; intros j.
    rewrite shifted_in_stretched.
     rewrite Lfield.mul_0_l, Lfield.mul_0_r; reflexivity.

     apply neq_0_lt, Nat.neq_sym; assumption.

    intros i.
bbb.

Theorem ps_mul_assoc : ∀ ps₁ ps₂ ps₃,
  ps_mul ps₁ (ps_mul ps₂ ps₃) ≈ ps_mul (ps_mul ps₁ ps₂) ps₃.
Proof.
intros ps₁ ps₂ ps₃.
unfold ps_mul; simpl.
destruct ps₁ as [nz₁| ]; [ idtac | reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
destruct ps₃ as [nz₃| ]; [ constructor | reflexivity ].
unfold normalise_nz; simpl.
rewrite zzz; symmetry.
rewrite zzz; symmetry.
do 4 rewrite <- series_stretch_stretch.
unfold cm, cm_factor; simpl.
rewrite series_mul_assoc.
bbb.
rewrite series_mul_assoc.
remember (series_mul (nz_terms nz₁) (nz_terms nz₂)) as s₁₂.
remember (series_mul s₁₂ (nz_terms nz₃)) as s₁₂₃; subst s₁₂.
remember (null_coeff_range_length fld s₁₂₃ 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; constructor; simpl.
 rewrite series_mul_assoc, <- Heqs₁₂₃.
 unfold gcd_nz; simpl.
 f_equal.
  apply Z.add_cancel_r.
  do 2 rewrite Pos2Z.inj_mul; ring.

  do 2 f_equal.
   do 2 rewrite Pos2Z.inj_mul; ring.

   rewrite Pos.mul_assoc; reflexivity.

 rewrite series_mul_assoc, <- Heqs₁₂₃.
 do 2 f_equal.
  do 4 rewrite Pos2Z.inj_mul.
  rewrite Z.mul_assoc; reflexivity.

  unfold gcd_nz; simpl.
  do 2 f_equal.
   do 2 rewrite Pos2Z.inj_mul; ring.

   rewrite Pos.mul_assoc; reflexivity.

 rewrite series_mul_assoc, <- Heqs₁₂₃.
 apply eq_series_eq.
 do 2 f_equal.
 unfold gcd_nz; simpl.
 do 2 f_equal.
  do 2 rewrite Pos2Z.inj_mul; ring.

  rewrite Pos.mul_assoc; reflexivity.
Qed.

Lemma eq_nz_mul_compat_r : ∀ nz₁ nz₂ nz₃,
  eq_nz nz₁ nz₂
  → eq_nz (nz_mul nz₁ nz₃) (nz_mul nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃ Heq.
induction Heq.
constructor; simpl.
 rewrite H, H0; reflexivity.

 rewrite H0; reflexivity.

 rewrite H1; reflexivity.
Qed.

Lemma eq_nz_mul_compat_l : ∀ nz₁ nz₂ nz₃,
  eq_nz nz₁ nz₂
  → eq_nz (nz_mul nz₃ nz₁) (nz_mul nz₃ nz₂).
Proof.
intros nz₁ nz₂ nz₃ Heq.
induction Heq.
constructor; simpl.
 rewrite H, H0; reflexivity.

 rewrite H0; reflexivity.

 rewrite H1; reflexivity.
Qed.

Lemma series_mul_stretch_mul_inf : ∀ a b k,
  series_mul (series_stretch k a) b
  ≃ series_mul_inf (series_stretch k (series_inf fld a))
      (series_inf fld b).
Proof.
intros a b l.
constructor; intros k.
unfold series_nth_fld; simpl.
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
    rewrite series_nth_fld_mul_stretch.
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
  apply all_0_sigma_0; intros i.
  apply all_0_sigma_0; intros j.
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
    unfold series_nth_fld; simpl.
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

(* faux ; exemple pour k > 1 :
   - terme de gauche : a₀b₀ + 0 x + ...
   - terme de droite : a₀b₀ + a₀b₁x + ...
Lemma zzz : ∀ a b k,
  series_stretch k (series_mul a b)
  ≃ series_mul (series_stretch k a) b.
Proof.
intros a b k.
rewrite series_mul_stretch_mul_inf.
rewrite series_mul_mul_inf.
remember (series_inf fld a) as aa eqn:Haa .
remember (series_inf fld b) as bb eqn:Hbb .
constructor; intros i.
rewrite series_nth_mul_inf; simpl.
destruct (zerop (i mod Pos.to_nat k)) as [H₁| H₁].
 apply Nat.mod_divides in H₁; auto.
 destruct H₁ as (j, Hj).
 rewrite Hj in |- * at 1.
 rewrite series_nth_fld_mul_stretch.
 rewrite series_nth_mul_inf.
 unfold series_mul_inf; simpl.
 unfold convol_mul_inf.
 rewrite Nat.mul_comm in Hj; rewrite Hj.
bbb.
 rewrite inserted_0_sigma.
*)

(*
Lemma zzz : ∀ s k v c,
 normalise_nz
   {| nz_terms := series_stretch k s; nz_valnum := v; nz_comden := c |}
 ≐ normalise_nz
     {| nz_terms := s; nz_valnum := v; nz_comden := c |}.
Proof.
intros s k v c.
unfold normalise_nz; simpl.
rewrite null_coeff_range_length_stretch_0.
rewrite Nbar.mul_comm.
remember (null_coeff_range_length fld s 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ simpl | reflexivity ].
constructor; constructor; simpl.
 unfold gcd_nz; simpl.
 rewrite greatest_series_x_power_stretch.
bbb.
*)

Lemma normalise_nz_adjust_nz_mul_0_l : ∀ nz₁ nz₂ k,
  normalise_nz (nz_mul nz₁ nz₂) ≐
  normalise_nz (nz_mul (adjust_nz 0 k nz₁) nz₂).
Proof.
intros nz₁ nz₂ k.
rewrite nz_adjust_eq with (n := O) (k := k).
unfold nz_mul; simpl.
unfold adjust_nz; simpl.
do 2 rewrite Z.sub_0_r.
rewrite Pos2Z.inj_mul, Z.mul_assoc.
rewrite Z.mul_shuffle0.
rewrite <- Z.mul_add_distr_r.
rewrite Pos_mul_shuffle0.
do 2 rewrite series_shift_0.
bbb.
apply normalise_nz_morph.
constructor; try reflexivity; simpl.
bbb.
*)

(* faux car faux pour n = 0 du lemme ci-dessus qui est faux
Lemma normalise_nz_adjust_nz_mul_r : ∀ nz₁ nz₂ n k,
  normalise_nz (nz_mul nz₁ nz₂) ≐
  normalise_nz (nz_mul (adjust_nz n k nz₁) nz₂).
Proof.
intros nz₁ nz₂ n k.
rewrite nz_adjust_eq with (n := n) (k := k).
unfold nz_mul; simpl.
unfold adjust_nz; simpl.
symmetry.
rewrite Pos2Z.inj_mul, Z.mul_assoc.
rewrite Z.mul_sub_distr_r.
rewrite Z.mul_shuffle0.
rewrite <- Z.add_sub_swap.
rewrite <- Z.mul_add_distr_r.
rewrite Pos_mul_shuffle0.
bbb.
assert
 (series_mul (series_shift n (series_stretch k (nz_terms nz₁)))
    (nz_terms nz₂) ≃
  series_shift n
    (series_stretch k (series_mul (nz_terms nz₁) (nz_terms nz₂)))).
 Focus 2.
 rewrite H.
bbb.

intros nz₁ nz₂ n k.
rewrite eq_norm_ps_mul_adjust_0_l with (k := k).
apply normalise_nz_adjust_nz_mul.
bbb.
*)

(* faux
Lemma yyy : ∀ nz n,
  normalise_nz nz ≐ normalise_nz (nz_mul (nz_monom 1%fld (Qnat n)) nz).
Proof.
intros nz n.
unfold nz_mul; simpl.
rewrite series_mul_1_l, Z.mul_1_r.
bbb.
*)

(* faux
Lemma zzz : ∀ nz n k,
  normalise_nz nz
  ≐ normalise_nz (nz_mul (nz_monom 1%fld (Qnat n)) (adjust_nz 0 k nz)).
Proof.
intros nz n k.
bbb.
*)

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
 remember Hps₁ as H; clear HeqH.
 apply normalised_exists_adjust in H.
 destruct H as (n₁, (k₁, H)).
 apply eq_nz_mul_compat_r with (nz₃ := nz₃) in H.
 rewrite H; clear H.
 remember Hps₂ as H; clear HeqH.
 apply normalised_exists_adjust in H.
 destruct H as (n₂, (k₂, H)).
 apply eq_nz_mul_compat_r with (nz₃ := nz₃) in H.
 rewrite H; clear H.
 rewrite nz_norm_mul_comm; symmetry.
 rewrite nz_norm_mul_comm; symmetry.
 remember (normalise_nz nz₃) as ps₃ eqn:Hps₃ .
 symmetry in Hps₃.
 destruct ps₃ as [nz'₃| ].
  remember Hps₃ as H; clear HeqH.
  apply normalised_exists_adjust in H.
  destruct H as (n₃, (k₃, H)).
  remember H as H₁; clear HeqH₁.
  apply eq_nz_mul_compat_r with (nz₃ := adjust_nz n₁ k₁ nz'₁) in H₁.
  rewrite H₁; clear H₁.
  remember H as H₁; clear HeqH₁.
  apply eq_nz_mul_compat_r with (nz₃ := adjust_nz n₂ k₂ nz'₂) in H₁.
  rewrite H₁; clear H₁.
  unfold nz_mul; simpl.
  inversion Heq; subst.
  inversion H2; subst.
  rewrite <- H0, <- H1, <- H3.
bbb.

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
bbb.

Definition ps_fld α : Lfield.t (puiseux_series α) :=
  {| Lfield.zero := @ps_zero α;
     Lfield.one := @ps_one α fld;
     Lfield.add := @ps_add α fld;
     Lfield.mul := @ps_mul;
     Lfield.opp := @ps_opp α fld;
(*
     Lfield.inv := 0;
*)
     Lfield.eq := @eq_ps α fld;
     Lfield.eq_refl := @eq_ps_refl α fld;
     Lfield.eq_sym := @eq_ps_sym α fld;
     Lfield.eq_trans := @eq_ps_trans α fld;
     Lfield.neq_1_0 := @ps_neq_1_0;
     Lfield.add_comm := @ps_add_comm α fld;
     Lfield.add_assoc := @ps_add_assoc α fld;
     Lfield.add_0_l := @ps_add_0_l α fld;
     Lfield.add_opp_l := @ps_add_opp_l α fld;
     Lfield.add_compat_l := @ps_add_compat_l α fld;
     Lfield.mul_comm := @ps_mul_comm;
     Lfield.mul_assoc := @ps_mul_assoc;
     Lfield.mul_1_l := @ps_mul_1_l;
     Lfield.mul_compat_l := @ps_mul_compat_l
(*
     Lfield.mul_inv_l := 0;
     Lfield.mul_add_distr_l := 0
*)
   |}.

Add Parametric Morphism α (fld : Lfield.t α) : (ps_mul fld)
with signature eq_ps fld ==> eq_ps fld ==> eq_ps fld
as ps_mul_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
bbb.
