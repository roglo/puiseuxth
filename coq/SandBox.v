(* $Id: SandBox.v,v 2.13 2013-11-11 10:10:30 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Series.
Require Import Puiseux_series.
Require Import Nbar.
Require Import Ps_add.
Require Import Misc.

Set Implicit Arguments.

Section fld.

Variable α : Type.
Variable fld : field α.
Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).
Notation "a ≈ b" := (eq_ps fld a b) (at level 70).
Notation "a ≐ b" := (eq_norm_ps fld a b) (at level 70).

Delimit Scope ps_scope with ps.
Bind Scope ps_scope with puiseux_series.
Notation "a + b" := (ps_add fld a b) : ps_scope.
Notation "a ∔ b" := (nz_add fld a b) (at level 70).

Lemma series_nth_0_series_nth_shift_0 : ∀ s n,
  (∀ i, series_nth_fld fld i s ≍ zero fld)
  → ∀ i, series_nth_fld fld i (series_shift fld n s) ≍ zero fld.
Proof.
intros s n H i.
revert i.
induction n as [| n]; intros.
 rewrite series_shift_0; apply H.

 destruct i.
  unfold series_nth_fld; simpl.
  destruct (Nbar.lt_dec 0 (stop s + fin (S n))); reflexivity.

  rewrite <- series_nth_shift_S; apply IHn.
Qed.

Lemma series_nth_shift_0_series_nth_0 : ∀ s n,
  (∀ i : nat, series_nth_fld fld i (series_shift fld n s) ≍ zero fld)
  → ∀ i, series_nth_fld fld i s ≍ zero fld.
Proof.
intros s n H i.
revert i.
induction n as [| n]; intros.
 rewrite <- series_shift_0; apply H.

 apply IHn; intros j.
 rewrite series_nth_shift_S; apply H.
Qed.

(*
Lemma series_nth_shift_0_P_series_nth_0 : ∀ s n P,
  (∀ i, P i → series_nth_fld fld i (series_shift fld n s) ≍ zero fld)
  → ∀ i, P i
    → series_nth_fld fld i s ≍ zero fld.
Proof.
intros s n P H i Pi.
revert i Pi.
induction n; intros.
 rewrite <- series_shift_0.
 apply H; assumption.

 apply IHn; [ intros j Pj | assumption ].
 rewrite series_nth_shift_S.
aaa.
*)

Lemma normalise_series_add_shift : ∀ s n m k,
  normalise_series (n + m) k (series_shift fld m s)
  ≃ normalise_series n k s.
Proof.
intros s n m k.
unfold normalise_series.
unfold series_shrink, series_left_shift.
constructor; intros i.
unfold series_nth_fld.
remember Nbar.div_sup as f; simpl; subst f.
do 2 rewrite Nbar.fold_sub.
replace (stop s + fin m - fin (n + m))%Nbar with (stop s - fin n)%Nbar .
 remember (Nbar.div_sup (stop s - fin n) (fin (Pos.to_nat k))) as x eqn:Hx .
 destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁]; [ idtac | reflexivity ].
 subst x.
 remember (i * Pos.to_nat k)%nat as x.
 replace (n + m + x - m)%nat with (n + x)%nat by omega.
 subst x.
 destruct (lt_dec (n + m + i * Pos.to_nat k) m) as [H₂| H₂].
  rewrite Nat.add_shuffle0, Nat.add_comm in H₂.
  apply Nat.nle_gt in H₂.
  exfalso; apply H₂.
  apply Nat.le_add_r.

  reflexivity.

 simpl.
 destruct (stop s) as [st| ]; [ simpl | reflexivity ].
 apply Nbar.fin_inj_wd.
 omega.
Qed.

(* à revoir, s'il le faut...
Lemma greatest_series_x_power_le : ∀ s n₁ n₂ k,
  null_coeff_range_length fld s (S n₁) = fin n₂
  → greatest_series_x_power fld s n₁ = k
    → (Pos.to_nat k ≤ S n₂)%nat.
Proof.
intros s n₁ n₂ k Hn₂ Hk.
apply greatest_series_x_power_iff in Hk.
rewrite Hn₂ in Hk.
destruct Hk as (Hz, Hnz).
apply Nat.nlt_ge; intros H₁.
assert (S n₂ mod Pos.to_nat k ≠ 0)%nat as H.
 rewrite Nat.mod_small; [ intros H; discriminate H | assumption ].

 apply Hz in H.
 apply null_coeff_range_length_iff in Hn₂.
 destruct Hn₂ as (_, Hn₂).
 apply Hn₂.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 assumption.
Qed.
*)

(* exercice... *)
(* mmm... à voir... not sure it can be proved cause ¬∀ doesn't imply ∃
Lemma greatest_series_x_power_divides : ∀ s n₁ n₂ k,
  null_coeff_range_length fld s (S n₁) = fin n₂
  → greatest_series_x_power fld s n₁ = k
    → (k | S n₂)%nat.
Proof.
intros s n₁ n₂ k Hn₂ Hk.
aaa.
*)

Lemma normalised_series_null_coeff_range_length : ∀ s n k,
  null_coeff_range_length fld s 0 = fin n
  → null_coeff_range_length fld (normalise_series n k s) 0 = fin 0.
Proof.
intros s n k Hn.
apply null_coeff_range_length_iff in Hn.
apply null_coeff_range_length_iff.
simpl in Hn |- *.
destruct Hn as (Hz, Hnz).
split.
 intros i Hi.
 exfalso; revert Hi; apply Nat.nlt_0_r.

 unfold series_nth_fld in Hnz.
 destruct (Nbar.lt_dec (fin n) (stop s)) as [H₁| H₁].
  unfold series_nth_fld.
  remember (normalise_series n k s) as t eqn:Ht .
  destruct (Nbar.lt_dec 0 (stop t)) as [H₂| H₂].
   rewrite Ht; simpl.
   rewrite Nat.add_0_r; assumption.

   apply Nbar.nlt_ge in H₂.
   apply Nbar.le_0_r in H₂.
   rewrite Ht in H₂.
   unfold normalise_series in H₂.
   simpl in H₂.
   destruct (stop s) as [st| ]; [ idtac | discriminate H₂ ].
   simpl in H₂.
   apply Nbar.fin_inj_wd in H₂.
   apply Nbar.fin_lt_mono in H₁.
   remember (st - n)%nat as stn eqn:Hstn .
   symmetry in Hstn.
   destruct stn as [| stn].
    exfalso; revert Hstn; apply Nat.sub_gt; assumption.

    simpl in H₂.
    rewrite Nat.sub_0_r in H₂.
    remember (Pos.to_nat k) as pk.
    remember (stn + pk)%nat as x.
    replace pk with (1 * pk)%nat in Heqx by apply Nat.mul_1_l.
    subst pk x.
    rewrite Nat.div_add in H₂; [ idtac | apply Pos2Nat_ne_0 ].
    apply Nat.eq_add_0 in H₂.
    destruct H₂ as (_, H); discriminate H.

  exfalso; apply Hnz; reflexivity.
Qed.

(* à revoir, si nécessaire...
Lemma normalised_stretched_series : ∀ s n k,
  greatest_series_x_power fld s n = k
  → series_stretch fld k (normalise_series n k s) ≃ series_left_shift n s.
Proof.
intros s n k Hsf.
unfold normalise_series.
unfold series_shrink, series_left_shift.
remember Nbar.div_sup as f; simpl; subst f.
rewrite Nbar.fold_sub.
apply greatest_series_x_power_iff in Hsf.
remember (null_coeff_range_length fld s (S n)) as n₁ eqn:Hn₁ .
symmetry in Hn₁.
destruct n₁ as [n₁| ].
 destruct Hsf as (Hz, Hnz).
 assert (Pos.to_nat k ≠ 0)%nat as Hknz by apply Pos2Nat_ne_0.
 constructor; intros i.
 remember (Nbar.div_sup (stop s - fin n) (fin (Pos.to_nat k))) as x.
 unfold series_nth_fld; simpl.
 unfold series_nth_fld; simpl.
 rewrite Nbar.fold_sub.
 destruct (Nbar.lt_dec (fin i) (x * fin (Pos.to_nat k))) as [H₁| H₁].
  destruct (Nbar.lt_dec (fin i) (stop s - fin n)) as [H₂| H₂].
   destruct (zerop (i mod Pos.to_nat k)) as [H₃| H₃].
    apply Nat.mod_divides in H₃; [ idtac | assumption ].
    destruct H₃ as (c, H₃).
    rewrite Nat.mul_comm in H₃.
    subst i.
    rewrite Nat.div_mul; [ idtac | assumption ].
    destruct (Nbar.lt_dec (fin c) x) as [H₃| H₃].
     rewrite Nat.add_comm; reflexivity.

     exfalso; apply H₃; clear H₃.
     subst x.
     destruct (stop s) as [st| ]; [ idtac | constructor ].
     rewrite Nbar.fin_inj_mul in H₁.
     apply Nbar.lt_mul_r_lt_div_sup; [ idtac | assumption ].
     apply Nbar.lt_fin, Pos2Nat.is_pos.

    assert (i mod Pos.to_nat k ≠ 0)%nat as Hik.
     intros Hik.
     apply Nat.mod_divides in Hik; [ idtac | assumption ].
     destruct Hik as (c, Hi).
     subst i.
     rewrite Nat.mul_comm in H₃.
     rewrite Nat.mod_mul in H₃; [ idtac | assumption ].
     revert H₃; apply Nat.lt_irrefl.

     apply Hz in Hik.
     unfold series_nth_fld in Hik.
     symmetry.
     destruct (Nbar.lt_dec (fin (n + i)) (stop s)) as [H₄| H₄].
      assumption.

      exfalso; apply H₄.
      simpl in H₂.
      remember (stop s) as st eqn:Hst .
      destruct st as [st| ].
       apply Nbar.lt_fin.
       apply Nbar.fin_lt_mono in H₂.
       apply Nat.add_le_lt_mono with (n := n) (m := n) in H₂.
        rewrite Nat.add_sub_assoc in H₂.
         replace (n + st)%nat with (st + n)%nat in H₂ by apply Nat.add_comm.
         rewrite Nat.add_sub in H₂; assumption.

         destruct (lt_dec st n) as [H₅| H₅].
          subst x.
          simpl in H₁.
          replace (st - n)%nat with O in H₁ by fast_omega H₅.
          simpl in H₁.
          rewrite Nat.div_small in H₁.
           exfalso; revert H₁; apply Nbar.nlt_0_r.

           remember (Pos.to_nat k) as pk.
           destruct pk as [| pk]; [ assumption | idtac ].
           simpl; rewrite Nat.sub_0_r.
           apply Nat.lt_succ_diag_r.

          apply Nat.nlt_ge in H₅; assumption.

        reflexivity.

       constructor.

   destruct (zerop (i mod Pos.to_nat k)) as [H₃| H₃].
    apply Nat.mod_divides in H₃; [ idtac | assumption ].
    destruct H₃ as (c, Hi).
    subst i.
    rewrite Nat.mul_comm.
    rewrite Nat.div_mul; [ idtac | assumption ].
    destruct (Nbar.lt_dec (fin c) x) as [H₃| H₃].
     subst x.
     apply Nbar.lt_div_sup_lt_mul_r in H₃.
     exfalso; apply H₂.
     rewrite Nat.mul_comm; assumption.

     reflexivity.

    reflexivity.

  destruct (Nbar.lt_dec (fin i) (stop s - fin n)) as [H₂| H₂].
   destruct (zerop (i mod Pos.to_nat k)) as [H₃| H₃].
    apply Nat.mod_divides in H₃.
     destruct H₃ as (c, Hi).
     subst i.
     rewrite Nat.mul_comm.
     exfalso; apply H₁.
     subst x.
     rewrite Nat.mul_comm.
     rewrite Nbar.fin_inj_mul.
     apply Nbar.mul_lt_mono_pos_r.
      apply Nbar.fin_lt_mono, Pos2Nat.is_pos.

      intros H; discriminate H.

      intros H; discriminate H.

      apply Nbar.lt_mul_r_lt_div_sup.
       apply Nbar.fin_lt_mono, Pos2Nat.is_pos.

       rewrite Nbar.mul_comm.
       assumption.

     assumption.

    assert (i mod Pos.to_nat k ≠ 0)%nat as Hik.
     intros Hik.
     apply Nat.mod_divides in Hik; [ idtac | assumption ].
     destruct Hik as (c, Hi).
     subst i.
     rewrite Nat.mul_comm in H₃.
     rewrite Nat.mod_mul in H₃; [ idtac | assumption ].
     revert H₃; apply Nat.lt_irrefl.

     apply Hz in Hik.
     unfold series_nth_fld in Hik.
     destruct (Nbar.lt_dec (fin (n + i)) (stop s)) as [H₄| H₄].
      symmetry; assumption.

      exfalso; apply H₄; clear H₄.
      destruct (Nbar.lt_dec (stop s) (fin n)) as [H₄| H₄].
       destruct (stop s) as [st| ]; [ idtac | constructor ].
       apply Nbar.fin_lt_mono in H₂.
       apply Nbar.fin_lt_mono.
       apply Nbar.fin_lt_mono in H₄.
       fast_omega H₂ H₄.

       apply Nbar.nlt_ge in H₄.
       destruct (stop s) as [st| ]; [ idtac | constructor ].
       apply Nbar.fin_lt_mono in H₂.
       apply Nbar.fin_lt_mono.
       apply Nbar.fin_le_mono in H₄.
       fast_omega H₂ H₄.

   reflexivity.

 subst k.
 constructor; intros i.
 rewrite series_stretch_1.
 unfold series_nth_fld; simpl.
 destruct (stop s) as [st| ]; simpl.
  rewrite divmod_div, Nat.div_1_r, Nat.add_sub.
  rewrite Nat.mul_1_r, Nat.add_comm; reflexivity.

  rewrite Nat.mul_1_r, Nat.add_comm; reflexivity.
Qed.
*)

(* à revoir si nécessaire...
Lemma normalised_series : ∀ s n k,
  null_coeff_range_length fld s 0 = fin n
  → greatest_series_x_power fld s n = k
    → series_shift fld n (series_stretch fld k (normalise_series n k s)) ≃ s.
Proof.
intros s n k Hfn Hsf.
rewrite normalised_stretched_series; [ idtac | assumption ].
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.fold_sub.
apply null_coeff_range_length_iff in Hfn; simpl in Hfn.
destruct Hfn as (Hsz, Hsnz).
unfold series_nth_fld in Hsz.
destruct (lt_dec i n) as [H₃| H₃].
 apply Hsz in H₃; simpl in H₃.
 rewrite H₃.
 destruct (Nbar.lt_dec (fin i) (stop s - fin n + fin n)); reflexivity.

 apply Nat.nlt_ge in H₃.
 rewrite Nat.add_comm, Nat.sub_add; [ idtac | assumption ].
 destruct (Nbar.lt_dec (fin n) (stop s)) as [H₁| H₁].
  rewrite Nbar.sub_add; [ reflexivity | idtac ].
  apply Nbar.lt_le_incl; assumption.

  apply Nbar.nlt_ge in H₁.
  replace (stop s - fin n)%Nbar with 0%Nbar ; simpl.
   destruct (Nbar.lt_dec (fin i) (fin n)) as [H₂| H₂].
    apply Nbar.fin_lt_mono in H₂.
    apply Nat.nle_gt in H₂; contradiction.

    destruct (Nbar.lt_dec (fin i) (stop s)) as [H₄| H₄].
     exfalso; apply H₂.
     eapply Nbar.lt_le_trans; eassumption.

     reflexivity.

   destruct (stop s) as [st| ].
    apply Nbar.fin_le_mono in H₁.
    replace (st - n)%nat with O by fast_omega H₁.
    reflexivity.

    inversion H₁.
Qed.
*)

Lemma gcd_nz_add : ∀ nz n,
  gcd_nz (n + Z.to_nat (nz_valnum nz))
    (greatest_series_x_power fld
       (series_shift fld (Z.to_nat (nz_valnum nz)) (nz_terms nz))
       (n + Z.to_nat (nz_valnum nz))) (nz ∔ nz_zero fld) =
  gcd_nz n (greatest_series_x_power fld (nz_terms nz) n) nz.
Proof.
intros nz n.
unfold gcd_nz; simpl.
unfold nz_valnum_add.
rewrite Z.mul_1_r.
rewrite Nat2Z.inj_add.
rewrite Z.add_assoc.
rewrite Z.add_shuffle0.
rewrite <- Z.add_assoc.
rewrite Z.add_comm.
unfold cm; simpl.
rewrite Pos.mul_1_r.
remember (nz_valnum nz) as z eqn:Hz .
symmetry in Hz.
destruct z as [| z| z].
 simpl.
 rewrite Z.min_id.
 rewrite Z.add_0_r, Nat.add_0_r.
 rewrite series_shift_0.
 reflexivity.

 rewrite Z.min_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite greatest_series_x_power_shift.
 rewrite Z.add_0_r.
 rewrite Z2Nat.id; [ idtac | apply Pos2Z.is_nonneg ].
 reflexivity.

 rewrite Z.min_l; [ idtac | apply Pos2Z.neg_is_nonpos ].
 rewrite greatest_series_x_power_shift.
 f_equal.
 f_equal.
 symmetry; rewrite Z.add_comm.
 reflexivity.
Qed.

Lemma normalise_nz_add_0_r : ∀ nz,
  normalise_nz fld (nz ∔ nz_zero fld) ≐ normalise_nz fld nz.
Proof.
intros nz.
unfold normalise_nz; simpl.
rewrite nz_add_0_r.
rewrite null_coeff_range_length_shift.
remember (null_coeff_range_length fld (nz_terms nz) 0) as n₁ eqn:Hn₁ .
symmetry in Hn₁.
rewrite Nbar.add_comm.
destruct n₁ as [n₁| ]; [ simpl | reflexivity ].
constructor; constructor; simpl.
 unfold nz_valnum_add.
 rewrite Z.mul_1_r.
 rewrite nz_add_0_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.add_assoc, Z.add_shuffle0.
 rewrite Z2Nat_id_max, Z.min_comm.
 f_equal; [ idtac | apply gcd_nz_add ].
 remember (nz_valnum nz) as z eqn:Hz .
 symmetry in Hz.
 destruct z; reflexivity.

 unfold cm; simpl.
 rewrite Pos.mul_1_r.
 do 2 f_equal.
 rewrite nz_add_0_r.
 apply gcd_nz_add.

 rewrite nz_add_0_r.
 rewrite greatest_series_x_power_shift.
 constructor; intros i.
 rewrite normalise_series_add_shift.
 unfold gcd_nz; simpl.
 unfold cm; simpl.
 unfold nz_valnum_add.
 rewrite Z.mul_1_r, Pos.mul_1_r.
 rewrite Nat2Z.inj_add.
 destruct (nz_valnum nz) as [| p| p]; simpl.
  rewrite Z.add_0_r; reflexivity.

  rewrite positive_nat_Z.
  destruct (Z.of_nat n₁); try reflexivity.
  rewrite Pos.add_comm; reflexivity.

  rewrite Z.add_0_r; reflexivity.
Qed.

(* provable but supposes to use Bézout's identity
   probably complicated
Lemma normalised_series_greatest_series_x_power : ∀ s n k,
  null_coeff_range_length fld s 0 = fin n
  → greatest_series_x_power fld s n = k
    → greatest_series_x_power fld (normalise_series n k s) 0 = 1%positive.
Proof.
intros s n k Hn Hk.
aaa.

Lemma normalised_ps_greatest_series_x_power : ∀ nz nz₁,
  normalise_nz fld nz₁ = NonZero nz
  → greatest_series_x_power fld (nz_terms nz) 0 = 1%positive.
Proof.
intros nz nz₁ Hnorm.
aaa.
*)

(* probablement démontrable aussi avec null_coeff_range_length ... = fin 0
   comme but; à voir, peut-être, si nécessaire *)
Lemma null_coeff_range_length_normalised : ∀ nz nz₁ n,
  normalise_nz fld nz₁ = NonZero nz
  → null_coeff_range_length fld (nz_terms nz) 0 = fin n
    → n = O.
Proof.
intros nz nz₁ n Hnorm Hnz.
destruct n as [| n]; [ reflexivity | exfalso ].
apply null_coeff_range_length_iff in Hnz.
simpl in Hnz.
destruct Hnz as (Hz, Hnz).
pose proof (Hz O (Nat.lt_0_succ n)) as H₀.
unfold normalise_nz in Hnorm.
remember (null_coeff_range_length fld (nz_terms nz₁) 0) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; [ idtac | discriminate Hnorm ].
apply null_coeff_range_length_iff in Hm.
simpl in Hm.
destruct Hm as (Hmz, Hmnz).
unfold series_nth_fld in Hmnz.
destruct (Nbar.lt_dec (fin m) (stop (nz_terms nz₁))) as [H₂| H₂].
 injection Hnorm; clear Hnorm; intros; subst nz.
 simpl in Hz, Hnz, H₀.
 unfold series_nth_fld in H₀.
 simpl in H₀.
 rewrite Nbar.fold_sub in H₀.
 rewrite Nbar.fold_sub in H₀.
 rewrite Nbar.fold_div in H₀.
 remember (greatest_series_x_power fld (nz_terms nz₁) m) as k eqn:Hk .
 symmetry in Hk.
 remember (gcd_nz m k nz₁) as g eqn:Hg .
 remember (Z.to_pos g) as gp eqn:Hgp .
 remember (stop (nz_terms nz₁) - fin m + fin (Pos.to_nat gp) - 1)%Nbar as x.
 symmetry in Heqx.
 rewrite Nat.add_0_r in H₀.
 destruct (Nbar.lt_dec 0 (x / fin (Pos.to_nat gp))) as [H₁| H₁].
  rewrite H₀ in Hmnz; apply Hmnz; reflexivity.

  remember (stop (nz_terms nz₁) - fin m)%Nbar as y.
  symmetry in Heqy.
  destruct y as [y| ].
   destruct y as [| y].
    revert Heqy; apply Nbar.sub_gt; assumption.

    simpl in Heqx.
    rewrite Nat.sub_0_r in Heqx.
    apply H₁.
    rewrite <- Heqx; simpl.
    remember (y + Pos.to_nat gp)%nat as z.
    replace (Pos.to_nat gp) with (1 * Pos.to_nat gp)%nat in Heqz .
     subst z.
     rewrite Nat.div_add.
      apply Nbar.lt_fin.
      rewrite Nat.add_comm.
      apply Nat.lt_0_succ.

      apply Pos2Nat_ne_0.

     rewrite Nat.mul_1_l; reflexivity.

   subst x; simpl.
   apply H₁; simpl.
   constructor.

 apply Hmnz; reflexivity.
Qed.

Lemma nz_norm_add_0 : ∀ nz₁ nz₂,
  normalise_nz fld nz₁ ≐ normalise_nz fld nz₂
  → normalise_nz fld (nz₁ ∔ nz_zero fld) ≐
    normalise_nz fld (nz₂ ∔ nz_zero fld).
Proof.
intros nz₁ nz₂ Heq.
rewrite normalise_nz_add_0_r.
rewrite normalise_nz_add_0_r.
assumption.
Qed.

(* une idée, comme ça... mais qui marche ! *)
Lemma normalised_nz_norm_add_compat_r : ∀ nz₁ nz₂ nz₃,
  normalise_nz fld nz₁ ≐ normalise_nz fld nz₂
  → (normalise_nz fld nz₁ + normalise_nz fld nz₃ ≈
     normalise_nz fld nz₂ + normalise_nz fld nz₃)%ps.
Proof.
(* à nettoyer sérieusement *)
intros nz₁ nz₂ nz₃ Heqp.
remember (normalise_nz fld nz₁) as ps₁ eqn:Hps₁ .
remember (normalise_nz fld nz₂) as ps₂ eqn:Hps₂ .
remember (normalise_nz fld nz₃) as ps₃ eqn:Hps₃ .
symmetry in Hps₁, Hps₂, Hps₃.
destruct ps₃ as [nz'₃| ].
 destruct ps₁ as [nz'₁| ].
  destruct ps₂ as [nz'₂| ].
   simpl.
   constructor.
   inversion Heqp.
   clear nz₁0 H.
   clear nz₂0 H0.
   unfold normalise_nz.
   simpl.
   remember (null_coeff_range_length fld (nz_terms_add fld nz'₁ nz'₃) 0) as
     n₁ eqn:Hn₁ .
   remember (null_coeff_range_length fld (nz_terms_add fld nz'₂ nz'₃) 0) as
     n₂ eqn:Hn₂ .
   symmetry in Hn₁, Hn₂.
   unfold nz_terms_add in Hn₁.
   unfold nz_terms_add in Hn₂.
   unfold cm_factor in Hn₁.
   unfold cm_factor in Hn₂.
   inversion_clear H1.
   unfold adjust_series in Hn₁, Hn₂.
   rewrite H, H0, H2 in Hn₁.
   rewrite Hn₁ in Hn₂.
   move Hn₂ at top; subst n₁.
   destruct n₂ as [n₂| ].
    constructor; constructor; simpl.
     unfold nz_valnum_add, gcd_nz; simpl.
     unfold nz_valnum_add; simpl.
     unfold cm_factor, cm; simpl.
     rewrite H, H0.
     do 3 f_equal.
     unfold nz_terms_add.
     unfold cm_factor; simpl.
     rewrite H, H0.
     unfold adjust_series.
     rewrite H2.
     reflexivity.

     unfold cm; simpl.
     unfold nz_terms_add; simpl.
     unfold cm_factor; simpl.
     rewrite H, H0.
     unfold adjust_series; simpl.
     rewrite H2.
     do 2 f_equal.
     unfold gcd_nz; simpl.
     unfold nz_valnum_add; simpl.
     rewrite H.
     unfold cm_factor, cm.
     rewrite H0.
     reflexivity.

     unfold gcd_nz; simpl.
     unfold nz_valnum_add; simpl.
     unfold cm_factor, cm; simpl.
     rewrite H.
     rewrite H0.
     unfold nz_terms_add; simpl.
     unfold cm_factor, cm; simpl.
     rewrite H.
     rewrite H0.
     constructor; simpl.
     unfold adjust_series; simpl.
     intros i.
     rewrite H2 in |- * at 1.
     rewrite H2 in |- * at 1.
     reflexivity.

    constructor.

   simpl.
   constructor.
   unfold normalise_nz.
   simpl.
   inversion Heqp.

  inversion Heqp.
  reflexivity.

 inversion Heqp.
  simpl.
  constructor.
  unfold normalise_nz; simpl.
  inversion_clear H.
  rewrite H4.
  remember (null_coeff_range_length fld (nz_terms nz₂0) 0) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ]; [ idtac | reflexivity ].
  unfold gcd_nz.
  constructor; constructor; simpl; rewrite H2, H3, H4; reflexivity.

  reflexivity.
Qed.

Definition normalise_ps ps :=
  match ps with
  | NonZero nz => normalise_nz fld nz
  | Zero => Zero _
  end.

Lemma series_nth_normalised : ∀ s n g,
  null_coeff_range_length fld s 0 = fin n
  → ∀ i,
    series_nth_fld fld i (normalise_series n g s) =
    series_nth_fld fld (n + i * Pos.to_nat g) s.
Proof.
intros s n g Hn i.
unfold series_nth_fld; simpl.
do 2 rewrite Nbar.fold_sub.
rewrite Nbar.fold_div.
remember (Pos.to_nat g) as gn eqn:Hgn .
remember ((stop s - fin n + fin gn - 1) / fin gn)%Nbar as x.
remember (fin (n + i * gn)) as y.
destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁].
 destruct (Nbar.lt_dec y (stop s)) as [H₂| H₂]; [ reflexivity | exfalso ].
 subst x y gn.
 apply H₂; clear H₂.
 remember (stop s) as st eqn:Hst .
 symmetry in Hst.
 destruct st as [st| ]; [ idtac | constructor ].
 simpl in H₁.
 apply Nbar.fin_lt_mono in H₁.
 apply Nbar.fin_lt_mono.
 rewrite Nat_fold_div_sup in H₁.
 apply Nat_lt_div_sup_lt_mul_r in H₁.
 apply Nat.lt_add_lt_sub_l; assumption.

 destruct (Nbar.lt_dec y (stop s)) as [H₂| H₂]; [ exfalso | reflexivity ].
 subst x y gn.
 apply H₁; clear H₁.
 remember (stop s) as st eqn:Hst .
 symmetry in Hst.
 destruct st as [st| ]; [ simpl | constructor ].
 apply Nbar.fin_lt_mono in H₂.
 apply Nbar.fin_lt_mono.
 rewrite Nat_fold_div_sup.
 apply Nat_lt_mul_r_lt_div_sup; [ apply Pos2Nat.is_pos | idtac ].
 apply Nat.lt_add_lt_sub_l; assumption.
Qed.

(* peut-être pas nécessaire... *)
Lemma series_nth_normalised₁ : ∀ nz nz' n k g,
  normalise_nz fld nz = NonZero nz'
  → null_coeff_range_length fld (nz_terms nz) 0 = fin n
    → greatest_series_x_power fld (nz_terms nz) n = k
      → gcd_nz n k nz = g
        → ∀ i,
          series_nth_fld fld i (nz_terms nz') =
          series_nth_fld fld (n + i * Pos.to_nat (Z.to_pos g)) (nz_terms nz).
Proof.
intros nz nz' n k g Heq Hn Hk Hg i.
unfold normalise_nz in Heq.
rewrite Hn in Heq.
injection Heq; clear Heq; intros Heq; subst nz'; simpl.
rewrite Hk, Hg.
eapply series_nth_normalised; assumption.
Qed.

(* pas mieux que sans liste... l'induction par n déconne...
Fixpoint nonzero_list s b n :=
  match null_coeff_range_length fld s b with
  | fin m =>
      match n with
      | O => [m]
      | S n' => [m … nonzero_list s (S m) n']
      end
  | ∞ => []
  end.

Lemma sss : ∀ nz nz' n zl zl',
  normalise_nz fld nz = NonZero nz'
  → zl = nonzero_list (nz_terms nz) 0 n
    → zl' = nonzero_list (nz_terms nz') 0 n
      → List.map (λ i, series_nth_fld fld i (nz_terms nz)) zl =
        List.map (λ i, series_nth_fld fld i (nz_terms nz')) zl'.
Proof.
intros nz nz' n zl zl' Heq Hzl Hzl'.
subst zl zl'.
induction n as [| n]; simpl.
 remember (null_coeff_range_length fld (nz_terms nz) 0) as i eqn:Hi .
 remember (null_coeff_range_length fld (nz_terms nz') 0) as j eqn:Hj .
 symmetry in Hi, Hj.
 destruct i as [i| ].
  destruct j as [j| ]; [ simpl | exfalso ].
   f_equal.
   erewrite series_nth_normalised with (nz' := nz'); eauto .
   eapply null_coeff_range_length_normalised in Heq; [ idtac | eassumption ].
   subst j; rewrite Nat.mul_0_l, Nat.add_0_r; reflexivity.

   eapply series_nth_normalised with (i := O) in Heq; eauto .
   rewrite Nat.mul_0_l, Nat.add_0_r in Heq.
   apply null_coeff_range_length_iff in Hi; simpl in Hi.
   apply null_coeff_range_length_iff in Hj; simpl in Hj.
   destruct Hi as (Hz, Hnz).
   apply Hnz.
   rewrite <- Heq.
   apply Hj; reflexivity.

  destruct j as [j| ]; [ exfalso | reflexivity ].
  unfold normalise_nz in Heq.
  rewrite Hi in Heq; discriminate Heq.
bbb.
*)

Fixpoint nth_nonzero s b n :=
  match n with
  | O => null_coeff_range_length fld s b
  | S n' =>
      match null_coeff_range_length fld s b with
      | fin m => nth_nonzero s (S m) n'
      | ∞ => ∞
      end
  end.

(*
Lemma ttt : ∀ nz nz' n i j,
  normalise_nz fld nz = NonZero nz'
  → nth_nonzero (nz_terms nz) 0 n = fin i
    → nth_nonzero (nz_terms nz') 0 n = fin j
      → series_nth_fld fld i (nz_terms nz) =
        series_nth_fld fld j (nz_terms nz').
Proof.
intros nz nz' n i j Heq Hi Hj.
revert i j Hi Hj.
induction n; intros.
 erewrite series_nth_normalised with (nz' := nz'); eauto .
 eapply null_coeff_range_length_normalised in Heq; [ idtac | eassumption ].
 subst j; rewrite Nat.mul_0_l, Nat.add_0_r; reflexivity.

 simpl in Hi, Hj.
 remember (null_coeff_range_length fld (nz_terms nz) 0) as m eqn:Hm .
 remember (null_coeff_range_length fld (nz_terms nz') 0) as m' eqn:Hm' .
 symmetry in Hm, Hm'.
 destruct m as [m| ]; [ idtac | discriminate Hi ].
 destruct m' as [m'| ]; [ idtac | discriminate Hj ].
 destruct n as [| n].
  simpl in Hi, Hj.
  erewrite series_nth_normalised with (nz' := nz'); eauto .

bbb.
*)

(*
Lemma uuu : ∀ nz nz' n m p k g,
  normalise_nz fld nz = NonZero nz'
  → null_coeff_range_length fld (nz_terms nz) 0 = fin n
    → null_coeff_range_length fld (nz_terms nz) (S n) = fin p
      → null_coeff_range_length fld (nz_terms nz') 1 = fin m
       → greatest_series_x_power fld (nz_terms nz) n = k
         → gcd_nz n k nz = g
           → S p = (S m * Pos.to_nat g)%nat.
Proof.
intros nz nz' n m p k g Heq Hn Hp Hm Hk Hg.
destruct (lt_dec (S p) (S m * Pos.to_nat g)) as [H₁| H₁].
 exfalso.
bbb.
*)

(* pas très joli mais bon, si ça fait l'affaire... *)
Lemma gcd_mul_le : ∀ a b c g,
  Z.gcd a (' b) = g
  → (' b = c * g)%Z
    → (0 <= g ∧ 0 <= c)%Z.
Proof.
intros a b c g Hg Hb.
assert (0 <= g)%Z as Hgpos by (subst g; unfold gcd_nz; apply Z.gcd_nonneg).
split; [ assumption | idtac ].
assert (g ≠ 0)%Z as Hgnz.
 subst g; intros H; apply Z.gcd_eq_0_r in H.
 revert H; apply Pos2Z_ne_0.

 apply Z.mul_nonneg_cancel_r with (m := g).
  fast_omega Hgpos Hgnz.

  rewrite <- Hb; apply Pos2Z.is_nonneg.
Qed.

Lemma gcd_pos_pos : ∀ a b g,
  Z.gcd a (' b) = g
  → (0 < g)%Z.
Proof.
intros a b g Hg.
destruct (Z_dec 0 g) as [[H| H]| H].
 assumption.

 exfalso; apply Z.gt_lt, Z.nle_gt in H.
 apply H; subst g; apply Z.gcd_nonneg.

 rewrite <- H in Hg.
 apply Z.gcd_eq_0_r in Hg.
 exfalso; revert Hg; apply Pos2Z_ne_0.
Qed.

Lemma gcd_pos_ne_0 : ∀ a b g,
  Z.gcd a (' b) = g
  → (g ≠ 0)%Z.
Proof.
intros a b g Hg.
destruct (Z_dec 0 g) as [[H| H]| H].
 intros HH; rewrite HH in H.
 revert H; apply Z.lt_irrefl.

 intros HH; rewrite HH in H.
 apply Z.gt_lt in H.
 revert H; apply Z.lt_irrefl.

 rewrite <- H in Hg.
 apply Z.gcd_eq_0_r in Hg.
 exfalso; revert Hg; apply Pos2Z_ne_0.
Qed.

Lemma Z2Nat_gcd_ne_0 : ∀ a b g,
  Z.gcd a (' b) = g
  → (Z.to_nat g ≠ 0)%nat.
Proof.
intros a b g Hg.
apply gcd_pos_pos in Hg.
destruct g; [ exfalso; revert Hg; apply Z.lt_irrefl | idtac | idtac ].
 apply Pos2Nat_ne_0.

 exfalso; apply Z.nle_gt in Hg.
 apply Hg, Pos2Z.neg_is_nonpos.
Qed.

Lemma gcd_mul_ne_0 : ∀ a b c g,
  Z.gcd a (' b) = g
  → (' b = c * g)%Z
    → (Z.to_nat c ≠ 0)%nat.
Proof.
intros a b c g Hg Hb.
eapply gcd_mul_le in Hg; [ idtac | eassumption ].
destruct Hg as (Hg, Hc).
destruct c as [| c| c].
 exfalso; revert Hb; apply Pos2Z_ne_0.

 apply Pos2Nat_ne_0.

 exfalso; apply Z.nlt_ge in Hc.
 apply Hc, Pos2Z.neg_is_neg.
Qed.

Lemma gcd_mul_pos : ∀ a b c g,
  Z.gcd a (' b) = g
  → (' b = c * g)%Z
    → (0 < c)%Z.
Proof.
intros a b c g Hg Hb.
eapply gcd_mul_le in Hg; [ idtac | eassumption ].
destruct Hg as (Hg, Hc).
destruct c as [| c| c].
 exfalso; revert Hb; apply Pos2Z_ne_0.

 apply Pos2Z.is_pos.

 exfalso; apply Z.nlt_ge in Hc.
 apply Hc, Pos2Z.neg_is_neg.
Qed.

(* compatibilité avec l'ancienne version, vu que les preuves y avaient
   été faites avec ça et les reprendre semble pas simple *)
Definition is_the_greatest_series_x_power₃ s n k :=
  match null_coeff_range_length fld s (S n) with
  | fin _ =>
      (∀ i, i mod (Pos.to_nat k) ≠ O →
       series_nth_fld fld (n + i) s ≍ zero fld) ∧
      (∀ k', (Pos.to_nat k < k')%nat →
       ∃ i, i mod k' ≠ O ∧ series_nth_fld fld (n + i) s ≭ zero fld)
  | ∞ =>
      k = 1%positive
  end.

(* mouais... ça a pas l'air simple...
Lemma yyy : ∀ s n k,
  is_the_greatest_series_x_power fld s n k
  ↔ is_the_greatest_series_x_power₃ s n k.
Proof.
intros s n k.
split; intros H₁.
 unfold is_the_greatest_series_x_power in H₁.
 unfold is_the_greatest_series_x_power₃.
 destruct H₁ as (H₁, H₂).
 unfold is_a_series_in_x_power in H₁.
 rename n into m.
 remember (null_coeff_range_length fld s (S m)) as p eqn:Hp .
 symmetry in Hp.
 destruct p as [p| ].
  split.
   intros i H₃.
   assert
    (forall n,
     nth_null_coeff_range_length fld s n m ≠ 0
     → i mod nth_null_coeff_range_length fld s n m ≠ 0)%nat 
    as H₄.
    intros n H₄ H₅; apply H₃.
    apply Nat.mod_divides; auto.
    apply Nat_divides_l.
    apply Nat.mod_divides in H₅; [ idtac | assumption ].
    apply Nat_divides_l in H₅.
    etransitivity; [ apply H₁ | eassumption ].
bbb.
*)

(*
Lemma normalised_greatest_series_x_power : ∀ nz n k g,
  null_coeff_range_length fld (nz_terms nz) 0 = fin n
  → greatest_series_x_power fld (nz_terms nz) n = k
    → gcd_nz n k nz = g
      → greatest_series_x_power fld
          (normalise_series n (Z.to_pos g) (nz_terms nz)) 0 =
        Pos.of_nat (Pos.to_nat k / Z.to_nat g).
Proof.
-- gros nettoyage à faire : grosse répétition --
intros nz n k g Hn Hk Hg.
unfold gcd_nz in Hg.
remember (nz_valnum nz + Z.of_nat n)%Z as vn eqn:Hvn .
pose proof (Z.gcd_divide_r (Z.gcd vn (' nz_comden nz)) (' k)) as H.
rewrite Hg in H.
destruct H as (k', Hk').
apply greatest_series_x_power_iff in Hk.
apply yyy in Hk; unfold is_the_greatest_series_x_power₃ in Hk.
apply greatest_series_x_power_iff.
apply yyy; unfold is_the_greatest_series_x_power₃.
remember (normalise_series n (Z.to_pos g) (nz_terms nz)) as s eqn:Hs .
remember (null_coeff_range_length fld s 1) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; simpl.
 split.
  intros i H.
  rewrite Nat2Pos.id in H.
   rewrite Hs.
   rewrite series_nth_normalised; [ idtac | assumption ].
   remember (null_coeff_range_length fld (nz_terms nz) (S n)) as p eqn:Hp .
   symmetry in Hp.
   destruct p as [p| ].
    destruct Hk as (Hz, Hnz).
    apply Hz.
    intros H₁; apply H; clear H.
    do 2 rewrite <- Z2Nat.inj_pos in H₁.
    rewrite <- Z2Nat.inj_pos.
    rewrite Hk' in H₁ |- *.
    rewrite Z2Nat.inj_mul; try (edestruct gcd_mul_le; eassumption).
    rewrite Z2Pos.id in H₁; [ idtac | eapply gcd_pos_pos; eassumption ].
    rewrite Z2Nat.inj_mul in H₁; try (edestruct gcd_mul_le; eassumption).
    rewrite Nat.mul_mod_distr_r in H₁.
     apply Nat.mul_eq_0_l in H₁.
      rewrite Nat.div_mul; [ idtac | eapply Z2Nat_gcd_ne_0; eassumption ].
      assumption.

      eapply Z2Nat_gcd_ne_0; eassumption.

     eapply gcd_mul_ne_0; eassumption.

     eapply Z2Nat_gcd_ne_0; eassumption.

    subst k.
    symmetry in Hk'.
    rewrite Z.mul_comm in Hk'.
    apply Z.eq_mul_1 in Hk'.
    destruct Hk' as [Hk'| Hk'].
     move Hk' at top; subst g.
     rewrite Nat.div_same in H; [ idtac | intros H₁; discriminate H₁ ].
     exfalso; apply H; reflexivity.

     apply gcd_pos_pos in Hg.
     subst g.
     apply Z.nle_gt in Hg.
     exfalso; apply Hg.
     apply Z.opp_nonpos_nonneg, Z.le_0_1.

   rewrite <- Z2Nat.inj_pos, Hk'.
   rewrite Z2Nat.inj_mul.
    rewrite Nat.div_mul.
     eapply gcd_mul_ne_0; eassumption.

     eapply Z2Nat_gcd_ne_0; eassumption.

    eapply gcd_mul_le in Hg; [ idtac | eassumption ].
    destruct Hg; assumption.

    eapply gcd_mul_le in Hg; [ idtac | eassumption ].
    destruct Hg; assumption.

  intros k₁ Hk₁.
  rewrite Nat2Pos.id in Hk₁.
   rewrite <- Z2Nat.inj_pos in Hk₁.
   rewrite Hk' in Hk₁.
   rewrite Z2Nat.inj_mul in Hk₁.
    rewrite Nat.div_mul in Hk₁.
     remember (null_coeff_range_length fld (nz_terms nz) (S n)) as p eqn:Hp .
     symmetry in Hp.
     destruct p as [p| ].
      destruct Hk as (Hz, Hnz).
      apply Nat.mul_lt_mono_pos_r with (p := Z.to_nat g) in Hk₁.
       rewrite <- Z2Nat.inj_mul, <- Hk' in Hk₁.
        apply Hnz in Hk₁.
        destruct Hk₁ as (j, (Hjm, Hjn)).
        destruct (zerop (j mod Z.to_nat g)) as [H₁| H₁].
         apply Nat.mod_divides in H₁.
          destruct H₁ as (j', Hj').
          subst j.
          rewrite Nat.mul_comm in Hjn.
          rewrite <- Pos2Nat_to_pos in Hjn.
           rewrite <- series_nth_normalised in Hjn; [ idtac | assumption ].
           rewrite <- Hs in Hjn.
           rewrite Nat.mul_comm in Hjm.
           destruct k₁ as [| k₁]; [ exfalso; apply Hjm; reflexivity | idtac ].
           rewrite Nat.mul_mod_distr_r in Hjm.
            apply Nat.neq_mul_0 in Hjm.
            destruct Hjm as (Hjk, Hgz).
            exists j'; split; assumption.

            intros H; discriminate H.

            eapply Z2Nat_gcd_ne_0; eassumption.

           eapply gcd_pos_pos; eassumption.

          eapply Z2Nat_gcd_ne_0; eassumption.

         assert (j mod Pos.to_nat k ≠ 0)%nat as H₂.
          intros H.
          apply Nat.mod_divides in H; [ idtac | apply Pos2Nat_ne_0 ].
          destruct H as (j', Hj'); subst j.
          rewrite <- Z2Nat.inj_pos in H₁.
          rewrite Hk' in H₁.
          rewrite Z2Nat.inj_mul, Nat.mul_shuffle0 in H₁.
           rewrite Nat.mod_mul in H₁.
            revert H₁; apply Nat.lt_irrefl.

            eapply Z2Nat_gcd_ne_0; eassumption.

           eapply gcd_mul_le in Hk'; [ idtac | eassumption ].
           destruct Hk'; assumption.

           eapply gcd_mul_le in Hk'; [ idtac | eassumption ].
           destruct Hk'; assumption.

          exfalso; apply Hjn, Hz; assumption.

        eapply gcd_mul_le in Hk'; [ idtac | eassumption ].
        destruct Hk'; assumption.

        eapply gcd_mul_le in Hk'; [ idtac | eassumption ].
        destruct Hk'; assumption.

       rewrite <- Z2Nat.inj_0.
       apply Z2Nat.inj_lt; [ reflexivity | idtac | idtac ].
        eapply gcd_mul_le in Hk'; [ idtac | eassumption ].
        destruct Hk'; assumption.

        eapply gcd_pos_pos; eassumption.

      subst k.
      rewrite Z.gcd_1_r in Hg.
      move Hg at top; subst g.
      exfalso.
      apply null_coeff_range_length_iff in Hm.
      destruct Hm as (Hz, Hnz).
      apply Hnz; simpl.
      rewrite Hs.
      rewrite series_nth_normalised; [ idtac | assumption ].
      apply null_coeff_range_length_iff in Hp.
      rewrite Nat.mul_1_r.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l.
      apply Hp.

     eapply Z2Nat_gcd_ne_0; eassumption.

    eapply gcd_mul_le in Hk'; [ idtac | eassumption ].
    destruct Hk'; assumption.

    eapply gcd_mul_le in Hk'; [ idtac | eassumption ].
    destruct Hk'; assumption.

   rewrite <- Z2Nat.inj_pos, Hk'.
   rewrite Z2Nat.inj_mul.
    rewrite Nat.div_mul.
     eapply gcd_mul_ne_0; eassumption.

     eapply Z2Nat_gcd_ne_0; eassumption.

    eapply gcd_mul_le in Hg; [ idtac | eassumption ].
    destruct Hg; assumption.

    eapply gcd_mul_le in Hg; [ idtac | eassumption ].
    destruct Hg; assumption.

 remember (null_coeff_range_length fld (nz_terms nz) (S n)) as p eqn:Hp .
 symmetry in Hp.
 destruct p as [p| ].
  apply null_coeff_range_length_iff in Hm; simpl in Hm.
  apply null_coeff_range_length_iff in Hp; simpl in Hp.
  destruct Hp as (Hz, Hnz).
  rewrite <- Nat.add_succ_r in Hnz.
  destruct (zerop (S p mod Pos.to_nat k)) as [H₁| H₁].
   apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
   destruct H₁ as (p', Hp').
   rewrite Hp' in Hnz.
   exfalso; apply Hnz.
   rewrite Nat.mul_comm.
   rewrite <- Z2Nat.inj_pos, Hk'.
   rewrite Z2Nat.inj_mul, Nat.mul_assoc.
    rewrite Nat.mul_comm.
    rewrite <- Pos2Nat_to_pos.
     rewrite Nat.mul_comm.
     rewrite <- series_nth_normalised; [ idtac | assumption ].
     rewrite <- Hs.
     remember (p' * Z.to_nat k')%nat as pk eqn:Hpk .
     symmetry in Hpk.
     destruct pk as [| pk].
      apply Nat.mul_eq_0_l in Hpk.
       subst p'.
       rewrite Nat.mul_0_r in Hp'; discriminate Hp'.

       eapply gcd_mul_ne_0; eassumption.

      apply Hm.

     eapply gcd_pos_pos; eassumption.

    eapply gcd_mul_le in Hg; [ idtac | eassumption ].
    destruct Hg; assumption.

    eapply gcd_mul_le in Hg; [ idtac | eassumption ].
    destruct Hg; assumption.

   destruct Hk as (Hz₁, Hnz₁).
   rewrite Hz₁ in Hnz.
    exfalso; apply Hnz; reflexivity.

    intros H.
    rewrite H in H₁.
    revert H₁; apply Nat.lt_irrefl.

  subst k.
  symmetry in Hk'.
  rewrite Z.mul_comm in Hk'.
  apply Z.mul_eq_1 in Hk'.
  destruct Hk' as [Hk'| Hk'].
   move Hk' at top; subst g.
   rewrite Nat.div_same; [ idtac | intros H₁; discriminate H₁ ].
   reflexivity.

   apply gcd_pos_pos in Hg.
   subst g.
   apply Z.nle_gt in Hg.
   exfalso; apply Hg.
   apply Z.opp_nonpos_nonneg, Z.le_0_1.
Qed.
*)

Lemma normalise_series_0_1 : ∀ s : series α, normalise_series 0 1 s ≃ s.
Proof.
intros s.
constructor; intros i.
unfold series_nth_fld.
remember (normalise_series 0 1 s) as ns eqn:Hns .
destruct (Nbar.lt_dec (fin i) (stop ns)) as [H₁| H₁].
 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₂| H₂].
  rewrite Hns; simpl.
  rewrite Nat.mul_1_r; reflexivity.

  exfalso; apply H₂; clear H₂.
  rewrite Hns in H₁; simpl in H₁.
  destruct (stop s) as [st| ]; [ idtac | constructor ].
  simpl in H₁.
  rewrite Nat.sub_0_r in H₁.
  rewrite Pos2Nat.inj_1 in H₁.
  rewrite <- Nat_sub_sub_distr in H₁; [ idtac | reflexivity ].
  rewrite Nat.sub_diag, Nat.sub_0_r in H₁.
  rewrite divmod_div in H₁.
  rewrite Nat.div_1_r in H₁; assumption.

 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₂| ]; [ idtac | reflexivity ].
 exfalso; apply H₁; clear H₁.
 subst ns; simpl.
 destruct (stop s) as [st| ]; [ simpl | constructor ].
 rewrite Nat.sub_0_r.
 rewrite Pos2Nat.inj_1.
 rewrite <- Nat_sub_sub_distr; [ idtac | reflexivity ].
 rewrite Nat.sub_diag, Nat.sub_0_r.
 rewrite divmod_div.
 rewrite Nat.div_1_r; assumption.
Qed.

(* mouais... à voir si nécessaire...
Lemma normalise_nz_is_projection : ∀ nz,
  normalise_ps (normalise_nz fld nz) ≈ normalise_nz fld nz.
Proof.
intros nz.
remember (normalise_nz fld nz) as ps eqn:Hps .
rewrite Hps in |- * at 2.
symmetry in Hps.
destruct ps as [nz'| ]; simpl.
 unfold normalise_nz; simpl.
 remember (null_coeff_range_length fld (nz_terms nz') 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ].
  eapply null_coeff_range_length_normalised in Hn; [ idtac | eassumption ].
  subst n; simpl.
  rewrite Z.add_0_r.
  remember (null_coeff_range_length fld (nz_terms nz) 0) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ].
   constructor; simpl.
   unfold normalise_nz in Hps.
   rewrite Hn in Hps.
   injection Hps; clear Hps; intros; subst nz'; simpl.
   remember (greatest_series_x_power fld (nz_terms nz) n) as k eqn:Hk .
   remember (gcd_nz n k nz) as g eqn:Hg .
   symmetry in Hg.
   assert (0 <= g)%Z as A₁ by (rewrite <- Hg; apply Z.gcd_nonneg).
   assert (g ≠ 0)%Z as A₂ by (eapply gcd_pos_ne_0; eassumption).
   assert (Z.to_nat g ≠ 0)%nat as A₃ by (eapply Z2Nat_gcd_ne_0; eassumption).
   assert (0 < ' nz_comden nz / g)%Z as A₄
    by (unfold gcd_nz in Hg; rewrite Z.gcd_comm, Z.gcd_assoc in Hg;
         remember (Z.gcd (' k) (nz_valnum nz + Z.of_nat n)) as a;
         pose proof (Z.gcd_divide_r a (' nz_comden nz)) as H; 
         rewrite Hg in H; destruct H as (c, H); rewrite H; 
         rewrite Z.div_mul; [ idtac | assumption ]; 
         eapply gcd_mul_pos; eassumption).
   assert (0 < Pos.to_nat k / Z.to_nat g)%nat as A₅
    by (unfold gcd_nz in Hg;
         pose proof
          (Z.gcd_divide_r
             (Z.gcd (nz_valnum nz + Z.of_nat n) (' nz_comden nz)) 
             (' k)) as H; rewrite Hg in H; rewrite <- Z2Nat.inj_pos;
         destruct H as (c, H); rewrite H; rewrite Z2Nat.inj_mul;
         [ rewrite Nat.div_mul; [ idtac | assumption ]; apply Nat.neq_0_lt_0;
            eapply gcd_mul_ne_0; eassumption
         | eapply gcd_mul_le in Hg; [ idtac | eassumption ]; destruct Hg;
            assumption
         | eapply gcd_mul_le in Hg; [ idtac | eassumption ]; destruct Hg;
            assumption ]).
   assert (0 < ' Z.to_pos (' nz_comden nz / g))%Z as A₆
    by (rewrite Z2Pos.id; assumption).
   remember (normalise_series n (Z.to_pos g) (nz_terms nz)) as s eqn:Hs .
   remember (greatest_series_x_power fld s 0) as k₁ eqn:Hk₁ .
   unfold gcd_nz; simpl.
   rewrite Z.add_0_r.
   remember (nz_valnum nz + Z.of_nat n)%Z as vn eqn:Hvn .
   remember (Z.to_pos (' nz_comden nz / g)) as cg eqn:Hcg .
   remember (Z.gcd (Z.gcd (vn / g) (' cg)) (' k₁)) as g₁ eqn:Hg₁ .
   unfold normalise_nz; simpl.
   remember (null_coeff_range_length fld s 0) as m eqn:Hm .
   rewrite Hs in Hm.
   rewrite normalised_series_null_coeff_range_length in Hm;
     [ idtac | assumption ].
   subst m.
   rewrite Hs in Hk₁.
   symmetry in Hk.
bbb.
   erewrite normalised_greatest_series_x_power in Hk₁; try eassumption.
   remember (Z.gcd (vn / g) (' cg)) as g₂ eqn:Hg₂ .
   rewrite Hcg in Hg₂.
   remember Hg as Hg_v; clear HeqHg_v.
   unfold gcd_nz in Hg.
   rewrite <- Hvn in Hg.
   remember (Z.gcd vn (' nz_comden nz)) as g₃ eqn:Hg₃ .
   rewrite Hg₃ in Hg.
   symmetry in Hg.
   apply Z_gcd3_div_gcd3 in Hg; [ idtac | assumption ].
   rewrite Z2Pos.id in Hg₂; [ idtac | assumption ].
   rewrite <- Hg₂ in Hg.
   rewrite Hk₁ in Hg₁.
   rewrite Zposnat2Znat in Hg₁; [ idtac | assumption ].
   rewrite div_Zdiv in Hg₁; [ idtac | assumption ].
   rewrite positive_nat_Z in Hg₁.
   rewrite Z2Nat.id in Hg₁; [ idtac | assumption ].
   rewrite Hg in Hg₁; subst g₁.
   rewrite normalised_series_null_coeff_range_length.
    constructor; simpl.
     do 2 rewrite Z.add_0_r.
     unfold gcd_nz; simpl.
     do 2 rewrite Z.add_0_r.
     do 2 rewrite Z.div_1_r.
     rewrite normalise_series_0_1.
     rewrite Z2Pos.id; [ idtac | assumption ].
     reflexivity.

     unfold gcd_nz; simpl.
     do 2 rewrite Z.add_0_r.
     do 2 rewrite Z.div_1_r.
     rewrite normalise_series_0_1.
     rewrite Z2Pos.id; [ idtac | assumption ].
     reflexivity.

     constructor; intros i.
     rewrite normalise_series_0_1 in |- * at 1.
     unfold gcd_nz; simpl.
     rewrite normalise_series_0_1.
     do 2 rewrite Z.div_1_r.
     rewrite Pos2Z.id.
     reflexivity.

    rewrite Hs.
    apply normalised_series_null_coeff_range_length; assumption.

   unfold normalise_nz in Hps.
   rewrite Hn in Hps.
   discriminate Hps.

  rename Hn into Hm.
  unfold normalise_nz in Hps.
  remember (null_coeff_range_length fld (nz_terms nz) 0) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ]; [ idtac | reflexivity ].
  constructor; simpl.
  injection Hps; clear Hps; intros; subst nz'; simpl.
  simpl in Hm.
  remember (greatest_series_x_power fld (nz_terms nz) n) as k eqn:Hk .
  remember (gcd_nz n k nz) as g eqn:Hg .
  symmetry in Hg.
  constructor; intros i.
  apply null_coeff_range_length_iff in Hm.
  simpl in Hm.
  rewrite Hm.
  unfold series_nth_fld; simpl.
  destruct (Nbar.lt_dec (fin i) 0); reflexivity.

 rewrite Hps; reflexivity.
Qed.

Lemma normalise_is_projection : ∀ ps,
  normalise_ps (normalise_ps ps) ≈ normalise_ps ps.
Proof.
intros ps.
destruct ps as [nz| ]; [ simpl | reflexivity ].
apply normalise_nz_is_projection.
Qed.
*)

(* cf nz_adjust_eq, normalised_nz_norm_add_compat_r,
      eq_nz_add_add₂, eq_nz_norm_add_add₂ *)
Lemma nz_norm_add_compat_r : ∀ nz₁ nz₂ nz₃,
  normalise_nz fld nz₁ ≐ normalise_nz fld nz₂
  → normalise_nz fld (nz₁ ∔ nz₃) ≐ normalise_nz fld (nz₂ ∔ nz₃).
Proof.
intros nz₁ nz₂ nz₃ Heq.
(* truc à essayer :
rewrite eq_nz_norm_add_add₂.
rewrite eq_nz_norm_add_add₂.
unfold nz_add₂.
*)
(* truc à essayer aussi :
rewrite nz_adjust_eq.
symmetry.
rewrite nz_adjust_eq.
rewrite nz_adjust_eq in Heq.
symmetry in Heq.
rewrite nz_adjust_eq in Heq.
*)
remember (nz₁ ∔ nz₃) as nz₁₃ eqn:Hnz₁₃ .
remember (nz₂ ∔ nz₃) as nz₂₃ eqn:Hnz₂₃ .
unfold normalise_nz; simpl.
remember (null_coeff_range_length fld (nz_terms nz₁₃) 0) as n₁₃ eqn:Hn₁₃ .
remember (null_coeff_range_length fld (nz_terms nz₂₃) 0) as n₂₃ eqn:Hn₂₃ .
symmetry in Hn₁₃, Hn₂₃.
destruct n₁₃ as [n₁₃| ]; simpl.
 destruct n₂₃ as [n₂₃| ]; simpl.
  constructor; simpl.
   Focus 1.
   remember (greatest_series_x_power fld (nz_terms nz₁₃) n₁₃) as k₁₃ eqn:Hk₁₃ .
   remember (greatest_series_x_power fld (nz_terms nz₂₃) n₂₃) as k₂₃ eqn:Hk₂₃ .
   remember (gcd_nz n₁₃ k₁₃ nz₁₃) as g₁₃ eqn:Hg₁₃ .
   remember (gcd_nz n₂₃ k₂₃ nz₂₃) as g₂₃ eqn:Hg₂₃ .
bbb.

intros nz₁ nz₂ nz₃ Heq.
unfold normalise_nz; simpl.
remember (null_coeff_range_length fld (nz_terms_add fld nz₁ nz₃) 0) as n₁₃
 eqn:Hn₁₃ .
remember (null_coeff_range_length fld (nz_terms_add fld nz₂ nz₃) 0) as n₂₃
 eqn:Hn₂₃ .
symmetry in Hn₁₃, Hn₂₃.
apply null_coeff_range_length_iff in Hn₁₃.
unfold null_coeff_range_length_prop in Hn₁₃.
apply null_coeff_range_length_iff in Hn₂₃.
unfold null_coeff_range_length_prop in Hn₂₃.
simpl in Hn₁₃, Hn₂₃.
destruct n₁₃ as [n₁₃| ]; simpl.
 destruct n₂₃ as [n₂₃| ]; simpl.
  constructor; simpl.
   unfold normalise_nz in Heq; simpl in Heq.
   remember (null_coeff_range_length fld (nz_terms nz₁) 0) as n₁ eqn:Hn₁ .
   remember (null_coeff_range_length fld (nz_terms nz₂) 0) as n₂ eqn:Hn₂ .
   symmetry in Hn₁, Hn₂.
   apply null_coeff_range_length_iff in Hn₁.
   apply null_coeff_range_length_iff in Hn₂.
   unfold null_coeff_range_length_prop in Hn₁, Hn₂.
   simpl in Hn₁, Hn₂.
   destruct n₁ as [n₁| ]; simpl.
    destruct n₂ as [n₂| ]; simpl.
     inversion_clear Heq; simpl in *.
     unfold nz_valnum_add.
     unfold cm_factor.
     Focus 1.
bbb.

intros nz₁ nz₂ nz₃ Heq.
unfold normalise_nz in Heq; simpl in Heq.
remember (null_coeff_range_length fld (nz_terms nz₁) 0) as n₁ eqn:Hn₁ .
remember (null_coeff_range_length fld (nz_terms nz₂) 0) as n₂ eqn:Hn₂ .
symmetry in Hn₁, Hn₂.
destruct n₁ as [n₁| ].
 destruct n₂ as [n₂| ].
  inversion_clear Heq; simpl in *.
  remember (greatest_series_x_power fld (nz_terms nz₁) n₁) as k₁ eqn:Hk₁ .
  remember (greatest_series_x_power fld (nz_terms nz₂) n₂) as k₂ eqn:Hk₂ .
  symmetry in Hk₁, Hk₂.
  apply greatest_series_x_power_iff in Hk₁.
  apply greatest_series_x_power_iff in Hk₂.
  remember (null_coeff_range_length fld (nz_terms nz₁) (S n₁)) as sn₁ eqn:Hsn₁ .
  remember (null_coeff_range_length fld (nz_terms nz₂) (S n₂)) as sn₂ eqn:Hsn₂ .
  symmetry in Hsn₁, Hsn₂.
  destruct sn₁ as [sn₁| ].
   destruct sn₂ as [sn₂| ].
    destruct Hk₁ as [Hk₁| Hk₁].
     destruct Hk₂ as [Hk₂| Hk₂].
      unfold normalise_nz.
      remember (null_coeff_range_length fld (nz_terms (nz₁ ∔ nz₃)) 0) as n₁₃ eqn:Hn₁₃ .
      remember (null_coeff_range_length fld (nz_terms (nz₂ ∔ nz₃)) 0) as n₂₃ eqn:Hn₂₃ .
      symmetry in Hn₁₃, Hn₂₃.
      simpl in Hn₁₃, Hn₂₃ |- *.
      destruct n₁₃ as [n₁₃| ].
       destruct n₂₃ as [n₂₃| ].
        constructor; simpl.
         unfold cm_factor.
Focus 1.
bbb.
  destruct Hk₁ as (Hk₁, (Hik₁, Hlt₁)).
  destruct Hk₂ as (Hk₂, (Hik₂, Hlt₂)).
    destruct k₁₃ as [k₁₃| ].
     apply greatest_series_x_power_iff in Hk₁₃.
     rewrite Hn₁₃ in Hk₁₃.
     destruct Hk₁₃ as (Hk, _).
     exfalso; apply Hk; reflexivity.

     destruct k₂₃ as [k₂₃| ].
      apply greatest_series_x_power_iff in Hk₂₃.
      rewrite Hn₂₃ in Hk₂₃.
      destruct Hk₂₃ as (Hk, _).
      exfalso; apply Hk; reflexivity.

      constructor; [ simpl | simpl | idtac ].
       unfold cm_factor.
    Focus 1.
bbb.
  destruct k₁ as [| k₁]; [ discriminate Hk₁ | idtac ].
  destruct k₂ as [| k₂]; [ discriminate Hk₂ | idtac ].
  unfold normalise_nz; simpl.
  remember (null_coeff_range_length fld (nz_terms_add nz₁ nz₃)) as n₁₃ eqn:Hn₁₃ .
  remember (null_coeff_range_length fld (nz_terms_add nz₂ nz₃)) as n₂₃ eqn:Hn₂₃ .
  symmetry in Hn₁₃, Hn₂₃.
  destruct n₁₃ as [n₁₃| ].
    destruct n₂₃ as [n₂₃| ].
    constructor; simpl.
     Focus 1.
     unfold cm_factor; simpl.
     remember (greatest_series_x_power fld (nz_terms_add nz₁ nz₃)) as k₁₃.
     remember (greatest_series_x_power fld (nz_terms_add nz₂ nz₃)) as k₂₃.
     rename Heqk₁₃ into Hk₁₃.
     rename Heqk₂₃ into Hk₂₃.
     symmetry in Hk₁₃, Hk₂₃.
     apply greatest_series_x_power_iff in Hk₁₃.
     apply greatest_series_x_power_iff in Hk₂₃.
     rewrite Hn₁₃ in Hk₁₃.
     rewrite Hn₂₃ in Hk₂₃.
     destruct k₁₃ as [| k₁₃]; [ discriminate Hk₁₃ | idtac ].
     destruct k₂₃ as [| k₂₃]; [ discriminate Hk₂₃ | idtac ].
bbb.
*)
(*
     assert (nz₃ = nz_zero).
      Focus 2.
      subst nz₃; simpl.
      rewrite nz_add_0_r in Hn₁₃.
      rewrite nz_add_0_r in Hn₂₃.
      rewrite null_coeff_range_length_shift in Hn₁₃.
      rewrite null_coeff_range_length_shift in Hn₂₃.
      do 2 rewrite Z.mul_1_r.
      rewrite Hn₁ in Hn₁₃.
      rewrite Hn₂ in Hn₂₃.
      simpl in Hn₁₃, Hn₂₃.
      injection Hn₁₃; clear Hn₁₃; intros Hn₁₃.
      injection Hn₂₃; clear Hn₂₃; intros Hn₂₃.
      rewrite <- Hn₁₃, <- Hn₂₃.
      do 2 rewrite Nat2Z.inj_add.
      do 2 rewrite Z2Nat_id_max.
*)

Lemma ps_add_compat_r : ∀ ps₁ ps₂ ps₃,
  ps₁ ≈ ps₂
  → ps_add ps₁ ps₃ ≈ ps_add ps₂ ps₃.
Proof.
intros ps₁ ps₂ ps₃ H₁₂.
unfold ps_add.
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ].
  destruct ps₃ as [nz₃| ].
   constructor.
   inversion_clear H₁₂.
bbb.

intros ps₁ ps₂ ps₃ H₂₃.
unfold ps_add.
inversion H₂₃ as [k₂₁ k₂₂ nz₂₁ nz₂₂ Hss₂ Hvv₂ Hck₂| a b H₂ H₃]; subst.
 remember (nz_valnum ps₁) as v₁.
 remember (nz_valnum ps₂) as v₂.
 remember (nz_valnum ps₃) as v₃.
 symmetry in Heqv₁, Heqv₂, Heqv₃.
 destruct v₁ as [v₁| ]; [ idtac | assumption ].
 destruct v₂ as [v₂| ].
  destruct v₃ as [v₃| ]; [ idtac | discriminate Hvv₂ ].
  unfold ps_add_nz, cm_factor; simpl.
  rewrite Heqv₁, Heqv₂, Heqv₃; simpl.
  constructor 1 with (k₁ := k₂₁) (k₂ := k₂₂); unfold cm_factor; simpl.
   do 2 rewrite series_stretch_add_distr.
   do 4 rewrite stretch_shift_series_distr.
   do 4 rewrite <- stretch_series_stretch.
   do 4 rewrite Nat.mul_sub_distr_r.
   do 4 rewrite <- Z2Nat_inj_mul_pos_r.
   do 4 rewrite <- Z.mul_assoc; simpl.
   rewrite Hck₂.
   rewrite Pos.mul_comm in Hck₂; symmetry in Hck₂.
   rewrite Pos.mul_comm in Hck₂; symmetry in Hck₂.
   rewrite Hck₂.
   replace (k₂₁ * nz_comden ps₁)%positive with
    (nz_comden ps₁ * k₂₁)%positive by apply Pos.mul_comm.
   do 2 rewrite stretch_series_stretch.
   rewrite Hss₂.
   do 2 rewrite <- stretch_series_stretch.
   replace (nz_comden ps₁ * k₂₂)%positive with
    (k₂₂ * nz_comden ps₁)%positive by apply Pos.mul_comm.
   replace (v₂ * ' (nz_comden ps₁ * k₂₁))%Z with
    (v₃ * ' (k₂₂ * nz_comden ps₁))%Z .
    reflexivity.

    do 2 rewrite Pos2Z.inj_mul.
    do 2 rewrite Z.mul_assoc.
    symmetry; rewrite Z.mul_shuffle0.
    apply Z.mul_cancel_r; [ apply Pos2Z_ne_0 | idtac ].
    inversion Hvv₂; subst.
    reflexivity.

   rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
   rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
   simpl in Hvv₂.
   do 2 f_equal.
    do 2 rewrite <- Z.mul_assoc; simpl.
    rewrite Hck₂; reflexivity.

    rewrite Z.mul_shuffle0.
    injection Hvv₂; clear Hvv₂; intros Hvv₂; rewrite Hvv₂.
    rewrite Z.mul_shuffle0; reflexivity.

   rewrite <- Pos.mul_assoc, Hck₂, Pos.mul_assoc.
   reflexivity.

  destruct v₃ as [v₃| ]; [ discriminate Hvv₂ | reflexivity ].

 remember (nz_valnum ps₁) as v₁.
 remember (nz_valnum ps₂) as v₂.
 remember (nz_valnum ps₃) as v₃.
 symmetry in Heqv₁, Heqv₂, Heqv₃.
 destruct v₁ as [v₁| ]; [ idtac | assumption ].
 destruct v₂ as [v₂| ]; simpl.
  destruct H₂ as [H₂| H₂]; [ idtac | discriminate H₂ ].
  destruct v₃ as [v₃| ]; simpl.
   destruct H₃ as [H₃| H₃]; [ idtac | discriminate H₃ ].
   unfold build_ps; simpl.
   rewrite Heqv₁, Heqv₂, Heqv₃; simpl.
   Focus 1.
bbb.

intros ps₁ ps₃ ps₄ H.
inversion H as [k₂₁ k₂₂ nz₂₁ nz₂₂ Hss₂ Hvv₂ Hck₂| ]; subst.
 constructor 1 with (k₁ := k₂₁) (k₂ := k₂₂); unfold cm_factor; simpl.
  do 4 rewrite Z2Nat_inj_mul_pos_r.
  remember (nz_valnum nz₁) as v₁.
  remember (nz_comden nz₁) as c₁.
  remember (nz_comden nz₂₁) as c₂₁.
  remember (nz_comden nz₂₂) as c₂₂.
  remember (nz_valnum nz₂₁) as v₂₁.
  remember (nz_valnum nz₂₂) as v₂₂.
  do 2 rewrite series_stretch_add_distr.
  rewrite stretch_shift_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite stretch_shift_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite stretch_shift_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite stretch_shift_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite <- stretch_series_stretch; try apply Pos2Nat_ne_0.
  rewrite <- stretch_series_stretch; try apply Pos2Nat_ne_0.
  rewrite <- stretch_series_stretch; try apply Pos2Nat_ne_0.
  rewrite <- stretch_series_stretch; try apply Pos2Nat_ne_0.
-- à nettoyer
  rewrite Nat.mul_sub_distr_r.
  rewrite <- Nat.mul_assoc.
  rewrite <- Pos2Nat.inj_mul.
  rewrite Hck₂.
  rewrite Nat.mul_shuffle0.
  rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite Hvv₂.
  rewrite Pos2Z.inj_mul.
  rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite Z.mul_assoc.
  remember (v₁ * ' c₂₂ * ' k₂₂)%Z as vck eqn:Hvck .
  remember (v₂₂ * ' k₂₂ * ' c₁)%Z as vkc eqn:Hvkc .
  rewrite Nat.mul_sub_distr_r.
  do 4 rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite Z.mul_shuffle0.
  rewrite Hvv₂.
  rewrite <- Hvkc.
  rewrite <- Z.mul_assoc; simpl.
  rewrite Hck₂.
  rewrite Pos2Z.inj_mul.
  rewrite Z.mul_assoc.
  rewrite <- Hvck.
  do 2 rewrite Nat.mul_sub_distr_r.
  do 4 rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite <- Hvck.
  rewrite Z.mul_shuffle0.
  rewrite <- Hvkc.
  do 4 rewrite <- Pos2Nat.inj_mul.
  rewrite Pos.mul_comm.
  rewrite Hck₂.
  rewrite Pos.mul_comm.
  rewrite series_add_comm.
  rewrite Pos2Nat.inj_mul.
  rewrite Nat.mul_comm.
  rewrite stretch_series_stretch; try apply Pos2Nat_ne_0.
  rewrite Hss₂.
  rewrite <- stretch_series_stretch; try apply Pos2Nat_ne_0.
  rewrite Nat.mul_comm.
  rewrite <- Pos2Nat.inj_mul.
  rewrite series_add_comm.
  reflexivity.

  rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
  rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
  rewrite <- Z.mul_assoc; simpl.
  rewrite Hck₂.
  rewrite Z.mul_shuffle0, Hvv₂.
  rewrite Pos2Z.inj_mul, Z.mul_assoc.
  rewrite Z.min_comm, Z.mul_shuffle0, Z.min_comm.
  reflexivity.

  do 2 rewrite <- Pos.mul_assoc.
  apply Pos.mul_cancel_l.
  assumption.

 reflexivity.
Qed.
*)

Theorem ps_mul_ident : ∀ ps, ps_mul fld ps_one ps ≈ ps.
Proof.
intros ps.
unfold ps_mul; simpl.
destruct ps as [nz| ]; [ idtac | reflexivity ].
unfold cm_factor; simpl.
rewrite Z.mul_1_r.
apply eq_non_zero_ps with (k₁ := xH) (k₂ := xH); try reflexivity; simpl.
rewrite series_stretch_1.
rewrite series_stretch_1 in |- * at 2.
apply eq_series_base; simpl.
bbb.
 intros i.
 destruct i; simpl.
  unfold series_nth; simpl.
  rewrite Nat.add_0_r.
  destruct (lt_dec 0 (Pos.to_nat (nz_comden nz))) as [H| H].
   rewrite Nbar.mul_1_r.
   remember (stop (nz_terms nz)) as st.
   destruct st as [st| ]; simpl.
    destruct (lt_dec 0 st) as [H₁| H₁].
     rewrite Nat.mod_0_l; simpl.
      rewrite fld_mul_ident; reflexivity.

      apply Pos2Nat_ne_0.

     apply not_gt in H₁.
     apply Nat.le_0_r in H₁.
     subst st.
Focus 1.
bbb.

intros ps.
unfold ps_mul; simpl.
destruct ps as [nz| ]; [ idtac | reflexivity ].
unfold cm_factor; simpl.
rewrite Z.mul_1_r.
constructor 1 with (k₁ := xH) (k₂ := xH); try reflexivity; simpl.
rewrite series_stretch_1.
rewrite series_stretch_1 in |- * at 2.
constructor; simpl.
 intros i.
 remember
  (sum_mul_coeff fld 1 i
     (series_stretch fld (Pos.to_nat (nz_comden nz))
        {| terms := λ _ : nat, one fld; stop := 1 |})
     (series_stretch fld (Pos.to_nat 1) (nz_terms nz))) as x.
 symmetry in Heqx.
 destruct x as [x| ].
  unfold series_nth; simpl.
  rewrite Nat.add_0_r.
  destruct (lt_dec 0 (Pos.to_nat (nz_comden nz))) as [| Bad].
   rewrite Nbar.mul_1_r.
   remember (stop (nz_terms nz)) as st.
   symmetry in Heqst.
   destruct st as [st| ].
    destruct (lt_dec i st) as [H| H].
     rewrite Nat.mod_0_l; [ simpl | apply Pos2Nat_ne_0 ].
     rewrite divmod_div.
     rewrite Nat.div_1_r.
     rewrite fld_mul_ident.
bbb.

Definition ps_fld : field (puiseux_series α) :=
  {| zero := ps_zero;
     one := ps_one;
     add := ps_add fld;
     mul := ps_mul fld;
     fld_eq := eq_ps fld;
     fld_eq_refl := eq_ps_refl fld;
     fld_eq_sym := eq_ps_sym (fld := fld);
     fld_eq_trans := eq_ps_trans (fld := fld);
     fld_add_comm := ps_add_comm;
     fld_add_assoc := ps_add_assoc;
     fld_add_0_l := ps_add_ident;
     fld_add_compat := ps_add_compat;
     fld_mul_ident := ps_mul_ident |}.

End fld₄.
