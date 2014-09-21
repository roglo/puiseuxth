(* RootWhenR1.v *)

Require Import Utf8 QArith NPeano Sorting.

Require Import Misc.
Require Import SlopeMisc.
Require Import Slope_base.
Require Import Qbar.
Require Import Nbar.
Require Import Field.
Require Import Fpolynomial.
Require Import Fsummation.
Require Import Newton.
Require Import ConvexHullMisc.
Require Import ConvexHull.
Require Import PolyConvexHull.
Require Import NotInSegment.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_mul.
Require Import Ps_div.
Require Import PSpolynomial.
Require Import Puiseux_base.
Require Import AlgCloCharPol.
Require Import CharactPolyn.
Require Import F1Eq.
Require Import PosOrder.
Require Import F1Prop.
Require Import InK1m.
Require Import Q_field.
Require Import RootHeadTail.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Theorem eq_Qbar_eq : ∀ a b, a = b → (a = b)%Qbar.
Proof. intros a b Hab; subst a; reflexivity. Qed.

Theorem eq_Qbar_qinf : ∀ a, (a = ∞)%Qbar → a = ∞%Qbar.
Proof. intros a H; destruct a; auto; inversion H. Qed.

Theorem root_head_from_cγ_list_succ_r : ∀ pol ns pol₁ ns₁ c n i,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → zerop_1st_n_const_coeff n pol₁ ns₁ = false
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → (root_head_from_cγ_list pol ns 0 n (S i) =
      ps_monom 1%K (γ ns) * root_head_from_cγ_list pol₁ ns₁ 0 n i)%ps.
Proof.
intros pol ns pol₁ ns₁ c n i Hc Hpol₁ Hns₁ Hnz Hnz₁.
revert pol ns pol₁ ns₁ c i Hc Hpol₁ Hns₁ Hnz Hnz₁.
induction n; intros.
 simpl.
 unfold γ_sum; simpl.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite summation_shift; [ idtac | fast_omega  ].
 rewrite Nat_sub_succ_1.
 do 2 rewrite rng_add_0_r.
 simpl.
 rewrite <- Hc, <- Hpol₁, <- Hns₁.
 rewrite rng_add_comm.
 rewrite ps_monom_add_r.
 apply ps_mul_comm.

 simpl in Hnz.
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hnz.

  remember (S i) as si; simpl.
  rewrite <- Hc, <- Hpol₁, <- Hns₁.
  subst si; simpl.
  rewrite <- Hc, <- Hpol₁, <- Hns₁.
  remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
  remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
  remember (List.hd phony_ns (newton_segments pol₂)) as ns₂.
  unfold γ_sum; simpl.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite summation_shift; [ idtac | fast_omega  ].
  rewrite Nat_sub_succ_1.
  destruct (ps_zerop R (ps_poly_nth 0 (nth_pol i pol₂ ns₂))) as [H₂| H₂].
   do 2 rewrite rng_add_0_r.
   rewrite rng_add_comm.
   rewrite ps_monom_add_r.
   simpl.
   rewrite <- Hc, <- Hpol₁, <- Hns₁.
   apply ps_mul_comm.

   simpl.
   rewrite <- Hc, <- Hpol₁, <- Hns₁.
   rewrite ps_mul_add_distr_l.
   apply rng_add_compat.
    rewrite rng_add_comm; simpl.
    rewrite ps_monom_add_r.
    apply ps_mul_comm.

    apply IHn with (c := c); auto.
    rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
    apply zerop_1st_n_const_coeff_false_iff.
    clear i H₂.
    intros i Hin.
    destruct i; [ assumption | simpl ].
    rewrite <- Hc₁, <- Hpol₂, <- Heqns₂.
    apply Hnz.
    fast_omega Hin.
Qed.

Theorem apply_nth_pol : ∀ pol ns y n,
  let qr := Q_ring in
  zerop_1st_n_const_coeff n pol ns = false
  → (ps_pol_apply pol
       (root_head 0 n pol ns + ps_monom 1%K (γ_sum 0 n pol ns) * y) =
     ps_monom 1%K (Σ (i = 0, n), β (nth_ns i pol ns)) *
     ps_pol_apply (nth_pol (S n) pol ns) y)%ps.
Proof.
intros; revert H; intros Hnz.
revert pol ns y Hnz.
induction n; intros.
 unfold root_head; simpl.
 unfold γ_sum, summation; simpl.
 unfold next_pol; simpl.
 unfold ps_pol_apply; simpl.
 unfold apply_poly; simpl.
 unfold next_lap; simpl.
 remember (ac_root (Φq pol ns)) as c eqn:Hc .
 rewrite apply_lap_mul; simpl.
 rewrite rng_mul_0_l, rng_add_0_l.
 symmetry; rewrite rng_add_0_r; symmetry.
 rewrite rng_mul_assoc; simpl.
 rewrite <- ps_monom_add_r.
 rewrite rng_add_opp_r; simpl.
 rewrite ps_mul_1_l.
 rewrite apply_lap_compose; simpl.
 rewrite rng_mul_0_l, rng_add_0_l.
 simpl in Hnz.
 destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
  discriminate Hnz.

  do 2 rewrite rng_add_0_r.
  rewrite rng_add_comm; reflexivity.

 simpl in Hnz.
 destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
  discriminate Hnz.

  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite summation_shift; [ idtac | fast_omega  ].
  rewrite Nat_sub_succ_1.
  remember (S n) as sn in |- *; simpl.
  remember (ac_root (Φq pol ns)) as c eqn:Hc .
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  rewrite ps_monom_add_r.
  rewrite <- rng_mul_assoc.
  subst sn; simpl.
  erewrite nth_pol_n with (pol := pol₁) (ns := ns₁); eauto .
  erewrite <- nth_pol_succ; eauto ; [ idtac | erewrite nth_c_n; eauto  ].
  remember (S n) as sn in |- *; simpl.
  unfold root_head; simpl.
  destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₂| H₂].
   contradiction.

   clear H₂.
   rewrite Heqsn in |- * at 1; simpl.
   rewrite <- Hc, <- Hpol₁.
   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
    rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
    pose proof (Hnz O (Nat.le_0_l n)) as H; contradiction.

    subst sn.
    rewrite <- IHn; auto.
    unfold root_head; simpl.
    destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₃| H₃].
     contradiction.

     clear H₃.
     unfold γ_sum at 1, summation; simpl.
     rewrite rng_add_0_r.
     unfold γ_sum.
     rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
     rewrite summation_shift; [ idtac | fast_omega  ].
     rewrite Nat_sub_succ_1; simpl.
     rewrite <- Hc, <- Hpol₁, <- Hns₁.
     rewrite ps_monom_add_r.
     remember Σ (i = 0, n), nth_γ i pol₁ ns₁ as sγ eqn:Hsγ .
     rewrite <- ps_mul_assoc.
     remember (ps_monom 1%K sγ * y)%ps as u eqn:Hu .
     rewrite Hpol₁ in |- * at 1; simpl.
     unfold next_pol; simpl.
     unfold ps_pol_apply; simpl.
     unfold apply_poly; simpl.
     unfold next_lap; simpl.
     rewrite apply_lap_mul; simpl.
     rewrite rng_mul_0_l, rng_add_0_l.
     rewrite rng_mul_assoc; simpl.
     rewrite <- ps_monom_add_r.
     rewrite rng_add_opp_r; simpl.
     rewrite ps_mul_1_l.
     rewrite apply_lap_compose; simpl.
     rewrite rng_mul_0_l, rng_add_0_l.
     symmetry; rewrite ps_add_comm; symmetry.
     rewrite ps_mul_add_distr_l.
     rewrite ps_add_assoc.
     rewrite root_head_from_cγ_list_succ_r; eauto .
     reflexivity.
Qed.

Theorem Qnat_succ : ∀ n x, x * Qnat (S n) == x * Qnat n + x.
Proof.
intros n x.
unfold Qnat.
setoid_replace x with (x * 1) at 3.
 rewrite <- rng_mul_add_distr_l.
 apply rng_mul_compat_l; simpl.
 unfold Qeq; simpl.
 do 2 rewrite Z.mul_1_r.
 rewrite Pos.mul_1_r, Z.add_1_r.
 apply Zpos_P_of_succ_nat.

 rewrite rng_mul_1_r; reflexivity.
Qed.

Theorem summation_all_lt : ∀ f n x,
  let qr := Q_ring in
  (∀ i : nat, i ≤ n → x < f i)
  → x * Qnat (S n) < Σ (i = 0, n), f i.
Proof.
intros f n x qr Hi.
induction n.
 unfold Qnat, summation; simpl.
 rewrite rng_add_0_r.
 rewrite rng_mul_1_r.
 apply Hi; reflexivity.

 rewrite summation_split_last; [ simpl | apply Nat.le_0_l ].
 rewrite Qnat_succ.
 apply Qplus_lt_le_compat.
  apply IHn.
  intros i Hin; apply Hi.
  fast_omega Hin.

  apply Qlt_le_weak.
  apply Hi; reflexivity.
Qed.

Theorem order_pol_apply_nonneg : ∀ pol y,
  (∀ a, a ∈ al pol → (0 ≤ order a)%Qbar)
  → (0 ≤ order y)%Qbar
  → (0 ≤ order (ps_pol_apply pol y))%Qbar.
Proof.
intros pol y Ha Hy.
unfold ps_pol_apply, apply_poly.
remember (al pol) as la; clear Heqla.
induction la as [| a]; intros; simpl.
 rewrite order_0; constructor.

 eapply Qbar.le_trans; [ idtac | apply order_add ].
 rewrite order_mul; auto.
 apply Qbar.min_glb.
  eapply Qbar.le_trans; eauto .
  rewrite Qbar.add_comm.
  apply Qbar.le_sub_le_add_l.
  rewrite Qbar.sub_diag.
  apply IHla.
  intros b Hb.
  apply Ha; right; assumption.

  apply Ha; left; reflexivity.
Qed.

Theorem eq_1_0_ps_0 : (1 = 0)%K → ∀ a, (a = 0)%ps.
Proof.
intros H a.
apply order_inf.
unfold order.
remember (series_order R (ps_terms a) 0) as v eqn:Hv .
symmetry in Hv.
destruct v as [v| ]; auto.
apply series_order_iff in Hv.
unfold series_order_prop in Hv.
destruct Hv as (_, Hv).
exfalso; apply Hv; simpl.
apply eq_1_0_all_0; assumption.
Qed.

Theorem lowest_zerop_1st_n_const_coeff : ∀ pol ns n,
  zerop_1st_n_const_coeff n pol ns = true
  → ∃ i,
    i ≤ n ∧
    (i = O ∨ zerop_1st_n_const_coeff (pred i) pol ns = false) ∧
    zerop_1st_n_const_coeff i pol ns = true.
Proof.
intros pol ns n Hz.
revert pol ns Hz.
induction n; intros.
 exists O.
 split; [ reflexivity | idtac ].
 split; [ left; reflexivity | assumption ].

 simpl in Hz.
 destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
  exists O.
  split; [ apply Nat.le_0_l | idtac ].
  split; [ left; reflexivity | simpl ].
  destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.

  apply IHn in Hz.
  destruct Hz as (i, (Hin, (Hji, Hz))).
  destruct Hji as [Hji| Hji].
   subst i.
   simpl in Hz.
   remember (ac_root (Φq pol ns)) as c eqn:Hc .
   remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
    exists 1%nat.
    split; [ fast_omega  | simpl ].
    destruct (ps_zerop R (ps_poly_nth 0 pol)); [ contradiction | idtac ].
    split; [ right; reflexivity | idtac ].
    rewrite <- Hc, <- Hpol₁.
    destruct (ps_zerop R (ps_poly_nth 0 pol₁)); auto.

    discriminate Hz.

   destruct i.
    simpl in Hji, Hz.
    rewrite Hji in Hz.
    discriminate Hz.

    simpl in Hji.
    exists (S (S i)).
    split; [ fast_omega Hin | idtac ].
    split.
     right; simpl.
     destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
     contradiction.

     remember (S i) as si; simpl; subst si.
     destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
Qed.

Theorem first_null_coeff : ∀ pol₁ ns₁ i a₁ la₁,
  zerop_1st_n_const_coeff i pol₁ ns₁ = false
  → zerop_1st_n_const_coeff (S i) pol₁ ns₁ = true
  → al (nth_pol (S i) pol₁ ns₁) = [a₁ … la₁]
  → (a₁ = 0)%ps.
Proof.
intros pol₁ ns₁ i a₁ la₁ Hnz₁ Hz₁ Hla₁.
revert pol₁ ns₁ a₁ la₁ Hnz₁ Hz₁ Hla₁.
induction i; intros.
 simpl in Hnz₁, Hz₁, Hla₁.
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hnz₁.

  remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
  remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
  remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
  destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [H₂| H₂].
   unfold ps_poly_nth, ps_lap_nth in H₂; simpl in H₂.
   unfold next_pol in Hpol₂.
   rewrite Hla₁ in Hpol₂.
   rewrite Hpol₂ in H₂; simpl in H₂.
   assumption.

   discriminate Hz₁.

 remember (S i) as si; simpl in Hz₁, Hla₁; subst si.
 simpl in Hnz₁.
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hnz₁.

  remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
  remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
  remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
  eapply IHi; eauto .
Qed.

Theorem List_In_nth : ∀ α a la (d : α),
  a ∈ la
  → ∃ n, a = List.nth n la d.
Proof.
intros u a la d Ha.
revert a Ha.
induction la as [| b]; intros; [ contradiction | idtac ].
simpl in Ha.
destruct Ha as [Ha| Ha].
 subst b.
 exists O; reflexivity.

 apply IHla in Ha.
 destruct Ha as (n, Ha).
 exists (S n); simpl.
 assumption.
Qed.

Theorem a₀_0_root_0 : ∀ pol,
  (ps_poly_nth 0 pol = 0)%ps
  → (ps_pol_apply pol 0 = 0)%ps.
Proof.
intros pol H.
unfold ps_pol_apply, apply_poly, apply_lap; simpl.
unfold ps_poly_nth in H.
destruct (al pol) as [| a la]; [ reflexivity | simpl ].
unfold ps_lap_nth in H; simpl in H.
rewrite rng_mul_0_r, rng_add_0_l; assumption.
Qed.

Theorem root_when_fin : ∀ pol ns n,
  zerop_1st_n_const_coeff (pred n) pol ns = false
  → zerop_1st_n_const_coeff n pol ns = true
  → ∃ s, (ps_pol_apply pol s = 0)%ps.
Proof.
intros pol ns n Hnz Hz.
exists (root_head 0 (pred n) pol ns).
destruct n.
 rewrite Nat.pred_0 in Hnz.
 rewrite Hnz in Hz; discriminate Hz.

 rewrite Nat.pred_succ in Hnz.
 rewrite Nat.pred_succ.
 remember Hnz as H; clear HeqH.
 eapply apply_nth_pol with (y := 0%ps) in H.
 rewrite rng_mul_0_r, rng_add_0_r in H; rewrite H.
 unfold ps_pol_apply, apply_poly.
 remember (S n) as sn.
 unfold apply_lap; simpl.
 remember (al (nth_pol sn pol ns)) as la eqn:Hla .
 symmetry in Hla.
 destruct la as [| a]; simpl.
  rewrite rng_mul_0_r; reflexivity.

  rewrite rng_mul_0_r, rng_add_0_l; subst sn.
  rewrite first_null_coeff with (a₁ := a); eauto .
  rewrite rng_mul_0_r; reflexivity.
Qed.

Theorem no_newton_segments : ∀ pol,
  (ps_poly_nth 0 pol ≠ 0)%ps
  → newton_segments pol = []
  → (∀ i, (0 < i)%nat → (ps_poly_nth i pol = 0)%ps).
Proof.
(* perhaps simplifiable *)
intros pol Hnz Hns i Hi.
destruct i; [ exfalso; revert Hi; apply Nat.lt_irrefl | idtac ].
clear Hi.
unfold newton_segments in Hns.
unfold lower_convex_hull_points in Hns.
unfold points_of_ps_polynom in Hns.
unfold points_of_ps_lap in Hns.
remember (al pol) as la eqn:Hla .
symmetry in Hla.
unfold ps_poly_nth.
unfold ps_poly_nth in Hnz.
rewrite Hla in Hnz; rewrite Hla.
clear pol Hla.
unfold points_of_ps_lap_gen in Hns.
unfold qpower_list in Hns.
remember (pair_rec (λ pow ps, (Qnat pow, ps))) as f.
unfold ps_lap_nth in Hnz.
unfold ps_lap_nth.
revert la Hnz Hns.
induction i; intros.
 destruct la as [| a].
  exfalso; apply Hnz; reflexivity.

  simpl in Hnz; simpl.
  simpl in Hns.
  remember (f (O, a)) as fa.
  rewrite Heqf in Heqfa.
  simpl in Heqfa.
  unfold pair_rec in Heqfa; simpl in Heqfa.
  subst fa; simpl in Hns.
  apply order_fin in Hnz.
  remember (order a) as oa.
  symmetry in Heqoa.
  destruct oa as [oa| ]; [ idtac | exfalso; apply Hnz; reflexivity ].
  simpl in Hns.
  remember (filter_finite_ord R (List.map f (power_list 1 la))) as pts.
  symmetry in Heqpts.
  destruct pts; [ idtac | discriminate Hns ].
  clear Hns Hnz.
  destruct la as [| b]; [ reflexivity | simpl ].
  simpl in Heqpts.
  remember (f (1%nat, b)) as fb.
  rewrite Heqf in Heqfb.
  unfold pair_rec in Heqfb.
  simpl in Heqfb.
  subst fb; simpl in Heqpts.
  remember (order b) as ob.
  symmetry in Heqob.
  destruct ob as [ob| ]; auto.
   discriminate Heqpts.

   apply order_inf; assumption.

 destruct la as [| a]; [ reflexivity | simpl ].
 simpl in Hnz.
 simpl in Hns.
 remember (f (O, a)) as fa.
 rewrite Heqf in Heqfa.
 simpl in Heqfa.
 unfold pair_rec in Heqfa; simpl in Heqfa.
 subst fa; simpl in Hns.
 apply order_fin in Hnz.
 remember (order a) as oa.
 symmetry in Heqoa.
 destruct oa as [oa| ]; [ idtac | exfalso; apply Hnz; reflexivity ].
 simpl in Hns.
 remember (filter_finite_ord R (List.map f (power_list 1 la))) as pts.
 symmetry in Heqpts.
 destruct pts; [ idtac | discriminate Hns ].
 clear Hns.
 clear Hnz.
 revert Heqf Heqpts; clear; intros.
 remember 1%nat as pow; clear Heqpow.
 revert i pow Heqpts.
 induction la as [| a]; intros; [ reflexivity | idtac ].
 simpl in Heqpts.
 remember (f (pow, a)) as fa.
 rewrite Heqf in Heqfa.
 unfold pair_rec in Heqfa.
 simpl in Heqfa.
 subst fa; simpl in Heqpts.
 remember (order a) as oa.
 symmetry in Heqoa.
 destruct oa as [oa| ]; [ discriminate Heqpts | simpl ].
 destruct i.
  destruct la as [| b]; [ reflexivity | simpl ].
  simpl in Heqpts.
  remember (f (S pow, b)) as fb.
  rewrite Heqf in Heqfb.
  unfold pair_rec in Heqfb; simpl in Heqfb.
  subst fb.
  apply order_inf.
  remember (order b) as ob.
  symmetry in Heqob.
  destruct ob as [ob| ]; [ discriminate Heqpts | reflexivity ].

  eapply IHla; eauto .
Qed.

Theorem root_multiplicity_0 : ∀ c cpol,
  c = ac_root cpol
  → root_multiplicity acf c cpol = 0%nat
  → (degree ac_zerop cpol = 0)%nat.
Proof.
intros c cpol Hc Hr.
unfold root_multiplicity in Hr.
unfold degree, apply_poly.
remember (al cpol) as la.
symmetry in Heqla.
destruct la as [| a]; [ reflexivity | simpl ].
simpl in Hr.
unfold lap_mod_deg_1 in Hr; simpl in Hr.
destruct (ac_zerop (apply_lap la c * c + a)%K) as [H₁| H₁].
 discriminate Hr.

 remember (degree ac_zerop cpol) as deg eqn:Hdeg .
 symmetry in Hdeg.
 destruct deg.
  unfold degree in Hdeg.
  rewrite Heqla in Hdeg.
  simpl in Hdeg.
  assumption.

  assert (degree ac_zerop cpol ≥ 1)%nat as H by fast_omega Hdeg.
  clear Hdeg.
  apply ac_prop_root in H.
  rewrite <- Hc in H.
  unfold apply_poly in H.
  rewrite Heqla in H; simpl in H.
  contradiction.
Qed.

Theorem degree_eq_0_if : ∀ cpol,
  degree ac_zerop cpol = O
  → (cpol = POL [])%pol ∨ (∃ a, (a ≠ 0)%K ∧ (cpol = POL [a])%pol).
Proof.
intros cpol Hdeg.
unfold degree in Hdeg.
unfold eq_poly; simpl.
remember (al cpol) as la; clear Heqla.
induction la as [| a]; [ left; reflexivity | idtac ].
simpl in Hdeg.
remember (degree_plus_1_of_list ac_zerop la) as deg eqn:Hdeg₁ .
symmetry in Hdeg₁.
destruct deg.
 clear Hdeg.
 pose proof (IHla (Nat.eq_refl O)) as H.
 clear IHla.
 destruct H as [Hla| Hla].
  rewrite Hla.
  destruct (ac_zerop a) as [H₁| H₁].
   left; rewrite H₁.
   apply lap_eq_0.

   right.
   exists a.
   split; [ assumption | idtac ].
   rewrite Hla; reflexivity.

  clear cpol.
  destruct Hla as (b, (Hb, Hla)).
  rewrite Hla.
  right.
  revert a b Hb Hla.
  induction la as [| c]; intros.
   apply lap_eq_nil_cons_inv in Hla.
   destruct Hla; contradiction.

   simpl in Hdeg₁.
   apply lap_eq_cons_inv in Hla.
   destruct Hla as (Hcb, Hla).
   remember (degree_plus_1_of_list ac_zerop la) as deg eqn:Hdeg .
   symmetry in Hdeg.
   destruct deg.
    destruct (ac_zerop c) as [H₁| H₁]; [ idtac | discriminate Hdeg₁ ].
    rewrite H₁ in Hcb.
    symmetry in Hcb; contradiction.

    discriminate Hdeg₁.

 discriminate Hdeg.
Qed.

Theorem multiplicity_neq_0 : ∀ pol ns c,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) ≠ O.
Proof.
intros pol ns c Hns Hc Hr.
apply root_multiplicity_0 in Hr; eauto .
apply degree_eq_0_if in Hr.
destruct Hr as [Hr| Hr].
 unfold Φq in Hr; simpl in Hr.
 remember Hns as H; clear HeqH.
 apply exists_ini_pt_nat in H.
 destruct H as (j, (αj, Hini)).
 rewrite Hini in Hr.
 simpl in Hr.
 rewrite nat_num_Qnat in Hr.
 unfold eq_poly in Hr.
 simpl in Hr.
 rewrite Nat.sub_diag in Hr.
 rewrite list_pad_0 in Hr.
 apply lap_eq_cons_nil_inv in Hr.
 destruct Hr as (Hoj, Hcpol).
 exfalso; revert Hoj.
 eapply ord_coeff_non_zero_in_newt_segm; eauto .
 left; eassumption.

 destruct Hr as (a, (Ha, Hcpol)).
 unfold Φq in Hcpol; simpl in Hcpol.
 remember Hns as H; clear HeqH.
 apply exists_ini_pt_nat in H.
 destruct H as (j, (αj, Hini)).
 rewrite Hini in Hcpol; simpl in Hcpol.
 rewrite nat_num_Qnat in Hcpol.
 rewrite Nat.sub_diag in Hcpol.
 simpl in Hcpol.
 unfold eq_poly in Hcpol; simpl in Hcpol.
 apply lap_eq_cons_inv in Hcpol.
 destruct Hcpol as (Hoa, Hcpol).
 remember (oth_pts ns) as opts eqn:Hopts .
 symmetry in Hopts.
 destruct opts as [| pt].
  simpl in Hcpol.
  remember Hns as H; clear HeqH.
  apply exists_fin_pt_nat in H.
  destruct H as (k, (αk, Hfin)).
  rewrite Hfin in Hcpol.
  simpl in Hcpol.
  rewrite nat_num_Qnat in Hcpol; simpl in Hcpol.
  remember (k - S j)%nat as kj.
  clear Heqkj.
  induction kj.
   simpl in Hcpol.
   apply lap_eq_cons_nil_inv in Hcpol.
   destruct Hcpol as (Hoc, _).
   exfalso; revert Hoc.
   eapply ord_coeff_non_zero_in_newt_segm; eauto .
   rewrite Hopts; simpl.
   right; left; eassumption.

   simpl in Hcpol.
   apply lap_eq_cons_nil_inv in Hcpol.
   destruct Hcpol as (_, Hcpol).
   apply IHkj in Hcpol.
   assumption.

  simpl in Hcpol.
  remember Hns as H; clear HeqH.
  eapply exists_oth_pt_nat with (pt := pt) in H.
   destruct H as (h, (αh, Hoth)).
   rewrite Hoth in Hcpol; simpl in Hcpol.
   rewrite nat_num_Qnat in Hcpol.
   remember (h - S j)%nat as hj.
   clear Heqhj.
   induction hj.
    simpl in Hcpol.
    apply lap_eq_cons_nil_inv in Hcpol.
    destruct Hcpol as (Hoc, _).
    exfalso; revert Hoc.
    eapply ord_coeff_non_zero_in_newt_segm; eauto .
    right; apply List.in_or_app; left.
    rewrite Hopts; left; eassumption.

    simpl in Hcpol.
    apply lap_eq_cons_nil_inv in Hcpol.
    destruct Hcpol as (_, Hcpol).
    apply IHhj in Hcpol.
    assumption.

   rewrite Hopts; left; reflexivity.
Qed.

End theorems.
