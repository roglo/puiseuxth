(* Puiseux.v *)

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
Require Import RootAnyR.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Definition multiplicity_decreases pol ns n :=
  let c := ac_root (Φq pol ns) in
  let r := root_multiplicity acf c (Φq pol ns) in
  let poln := nth_pol n pol ns in
  let nsn := nth_ns n pol ns in
  let cn := nth_c n pol ns in
  let rn := root_multiplicity acf cn (Φq poln nsn) in
  lt_dec rn r.

Theorem order_root_tail_nonneg_any_r_aux : ∀ pol ns c pol₁ ns₁ m q₀ n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, i ≤ S n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
  → (∀ i, i ≤ S n → nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (0 ≤ order (root_tail (m * q₀) n pol₁ ns₁))%Qbar.
Proof.
intros pol ns c pol₁ ns₁ m q₀ n r Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hpsi Hri H₀.
unfold root_tail.
remember (zerop_1st_n_const_coeff n pol₁ ns₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁; [ rewrite order_0; constructor | idtac ].
revert m q₀ c pol ns pol₁ ns₁ Hns Hc Hm Hq₀ Hpol₁ Hns₁ Hz₁ Hpsi Hri.
induction n; intros.
 simpl.
 unfold order; simpl.
 pose proof (Hpsi 1%nat (Nat.le_refl 1)) as H; simpl in H.
 rewrite <- Hc, <- Hpol₁ in H.
 rename H into Hnz₁; move Hnz₁ before Hns₁.
 pose proof (Hri 0%nat Nat.le_0_1) as H.
 simpl in H; rewrite <- Hc in H.
 rename H into Hr₀; move Hr₀ before Hc.
 pose proof (Hri 1%nat (Nat.le_refl 1)) as H.
 simpl in H.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 move Hc₁ before Hns₁.
 move c₁ before ns₁.
 rename H into Hr₁; move Hr₁ before Hc₁.
 remember Hc as H; clear HeqH.
 eapply multiplicity_is_pos in H; try eassumption .
 rename H into Hrpos; move Hrpos before Hnz₁.
 remember Hns₁ as H; clear HeqH.
 eapply r_n_next_ns in H; try eassumption .
 move H before Hnz₁.
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember Hns₁ as H; clear HeqH.
 eapply hd_newton_segments in H; try eassumption .
 rename H into Hns₁i; move Hns₁i before Hns₁.
 remember Hns as H; clear HeqH.
 eapply next_pol_in_K_1_mq in H; try eassumption .
 remember (m * q₀)%positive as m₁ eqn:Hm₁.
 rename H into HK₁; move HK₁ before Hnz₁.
 move Hm₁ before Hq₀.
 rewrite Hini₁, Hfin₁; simpl.
 rewrite Hαk₁; simpl.
 rewrite Qnum_inv_Qnat_sub; [ | apply Hrpos ].
 rewrite Qden_inv_Qnat_sub; [ | apply Hrpos ].
 rewrite Z.add_0_r, Z.mul_1_r.
 remember (root_tail_series_from_cγ_list m₁ pol₁ ns₁) as t.
 remember (series_order {| terms := t |} 0) as v eqn:Hv .
 symmetry in Hv.
 destruct v; [ idtac | constructor ].
 apply Qbar.qfin_le_mono.
 rewrite Nat.sub_0_r.
 rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
 rewrite Pos2Z.inj_mul.
 rewrite Z.div_mul_cancel_r; [ | apply Pos2Z_ne_0 | apply Pos2Z_ne_0 ].
 erewrite αj_m_eq_p_r with (ns₁ := ns₁); try eassumption; [ | reflexivity ].
 rewrite Z.mul_shuffle0.
 rewrite <- Zposnat2Znat; auto.
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
 rewrite Z.div_mul; [ | apply Pos2Z_ne_0 ].
 unfold Qle; simpl.
 rewrite Z.mul_1_r.
 apply Z.add_nonneg_nonneg; [ idtac | apply Nat2Z.is_nonneg ].
 apply Z.lt_le_incl.
 eapply p_is_pos; eassumption .

 simpl in Hz₁; simpl.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hz₁.

  remember (m * q₀)%positive as m₁ eqn:Hm₁ .
  replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
  pose proof (Hri 0%nat (Nat.le_0_l (S (S n)))) as H.
  simpl in H; rewrite <- Hc in H.
  rename H into Hr₀; move Hr₀ before Hc.
  assert (1 ≤ S (S n)) as H by apply le_n_S, Nat.le_0_l.
  apply Hri in H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in H.
  rename H into Hr₁; move Hr₁ before Hc₁.
  remember Hc as H; clear HeqH.
  eapply multiplicity_is_pos in H; try eassumption .
  rename H into Hrpos; move Hrpos before Hns₁.
  remember Hns₁ as H; clear HeqH.
  eapply r_n_next_ns in H; try eassumption .
  destruct H as (αj₁, (αk₁, H)).
  destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
  remember Hns₁ as H; clear HeqH.
  eapply hd_newton_segments in H; try eassumption .
  rename H into Hns₁i; move Hns₁i before Hns₁.
  remember Hns as H; clear HeqH.
  eapply next_pol_in_K_1_mq in H; try eassumption .
  rewrite <- Hm₁ in H.
  rename H into HK₁; move HK₁ before Hns₁i.
  eapply IHn with (ns := ns₁) (pol := pol₁); try eassumption .
   symmetry in Hr₁; symmetry.
   eapply q_eq_1_any_r with (pol := pol₁); try eassumption; auto.

   intros i Hin.
   apply Nat.succ_le_mono in Hin.
   apply Hpsi in Hin; simpl in Hin.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin.
   assumption.

   intros i Hin.
   apply Nat.succ_le_mono in Hin.
   apply Hri in Hin; simpl in Hin.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin.
   assumption.
Qed.

(* todo: group order_root_tail_nonneg_any_r_aux and this theorem together *)
Theorem order_root_tail_nonneg_any_r : ∀ pol ns c pol₁ ns₁ m q₀ n r,
  ns ∈ newton_segments pol
  → m = ps_list_com_polord (al pol)
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → zerop_1st_n_const_coeff n pol ns = false
  → root_multiplicity acf c (Φq pol ns) = r
  → (∀ i, r ≤ nth_r i pol ns)
  → (1 ≠ 0)%K
  → (0 ≤ order (root_tail (m * q₀) n pol₁ ns₁))%Qbar.
Proof.
intros pol ns c pol₁ ns₁ m q₀ n r.
intros Hns HK Hq₀ Hc Hpol₁ Hns₁ Hz Hr Hrle H₀.
rewrite zerop_1st_n_const_coeff_false_iff in Hz.
pose proof (Hz O (Nat.le_0_l n)) as H; simpl in H.
rename H into Hnz; move Hnz before Hc.
apply zerop_1st_n_const_coeff_false_iff in Hz.
remember (zerop_1st_n_const_coeff n pol₁ ns₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁.
 unfold root_tail.
 rewrite Hz₁.
 rewrite order_0; constructor.

 eapply order_root_tail_nonneg_any_r_aux with (r := r); try eassumption.
  pose proof (exists_pol_ord K pol) as H.
  destruct H as (m', (Hm', Hp)).
  rewrite <- HK in Hm'; subst m'.
  apply Hp.

  apply not_zero_1st_prop; auto; simpl.
  rewrite <- Hc, <- Hpol₁, <- Hns₁; assumption.

  apply non_decr_imp_eq; auto.
   rewrite zerop_1st_n_const_coeff_succ; simpl.
   rewrite <- Hc, <- Hpol₁, <- Hns₁; rewrite Hz₁.
   remember (ps_poly_nth 0 pol) as x.
   destruct (ps_zerop K x); [ contradiction | reflexivity ].

   simpl; rewrite <- Hc; assumption.
Qed.

Theorem zerop_1st_n_const_coeff_false_before : ∀ pol ns m,
  zerop_1st_n_const_coeff m pol ns = false
  → ∀ i, i ≤ m →
    zerop_1st_n_const_coeff i pol ns = false.
Proof.
intros pol ns m H i Hi.
rewrite zerop_1st_n_const_coeff_false_iff in H.
apply zerop_1st_n_const_coeff_false_iff.
intros j Hj; apply H.
transitivity i; assumption.
Qed.

Theorem multiplicity_not_decreasing : ∀ pol ns r,
  (∀ i : nat, if multiplicity_decreases pol ns i then False else True)
  → root_multiplicity acf (ac_root (Φq pol ns)) (Φq pol ns) = r
  → ∀ j, r ≤ nth_r j pol ns.
Proof.
intros pol ns r Hn Hr j.
pose proof Hn j as H.
remember (multiplicity_decreases pol ns j) as p eqn:Hp .
destruct p as [| p]; [ contradiction  |  ].
unfold multiplicity_decreases in Hp; simpl in Hp.
destruct
  (lt_dec
     (root_multiplicity acf (nth_c j pol ns)
                        (Φq (nth_pol j pol ns) (nth_ns j pol ns)))
     (root_multiplicity acf (ac_root (Φq pol ns)) (Φq pol ns)))
 as [| H₁].
contradiction .

 clear Hp.
 apply Nat.nlt_ge in H₁.
 rewrite Hr in H₁.
 erewrite <- nth_r_n in H₁; try eassumption; eauto  .
Qed.

Theorem contradiction_when_r_constant : ∀ pol ns c pol₁ ns₁ m q₀ r N ofs,
  (1 ≠ 0)%K
  → ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (ps_poly_nth 0 pol ≠ 0)%ps
  → m = ps_list_com_polord (al pol)
  → q₀ = q_of_m m (γ ns)
  → root_multiplicity acf c (Φq pol ns) = S r
  → (∀ i : nat, if multiplicity_decreases pol ns i then False else True)
  → (order (ps_pol_apply pol₁ (root_tail (m * q₀) 0 pol₁ ns₁)) =
     qfin ofs)%Qbar
  → N = Z.to_nat (2 * ' m * ' q₀ * Qnum ofs)
  → zerop_1st_n_const_coeff N pol₁ ns₁ = false
  → False.
Proof.
intros pol ns c pol₁ ns₁ m q₀ r N ofs.
intros H₀ Hns Hc Hpol₁ Hns₁ Hnz₀ Hm Hq₀ Hr Hn Hofs HN Hz.
rewrite Hc in Hpol₁.
assert (Hrle : ∀ n : nat, S r ≤ nth_r n pol ns).
 rewrite Hc in Hr.
 apply multiplicity_not_decreasing; assumption.

 remember (@summation _ Q_ring O N (λ i, β (nth_ns i pol₁ ns₁))) as u eqn:Hu .
 remember (1 # 2 * m * q₀) as η eqn:Hη .
 assert (Hηβ : ∀ i, i ≤ N → η < β (nth_ns i pol₁ ns₁)).
  clear Hofs Hn.
  intros i Hi.
  subst c q₀.
  eapply β_lower_bound_r_const with (n := i) (r := S r); try eassumption.
   pose proof (exists_pol_ord K pol) as H.
   destruct H as (m', (Hm', Hp)).
   rewrite <- Hm in Hm'; subst m'.
   apply Hp.

   apply Nat.lt_0_succ.

   eapply zerop_1st_n_const_coeff_false_before; eassumption.

   apply non_decr_imp_eq; try assumption.
   apply zerop_1st_n_const_coeff_false_succ; auto; simpl.
   rewrite <- Hpol₁, <- Hns₁.
   eapply zerop_1st_n_const_coeff_false_before; eassumption.

   apply eq_refl.

  assert (Huo : u <= ofs).
   revert H₀ Hns Hc Hpol₁ Hns₁ Hnz₀ Hm Hq₀ Hr Hofs Hz Hrle Hu; clear; intros.
   rewrite root_tail_when_r_r with (n := N) (r := (S r)) in Hofs;
    try eassumption.
    rewrite apply_nth_pol in Hofs; auto.
    rewrite <- Hu in Hofs.
    rewrite order_mul in Hofs.
    rewrite ps_monom_order in Hofs; [  | assumption ].
    apply Qbar.qfin_le_mono.
    rewrite <- Hofs.
    apply Qbar.le_sub_le_add_l.
    rewrite Qbar.sub_diag.
    apply order_pol_apply_nonneg; auto.
     intros a Ha.
     remember (nth_pol N pol₁ ns₁) as polN eqn:HpolN .
     remember (nth_ns N pol₁ ns₁) as nsN eqn:HnsN .
     assert (HnsNi : nsN ∈ newton_segments polN).
      rewrite zerop_1st_n_const_coeff_false_iff in Hz.
      remember (m * q₀)%positive as m₁.
      eapply nth_in_newton_segments_any_r with (ns₁ := ns₁); eauto  .
      generalize Hns₁; intros H.
      pose proof (Hz O (Nat.le_0_l N)) as H₁.
      rewrite <- Hc in Hpol₁.
      eapply r_n_next_ns in H; try eassumption; eauto  .
       destruct H as (αj₁, (αk₁, H)).
       destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
       eapply List_hd_in; try eassumption.
       intros H; rewrite H in Hns₁; subst ns₁; discriminate Hfin₁.

       rewrite <- nth_r_n with (n := 1%nat) (pol := pol) (ns := ns).
        symmetry.
        eapply r_le_eq_incl; try eassumption; auto.
         simpl.
         rewrite <- Hc; auto.

         intros i Hi.
         destruct i; auto; simpl.
         rewrite <- Hc, <- Hpol₁, <- Hns₁.
         apply Hz.
         apply Nat.succ_le_mono in Hi.
         apply Nat.le_0_r in Hi; subst i.
         apply Nat.le_0_l.

        simpl; rewrite <- Hc; assumption.

        simpl; rewrite <- Hc, <- Hpol₁; assumption.

        symmetry.
        apply nth_c_n.
         simpl; rewrite <- Hc; assumption.

         simpl; rewrite <- Hc, <- Hpol₁; assumption.

      remember HnsNi as H; clear HeqH.
      eapply f₁_orders in H; try eassumption; eauto  .
      erewrite <- nth_pol_succ in H; try eassumption.
       destruct H as (H, _).
       apply List_In_nth with (d := 0%ps) in Ha.
       destruct Ha as (n, Hn₁).
       rewrite Hn₁.
       apply H.

       symmetry.
       apply nth_c_n; try eassumption.

     rewrite Nat.add_0_l.
     rewrite <- Hc in Hpol₁.
     eapply order_root_tail_nonneg_any_r; try eassumption.
     rewrite zerop_1st_n_const_coeff_succ; simpl.
     rewrite <- Hc, <- Hpol₁, <- Hns₁, Hz.
     remember (ps_poly_nth 0 pol) as x.
     destruct (ps_zerop K x); [ contradiction  | reflexivity ].

    pose proof (exists_pol_ord K pol) as H.
    destruct H as (m', (Hm', Hp)).
    rewrite <- Hm in Hm'; subst m'.
    apply Hp.

    rewrite <- Hc in Hpol₁.
    apply non_decr_imp_eq; auto.
     apply zerop_1st_n_const_coeff_false_iff.
     intros j Hj.
     destruct j; [ assumption |  ].
     apply le_S_n in Hj.
     apply Nat.le_0_r in Hj; subst j; simpl.
     rewrite <- Hc, <- Hpol₁.
     rewrite zerop_1st_n_const_coeff_false_iff in Hz.
     pose proof (Hz O (Nat.le_0_l N)) as H₁.
     assumption.

     simpl; rewrite <- Hc; assumption.

    rewrite zerop_1st_n_const_coeff_succ; simpl.
    rewrite <- Hpol₁, <- Hns₁, Hz.
    remember (ps_poly_nth 0 pol) as x.
    destruct (ps_zerop K x); [ contradiction  | reflexivity ].

   assert (Hou : ofs < u).
    clear Hofs Hn.
    subst u.
    apply summation_all_lt in Hηβ.
    eapply Qle_lt_trans; try eassumption.
    rewrite Hη, HN.
    rewrite <- Pos2Z.inj_mul.
    rewrite <- Pos2Z.inj_mul.
    remember (2 * m * q₀)%positive as mq eqn:Hmq .
    rewrite Z.mul_comm.
    rewrite Z2Nat_inj_mul_pos_r.
    unfold Qle; simpl.
    rewrite Pos.mul_1_r.
    rewrite Pos2Z.inj_mul.
    rewrite Zpos_P_of_succ_nat.
    rewrite Nat2Z.inj_mul.
    remember (Qnum ofs) as nofs eqn:Hnofs .
    symmetry in Hnofs.
    destruct nofs as [| nofs| nofs]; simpl; auto.
     rewrite positive_nat_Z.
     rewrite Z.mul_succ_l.
     rewrite positive_nat_Z.
     rewrite <- Pos2Z.inj_mul.
     rewrite <- Z.mul_1_r at 1.
     eapply Z.le_trans.
      apply Z.mul_le_mono_nonneg_l with (m := (' Qden ofs)%Z); auto.

      rewrite Z.one_succ.
      apply Zlt_le_succ.
      apply Pos2Z.is_pos.

      apply Z.le_sub_le_add_l.
      rewrite Z.sub_diag; apply Pos2Z.is_nonneg.

     apply Zle_neg_pos.

    apply Qlt_not_le in Hou; contradiction .
Qed.

Definition f₁_root_when_r_constant pol ns :=
  if fld_zerop 1%K then 0%ps
  else
    let m := ps_list_com_polord (al pol) in
    let q₀ := q_of_m m (γ ns) in
    let pol₁ := next_pol pol (β ns) (γ ns) (ac_root (Φq pol ns)) in
    let ns₁ := List.hd phony_ns (newton_segments pol₁) in
    let s := root_tail (m * q₀) 0 pol₁ ns₁ in
    match order (ps_pol_apply pol₁ s) with
    | qfin ofs =>
        let N := Z.to_nat (2 * ' m * ' q₀ * Qnum ofs) in
        if zerop_1st_n_const_coeff N pol₁ ns₁ then
          match lowest_with_zero_1st_const_coeff acf N pol₁ ns₁ with
          | O => 0%ps
          | S i' => root_head 0 i' pol₁ ns₁
          end
        else 0%ps
    | ∞%Qbar => s
    end.

Theorem f₁_has_root_when_r_constant : ∀ pol ns pol₁,
  ns ∈ newton_segments pol
  → (ps_poly_nth 0 pol ≠ 0)%ps
  → pol₁ = next_pol pol (β ns) (γ ns) (ac_root (Φq pol ns))
  → (∀ i, if multiplicity_decreases pol ns i then False else True)
  → ∃ s, (ps_pol_apply pol₁ s = 0)%ps.
Proof.
intros pol ns pol₁ Hns Hnz₀ Hpol₁ Hn.
exists (f₁_root_when_r_constant pol ns).
unfold f₁_root_when_r_constant.
rewrite <- Hpol₁.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁.
remember (ac_root (Φq pol ns)) as c eqn:Hc in Hpol₁ |-*.
remember (ps_list_com_polord (al pol)) as m eqn:Hm.
remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
destruct (fld_zerop 1%K) as [H₀| H₀].
 unfold ps_pol_apply, apply_poly, apply_lap; simpl.
 destruct (al pol₁) as [| a]; [ reflexivity | simpl ].
 rewrite rng_mul_0_r, rng_add_0_l.
 apply eq_1_0_ps_0; assumption.

 remember (order (ps_pol_apply pol₁ s)) as ofs eqn:Hofs .
 destruct ofs as [ofs| ].
  remember (Z.to_nat (2 * ' m * ' q₀ * Qnum ofs)) as N eqn:HN .
  remember (zerop_1st_n_const_coeff N pol₁ ns₁) as z eqn:Hz .
  symmetry in Hz.
  destruct z.
   apply lowest_zerop_1st_n_const_coeff in Hz.
   destruct Hz as (i, (Hi, (Hin, (Hji, Hz)))).
   symmetry in Hi.
   rewrite Hi.
   destruct Hji as [Hi2| Hpi].
    move Hi2 at top; subst i.
    simpl in Hz.
    destruct (ps_zerop K (ps_poly_nth 0 pol₁)); [ | discriminate Hz ].
    apply a₀_0_root_0; assumption.

    destruct i.
     simpl in Hpi, Hz; rewrite Hpi in Hz; discriminate Hz.

     apply root_when_fin in Hpi; [ apply Hpi | assumption ].

   exfalso.
   remember (root_multiplicity acf c (Φq pol ns)) as r eqn:Hr .
   symmetry in Hr.
   pose proof (multiplicity_neq_0 acf pol ns Hns Hc) as H.
   destruct r; [ contradiction | ].
   eapply contradiction_when_r_constant; try eassumption.
   rewrite Hofs, Hs; reflexivity.

  symmetry in Hofs.
  apply order_inf; assumption.
Qed.

Theorem f₁_has_root : ∀ pol ns pol₁,
  ns ∈ newton_segments pol
  → (ps_poly_nth 0 pol ≠ 0)%ps
  → pol₁ = next_pol pol (β ns) (γ ns) (ac_root (Φq pol ns))
  → ∃ s, (ps_pol_apply pol₁ s = 0)%ps.
Proof.
intros pol ns pol₁ Hns Hnz₀ Hpol₁.
remember (ac_root (Φq pol ns)) as c eqn:Hc.
remember (root_multiplicity acf c (Φq pol ns)) as r eqn:Hr .
symmetry in Hr.
revert pol ns c pol₁ Hns Hnz₀ Hc Hpol₁ Hr.
induction r as (r, IHr) using all_lt_all; intros.
set (v := fun i => if multiplicity_decreases pol ns i then S O else O).
destruct (LPO v) as [Hn| Hn].
 subst c.
 eapply f₁_has_root_when_r_constant; try eassumption.
 intros i.
 pose proof Hn i as H; unfold v in H.
 destruct (multiplicity_decreases pol ns i); [ | constructor ].
 discriminate H.

 destruct Hn as (n, Hn).
 unfold v in Hn; clear v.
 unfold multiplicity_decreases in Hn.
 rewrite <- Hc, Hr in Hn.
 remember (nth_pol n pol ns) as poln eqn:Hpoln .
 remember (nth_ns n pol ns) as nsn eqn:Hnsn .
 remember (nth_c n pol ns) as cn eqn:Hcn .
 remember (root_multiplicity acf cn (Φq poln nsn)) as rn eqn:Hrn .
 symmetry in Hrn.
 destruct n.
  exfalso.
  simpl in Hpoln, Hnsn, Hcn.
  subst poln nsn cn.
  rewrite <- Hc in Hrn.
  rewrite Hrn in Hr; subst rn.
  destruct (lt_dec r r) as [H| H]; [  | apply Hn, eq_refl ].
  revert H; apply lt_irrefl.

  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  erewrite <- nth_r_n in Hrn; try eassumption; subst rn.
  destruct (lt_dec (nth_r (S n) pol ns) r) as [H| H].
   clear Hn; rename H into Hn.
   apply lowest_i_such_that_ri_lt_r₀ in Hn; [  | subst; auto ].
   destruct Hn as (i, (Hin, (Hir, Hri))).
   destruct Hir as [Hir| Hir].
    subst i.
    exfalso; revert Hri; rewrite <- Hr; subst.
    apply Nat.lt_irrefl.

    destruct i.
     exfalso; revert Hri; rewrite <- Hr; subst.
     apply Nat.lt_irrefl.

     remember (nth_pol i pol ns) as poli eqn:Hpoli .
     remember (nth_ns i pol ns) as nsi eqn:Hnsi .
     remember (nth_pol (S i) pol ns) as polsi eqn:Hpolsi .
     remember (nth_ns (S i) pol ns) as nssi eqn:Hnssi .
     remember (newton_segments polsi) as nsl eqn:Hnsl .
     remember (nth_c (S i) pol ns) as cssi eqn:Hcssi.
     remember (next_pol polsi (β nssi) (γ nssi) cssi) as polssi eqn:Hpolssi.
     symmetry in Hnsl.
     destruct nsl as [| ns₂].
      destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₁| H₁].
       apply a₀_0_root_0 in H₁.
       exists 0%ps; assumption.

       generalize Hnsl; intros H.
       rewrite Hpolsi in H.
       simpl in H.
       rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
       apply nth_newton_segments_nil in H; auto.
        destruct H as (j, (Hjn, (Hjz, Hjnz))).
        destruct Hjz as [Hjz| Hjz].
         subst j.
         simpl in Hjnz.
         destruct (ps_zerop K (ps_poly_nth 0 pol₁)); [ contradiction | ].
         discriminate Hjnz.

         exists (root_head 0 (pred j) pol₁ ns₁).
         apply root_when_fin; assumption.

        eapply List_hd_in; try eassumption.
        clear H.
        remember Hns as H; clear HeqH.
        eapply next_has_root_0_or_newton_segments in H; auto.
        simpl in H.
        rewrite <- Hc, <- Hpol₁ in H.
        destruct H; [ contradiction | assumption ].

      remember (zerop_1st_n_const_coeff i pol₁ ns₁) as z eqn:Hz .
      symmetry in Hz.
      destruct z.
       apply lowest_zerop_1st_n_const_coeff in Hz.
       destruct Hz as (m, (Hm, (Hmi, (Hle, Heq)))).
       destruct Hle as [Hle| Hle].
        move Hle at top; subst m.
        simpl in Heq.
        destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₂| H₂].
         exists 0%ps.
         apply a₀_0_root_0; assumption.

         discriminate Heq.

        exists (root_head 0 (pred m) pol₁ ns₁).
        apply root_when_fin; assumption.

       eapply IHr with (pol := polsi) (ns := nssi) (pol₁ := polssi) in Hri.
        destruct Hri as (s₁, Hs₁).
        remember (root_head 0 i pol₁ ns₁) as rh.
        remember (ps_monom 1%K (γ_sum 0 i pol₁ ns₁)) as mo.
        exists (rh + mo * s₁)%ps; subst rh mo.
        rewrite apply_nth_pol; auto.
        erewrite nth_pol_n; try eassumption; eauto  .
        erewrite <- nth_c_n; try eassumption.
        rewrite <- Hcssi, <- Hpolssi.
        rewrite Hs₁, rng_mul_0_r; reflexivity.

        eapply List_hd_in.
         subst nssi; simpl.
         eapply nth_ns_n; try eassumption; eauto  .
          rewrite Hc; reflexivity.

          subst polsi; simpl.
          eapply nth_pol_n; try eassumption; eauto  .
          rewrite Hc; reflexivity.

         intros H; rewrite H in Hnsl; discriminate Hnsl.

        rewrite zerop_1st_n_const_coeff_false_iff in Hz.
        pose proof (Hz i (Nat.le_refl i)) as H.
        rewrite Hpolsi; simpl.
        rewrite <- Hc, <- Hpol₁, <- Hns₁; auto.

        reflexivity.

        erewrite nth_c_n in Hcssi; try eassumption.
        rewrite <- Hcssi; assumption.

        symmetry.
        apply nth_r_n; try eassumption.
        erewrite nth_c_n; try eassumption; reflexivity.

   exfalso; apply Hn, eq_refl.
Qed.

Theorem degree_pos_imp_has_ns : ∀ pol,
  degree (ps_zerop K) pol ≥ 1
  → (ps_poly_nth 0 pol ≠ 0)%ps
  → newton_segments pol ≠ [].
Proof.
intros pol Hdeg Hnz.
unfold degree in Hdeg.
unfold ps_poly_nth in Hnz.
unfold ps_lap_nth in Hnz.
unfold newton_segments, points_of_ps_polynom.
unfold points_of_ps_lap, points_of_ps_lap_gen; simpl.
intros Hnsl.
remember (al pol) as la eqn:Hla .
clear pol Hla.
destruct la as [| a]; [ apply Hnz; reflexivity | idtac ].
simpl in Hdeg, Hnz, Hnsl.
remember (degree_plus_1_of_list (ps_zerop K) la) as d eqn:Hd .
symmetry in Hd.
destruct d.
 destruct (ps_zerop K a) as [H₁| H₁].
  apply Nat.nlt_ge in Hdeg; apply Hdeg, Nat.lt_0_1.

  apply Nat.nlt_ge in Hdeg; apply Hdeg, Nat.lt_0_1.

 clear Hdeg.
 apply order_fin in Hnz.
 remember (order a) as va eqn:Hva .
 symmetry in Hva.
 destruct va as [va| ]; [ clear Hnz | apply Hnz; reflexivity ].
 remember 1%nat as pow in Hnsl; clear Heqpow.
 revert a d va pow Hd Hva Hnsl.
 induction la as [| b]; intros; [ discriminate Hd | idtac ].
 simpl in Hd.
 remember (degree_plus_1_of_list (ps_zerop K) la) as e eqn:He  in Hd.
 symmetry in He.
 destruct e.
  destruct (ps_zerop K b) as [H₁| H₁]; [ discriminate Hd | idtac ].
  clear d Hd.
  simpl in Hnsl.
  apply order_fin in H₁.
  remember (order b) as vb eqn:Hvb .
  symmetry in Hvb.
  destruct vb as [vb| ]; [ discriminate Hnsl | apply H₁; reflexivity ].

  clear d Hd.
  simpl in Hnsl.
  remember (order b) as vb eqn:Hvb .
  symmetry in Hvb.
  destruct vb as [vb| ]; [ discriminate Hnsl | idtac ].
  eapply IHla; eauto .
Qed.

Theorem puiseux_series_algeb_closed : ∀ (pol : polynomial (puiseux_series α)),
  degree (ps_zerop K) pol ≥ 1
  → ∃ s, (ps_pol_apply pol s = 0)%ps.
Proof.
intros pol Hdeg.
destruct (ps_zerop _ (ps_poly_nth 0 pol)) as [Hz| Hnz].
 exists 0%ps.
 unfold ps_pol_apply, apply_poly, apply_lap; simpl.
 unfold ps_poly_nth, ps_lap_nth in Hz; simpl in Hz.
 remember (al pol) as la eqn:Hla .
 symmetry in Hla.
 destruct la as [| a]; [ reflexivity | simpl in Hz; simpl ].
 rewrite rng_mul_0_r, rng_add_0_l; assumption.

 remember Hdeg as H; clear HeqH.
 eapply degree_pos_imp_has_ns in H; [ idtac | assumption ].
 rename H into Hnsnz.
 remember (newton_segments pol) as nsl eqn:Hnsl .
 symmetry in Hnsl.
 destruct nsl as [| ns]; [ exfalso; apply Hnsnz; reflexivity | idtac ].
 clear Hnsnz.
 assert (ns ∈ newton_segments pol) as Hns.
  rewrite Hnsl; left; reflexivity.

  generalize Hns; intros H.
  remember (ac_root (Φq pol ns)) as c eqn:Hc .
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  eapply f₁_has_root with (pol₁ := pol₁) in H; eauto .
   destruct H as (s₁, Hs₁).
   exists (ps_monom c (γ ns) + ps_monom 1%K (γ ns) * s₁)%ps.
   eapply f₁_root_f_root; eauto .
   reflexivity.

   subst c; assumption.
Qed.

End theorems.

Check puiseux_series_algeb_closed.
