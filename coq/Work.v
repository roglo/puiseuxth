(* Work.v *)

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
Require Import RootWhenR1.
Require Import RootAnyR.

Set Implicit Arguments.

Axiom exists_or_not_forall : ∀ P : nat → Prop, { ∃ n, P n } + { ∀ n, ¬P n }.

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
  (rn < r)%nat.

Theorem non_decr_imp_eq : ∀ pol ns b r,
  ns ∈ newton_segments pol
  → zerop_1st_n_const_coeff b pol ns = false
  → nth_r 0 pol ns = r
  → (∀ i, r ≤ nth_r i pol ns)
  → ∀ n : nat, n ≤ b → nth_r n pol ns = r.
Proof.
intros pol ns b r Hns Hz Hr Hri n Hnb.
revert pol ns n Hns Hz Hr Hri Hnb.
induction b; intros; [ apply Nat.le_0_r in Hnb; subst n; auto | idtac ].
destruct n; auto.
apply le_S_n in Hnb.
remember Hz as H; clear HeqH.
rewrite zerop_1st_n_const_coeff_succ2 in H.
apply orb_false_iff in H.
destruct H as (Hz₁, _).
remember Hns as H; clear HeqH.
eapply all_ns_in_newton_segments in H; try eassumption.
rename H into Hnsni.
remember (nth_ns n pol ns) as nsn eqn:Hnsn .
remember (nth_pol n pol ns) as poln eqn:Hpoln .
remember (ac_root (Φq poln nsn)) as cn eqn:Hcn .
remember (next_pol poln (β nsn) (γ nsn) cn) as poln₁ eqn:Hpoln₁ .
remember (List.hd phony_ns (newton_segments poln₁)) as nsn₁ eqn:Hnsn₁ .
remember (ac_root (Φq poln₁ nsn₁)) as cn₁ eqn:Hcn₁ .
remember (nth_r (S n) pol ns) as r₁ eqn:Hr₁ .
remember Hnb as H; clear HeqH.
symmetry in Hr₁.
apply Nat.succ_le_mono in H.
rewrite zerop_1st_n_const_coeff_false_iff in Hz.
apply Hz in H.
erewrite nth_pol_succ in H; try eassumption; try reflexivity.
erewrite nth_c_n in H; try eassumption.
rewrite <- Hcn, <- Hpoln₁ in H.
rename H into Hnzn₁.
remember Hns as H; clear HeqH.
eapply IHb in H; eauto .
rename H into Hrn.
remember Hcn as H; clear HeqH.
erewrite <- nth_c_n in H; try eassumption.
rename H into Hcnn.
remember Hnsni as H; clear HeqH.
eapply next_ns_r_non_decr with (r := r) (r₁ := r₁) in H; eauto .
 destruct H; symmetry; assumption.

 erewrite <- nth_r_n; try eassumption.

 symmetry; clear H.
 remember Hpoln as H; clear HeqH.
 eapply nth_pol_succ in H; try eassumption.
 rewrite <- Hpoln₁ in H.
 symmetry in H.
 rename H into Hpoln₁₁.
 remember Hpoln₁₁ as H; clear HeqH.
 eapply nth_ns_succ in H; try eassumption.
 rewrite <- Hnsn₁ in H.
 symmetry in H.
 rename H into Hnsn₁₁.
 erewrite nth_r_n in Hr₁; eauto .
 erewrite nth_c_n; try eassumption.

 rewrite <- Hr₁; apply Hri.
Qed.

Lemma zerop_1st_n_const_coeff_false_succ : ∀ pol ns n,
  (ps_poly_nth 0 pol ≠ 0)%ps
  → zerop_1st_n_const_coeff n (nth_pol 1 pol ns) (nth_ns 1 pol ns) = false
  ↔ zerop_1st_n_const_coeff (S n) pol ns = false.
Proof.
intros pol ns n Hnz.
split; intros H.
 apply zerop_1st_n_const_coeff_false_iff.
 apply not_zero_1st_prop; assumption.

 simpl in H.
 destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
 contradiction.
Qed.

(* cf root_tail_from_0 *)
Theorem root_tail_from_0_const_r : ∀ pol ns c pol₁ ns₁ c₁ m q₀ b r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₁ = ac_root (Φq pol₁ ns₁)
  → (∀ i, i ≤ 1%nat → nth_r i pol ns = r)
  → (∀ n, r ≤ nth_r n pol ns)
  → (1 ≠ 0)%K
  → (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum b 0 pol₁ ns₁) *
       root_tail (m * q₀) (b + 1) pol₁ ns₁)%ps.
Proof.
intros pol ns c pol₁ ns₁ c₁ m q₀ b r.
intros Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hc₁ Hri Hrle H₀.
remember (m * q₀)%positive as m₁.
destruct b; [ subst m₁; eapply root_tail_split_1st_any_r; eauto  | idtac ].
remember (S b) as b₁ eqn:Hb₁ .
unfold root_tail, root_head; simpl.
rewrite Nat.add_0_r.
remember (zerop_1st_n_const_coeff b₁ pol₁ ns₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁.
 rewrite Nat.add_1_r.
 rewrite zerop_1st_n_const_coeff_succ2.
 rewrite Hz₁; simpl.
 rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

 rewrite rng_add_0_r.
 unfold γ_sum; simpl.
 unfold summation; simpl.
 rewrite Nat.add_0_r, rng_add_0_r.
 remember Hns as HK₁; clear HeqHK₁.
 eapply next_pol_in_K_1_mq in HK₁; try eassumption .
 rewrite <- Heqm₁ in HK₁.
 rewrite Hb₁ in Hz₁.
 rewrite zerop_1st_n_const_coeff_succ in Hz₁.
 apply Bool.orb_false_iff in Hz₁.
 destruct Hz₁ as (Hz₁, Hpsi).
 simpl in Hz₁.
 rewrite Nat.add_1_r.
 rewrite zerop_1st_n_const_coeff_succ.
 remember (zerop_1st_n_const_coeff 0 pol₁ ns₁) as x.
 simpl in Heqx.
 remember (ps_poly_nth 0 pol₁) as y.
 destruct (ps_zerop R y) as [| Hnz₁]; [ discriminate Hz₁ | subst y ].
 clear Hz₁; subst x.
 rewrite Bool.orb_false_l, Hb₁.
 rewrite zerop_1st_n_const_coeff_succ2, Hpsi.
 rewrite Bool.orb_false_l.
 rewrite <- Hb₁.
 remember (S b₁) as sb₁; simpl; subst sb₁.
 pose proof (Hri O Nat.le_0_1) as H; simpl in H.
 rename H into Hr₀.
 pose proof (Hri 1%nat (Nat.le_refl 1)) as H; simpl in H.
 rename H into Hr₁.
 rewrite <- Hc in Hr₀.
 rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in Hr₁.
 rewrite <- Hc₁.
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 assert (0 < r)%nat as Hrpos by (eapply multiplicity_is_pos; try eassumption ).
 remember Hns₁ as H; clear HeqH.
 eapply r_n_next_ns in H; try eassumption .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 apply zerop_1st_n_const_coeff_false_succ in Hpsi; [ idtac | assumption ].
 rewrite <- Hb₁ in Hpsi.
 remember Hns₁ as H; clear HeqH.
 eapply hd_newton_segments in H; try eassumption.
 rename H into Hns₁i.
 remember Hr₁ as H; clear HeqH.
 rewrite <- nth_r_n with (n := O) (ns := ns₁) (pol := pol₁) in H; auto.
 rename H into Hr₁n.
 assert
  (∀ n, n ≤ b₁ → nth_ns n pol₁ ns₁ ∈ newton_segments (nth_pol n pol₁ ns₁)).
  apply all_ns_in_newton_segments with (r := r); try assumption.
  intros i.
  pose proof (Hrle (S i)) as H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; assumption.

  rename H into Hain.
  assert (∀ n, n ≤ b₁ → nth_r n pol₁ ns₁ = r) as Hreq.
   apply non_decr_imp_eq; auto.
   intros i.
   pose proof (Hrle (S i)) as H; simpl in H.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; assumption.

   assert (∀ i, i ≤ b₁ → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps).
    rewrite Hb₁; apply not_zero_1st_prop; auto.
    rewrite Hb₁ in Hpsi.
    apply zerop_1st_n_const_coeff_false_succ; assumption.

    clear Hpsi; rename H into Hpsi.
    assert (∀ i, r ≤ nth_r i pol₁ ns₁) as Hrle₁.
     eapply all_r_le_next with (ns := ns); try eassumption.

     remember (nth_ns b₁ pol₁ ns₁) as nsb₂ eqn:Hnsb₂ .
     remember (nth_pol b₁ pol₁ ns₁) as polb₂ eqn:Hpolb₂ .
     pose proof (Hain b₁ (Nat.le_refl b₁)) as H.
     rewrite <- Hnsb₂, <- Hpolb₂ in H.
     rename H into Hnsb₂i.
     remember Hns₁i as H; clear HeqH.
     eapply r_n_nth_ns with (n := b) (r := r) in H; eauto .
      erewrite <- nth_ns_succ2 in H; eauto .
      rewrite <- Hb₁ in H.
      rewrite <- Hnsb₂ in H.
      destruct H as (αjb₂, (αkb₂, H)).
      destruct H as (Hinib₂, (Hfinb₂, (Hαjb₂, Hαkb₂))).
      unfold root_tail_from_cγ_list, ps_monom; simpl.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
      erewrite nth_γ_n; eauto ; simpl.
      remember (nth_pol b₁ pol₂ ns₂) as polb₃ eqn:Hpolb₃ .
      remember (nth_ns b₁ pol₂ ns₂) as nsb₃ eqn:Hnsb₃ .
      rewrite Hinib₂, Hfinb₂; simpl.
      rewrite Hαkb₂; simpl.
      rewrite Qnum_inv_Qnat_sub; auto.
      rewrite Qden_inv_Qnat_sub; auto.
      rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
      rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
      rewrite Pos2Z.inj_mul.
      rewrite Z.div_mul_cancel_r; auto.
      remember Hns₁i as H; clear HeqH.
      eapply nth_pol_in_K_1_m with (poln := polb₂) in H; eauto .
      rename H into HKb₂.
      pose proof (Hreq b₁ (Nat.le_refl b₁)) as H.
      erewrite nth_r_n in H; eauto .
      erewrite nth_c_n in H; eauto .
      rename H into Hrb₂.
      erewrite αj_m_eq_p_r with (pol₁ := polb₂); eauto .
      rewrite Pos2Z.inj_mul, Z.mul_shuffle0, Zposnat2Znat; auto.
      rewrite <- Z.mul_assoc.
      rewrite <- Zposnat2Znat; simpl; try eassumption.
      rewrite Z.div_mul; auto.
      destruct (ps_zerop R (ps_poly_nth 0 polb₃)) as [H₁| H₁].
       rewrite rng_mul_0_r, rng_add_0_r.
       remember (Qden αjb₂ * Pos.of_nat r * Qden αkb₂)%positive as dd.
       rewrite ps_adjust_eq with (n := O) (k := dd); symmetry.
       rewrite ps_adjust_eq with (n := O) (k := m₁); symmetry.
       unfold adjust_ps; simpl.
       rewrite Pos.mul_comm.
       do 2 rewrite Z.sub_0_r.
       do 2 rewrite series_shift_0.
       rewrite fold_series_const, series_stretch_const.
       rewrite Z.mul_shuffle0.
       erewrite αj_m_eq_p_r with (pol₁ := polb₂); try eassumption; eauto .
       do 2 rewrite <- Z.mul_assoc.
       remember (Z.of_nat r * (' Qden αjb₂ * ' Qden αkb₂))%Z as x.
       rewrite Z.mul_comm, Z.mul_shuffle0 in Heqx.
       rewrite <- Zposnat2Znat in Heqx; auto.
       simpl in Heqx.
       rewrite <- Heqdd in Heqx; subst x.
       apply mkps_morphism; auto.
       unfold series_stretch.
       constructor; intros i; simpl.
       rename H₁ into Hzb₃.
       destruct (zerop (i mod Pos.to_nat dd)) as [H₁| H₁].
        apply Nat.mod_divides in H₁; auto.
        destruct H₁ as (d, Hd).
        rewrite Nat.mul_comm in Hd; rewrite Hd.
        rewrite Nat.div_mul; auto.
        unfold root_tail_series_from_cγ_list.
        rewrite <- Hd.
        destruct (zerop i) as [H₁| H₁].
         subst i.
         apply Nat.eq_mul_0_l in H₁; auto.
         subst d; simpl.
         destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [H₁| H₁].
          pose proof (Hpsi b₁ (Nat.le_refl b₁)) as H.
          rewrite <- Hpolb₂ in H; contradiction.

          erewrite nth_c_n; try eassumption; reflexivity.

         simpl.
         destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [| H₂]; auto.
         destruct d.
          rewrite Hd in H₁.
          exfalso; revert H₁; apply Nat.lt_irrefl.

          remember (ac_root (Φq polb₂ nsb₂)) as cb₂ eqn:Hcb₂ .
          erewrite <- nth_pol_n with (c := c₁); eauto .
          erewrite <- nth_ns_n with (c := c₁); eauto .
           simpl.
           rewrite <- Hpolb₃.
           destruct (ps_zerop R (ps_poly_nth 0 polb₃));
            [ reflexivity | contradiction ].

           eapply nth_pol_n with (c := c₁); eauto .

        destruct (zerop i); [ subst i | reflexivity ].
        rewrite Nat.mod_0_l in H₁; auto.
        exfalso; revert H₁; apply Nat.lt_irrefl.

       rename H₁ into Hnzb₃.
       remember Hnsb₃ as H; clear HeqH.
       erewrite nth_ns_n in H; eauto .
       erewrite <- nth_pol_n in H; eauto .
       rewrite <- Hpolb₃ in H.
       rename H into Hnsb₃₁.
       remember Hpolb₃ as H; clear HeqH.
       erewrite nth_pol_n in H; eauto .
       rename H into Hpolb₃n.
       remember Hnsb₃₁ as H; clear HeqH.
       eapply next_ns_in_pol with (pol := polb₂) in H; eauto .
       rename H into Hnsb₃i.
       assert (1 ≤ b₁) as H by (subst b₁; apply le_n_S, Nat.le_0_l).
       apply Hain in H; simpl in H.
       rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
       rename H into Hns₂i.
       pose proof (Hrle₁ (S b₁)) as H; simpl in H.
       rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
       rename H into Hler₃.
       remember Hnsb₂i as H; clear HeqH.
       remember (ac_root (Φq polb₃ nsb₃)) as cb₃ eqn:Hcb₃ .
       remember (root_multiplicity acf cb₃ (Φq polb₃ nsb₃)) as rcb₃ eqn:Hrcb₃ .
       symmetry in Hrcb₃.
       erewrite nth_r_n in Hler₃; eauto .
       erewrite nth_c_n in Hler₃; eauto .
       rewrite <- Hcb₃, Hrcb₃ in Hler₃.
       eapply next_ns_r_non_decr in H; eauto .
       destruct H as (H₁, H); move H₁ at top; subst rcb₃.
       destruct H as (αjb₃, (αkb₃, H)).
       destruct H as (Hinib₃, (Hfinb₃, (Hαjb₃, Hαkb₃))).
       rewrite Hinib₃, Hfinb₃; simpl.
       rewrite Hαkb₃; simpl.
       rewrite Qnum_inv_Qnat_sub; auto.
       rewrite Qden_inv_Qnat_sub; auto.
       rewrite Nat.sub_0_r.
       rewrite Z.add_0_r, Z.mul_1_r.
       remember (Qden αjb₂ * Pos.of_nat r * Qden αkb₂)%positive as dd.
       rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
       do 2 rewrite Pos2Z.inj_mul.
       rewrite Z.div_mul_cancel_r; simpl; auto.
       remember (Qnum αjb₂ * ' Qden αkb₂)%Z as nd.
       remember Hnsb₂i as H; clear HeqH.
       eapply nth_pol_in_K_1_m with (poln := polb₃) (n := b₁) in H; eauto .
        rename H into HKb₃.
        erewrite αj_m_eq_p_r with (pol₁ := polb₃); try eassumption; eauto .
        rewrite Z.mul_shuffle0.
        rewrite <- Zposnat2Znat; auto.
        rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
        rewrite Z.div_mul; auto.
        unfold ps_add, ps_mul; simpl.
        unfold cm; simpl.
        rewrite fold_series_const.
        rewrite fold_series_const.
        unfold ps_terms_add; simpl.
        unfold ps_ordnum_add; simpl.
        rewrite Z.mul_add_distr_r.
        rewrite Pos2Z.inj_mul, Z.mul_assoc, Z.mul_shuffle0.
        rewrite Z.min_l.
         rewrite Z.min_r.
          rewrite Z.add_simpl_l, Z.sub_diag.
          simpl.
          rewrite Pos.mul_assoc.
          rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
          unfold adjust_ps; simpl.
          rewrite series_shift_0.
          rewrite Z.sub_0_r.
          subst nd.
          remember (Qnum αjb₂ * ' Qden αkb₂ * ' m₁)%Z as x.
          rewrite Z.mul_shuffle0 in Heqx; subst x.
          erewrite αj_m_eq_p_r with (ns₁ := nsb₂) (pol₁ := polb₂); eauto .
          remember (p_of_m m₁ (γ nsb₂)) as pb₂ eqn:Hpb₂ .
          remember (pb₂ * Z.of_nat r * ' Qden αjb₂ * ' Qden αkb₂)%Z as x.
          do 2 rewrite <- Z.mul_assoc in Heqx.
          rewrite Z.mul_comm, Z.mul_assoc in Heqx.
          remember (Z.of_nat r * ' Qden αjb₂ * ' Qden αkb₂)%Z as y eqn:Hy .
          rewrite Z.mul_comm in Heqx; subst x.
          rewrite Z.mul_shuffle0, Z.mul_comm in Hy.
          rewrite Z.mul_assoc in Hy.
          rewrite <- Zposnat2Znat in Hy; auto.
          simpl in Hy; rewrite <- Heqdd in Hy; subst y.
          remember (m₁ * (dd * dd))%positive as x.
          rewrite Pos.mul_comm in Heqx; subst x.
          apply mkps_morphism; auto.
bbb.

         apply mkps_morphism.
(**)
          rewrite <- series_stretch_const with (k := (dd * dd)%positive).
          rewrite <- Z.mul_opp_l.
          do 2 rewrite Z2Nat_inj_mul_pos_r.
          do 2 rewrite <- stretch_shift_series_distr.
          rewrite <- series_stretch_add_distr.
          apply stretch_morph; [ reflexivity | idtac ].
          rewrite Z2Nat_neg_eq_0.
           rewrite series_shift_0.
           unfold series_add; simpl.
           constructor; simpl; intros i.
           rename H₁ into Hpsb₃.
           destruct (zerop i) as [H₁| H₁].
            subst i; simpl.
            destruct (lt_dec 0 (Z.to_nat pb₃)) as [H₁| H₁].
             rewrite rng_add_0_r.
             unfold root_tail_series_from_cγ_list; simpl.
             destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [H₃| H₃].
              contradiction.

              clear H₃; symmetry.
              erewrite nth_c_n; try eassumption .

             contradiction.

            rewrite rng_add_0_l.
            destruct (lt_dec i (Z.to_nat pb₃)) as [H₂| H₂].
             unfold root_tail_series_from_cγ_list; simpl.
             rewrite <- Hcb₂, <- Hpolb₃, <- Hbns₂.
             destruct i; [ fast_omega H₁ | clear H₁ ].
             destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [| H₁]; auto.
             simpl.
             destruct (ps_zerop R (ps_poly_nth 0 polb₃)) as [| H₃]; auto.
             unfold next_pow at 1; simpl.
             rewrite Hinib₃, Hfinb₃; simpl.
             rewrite Hαkb₃; simpl.
             rewrite Qnum_inv_Qnat_sub; auto.
             rewrite Qden_inv_Qnat_sub; auto.
             rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r, Pos.mul_1_r.
             rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
             rewrite Pos2Z.inj_mul.
             rewrite Z.div_mul_cancel_r; auto.
             erewrite αj_m_eq_p_r with (pol₁ := polb₃); try eassumption .
             rewrite Pos2Z.inj_mul.
             rewrite Z.mul_shuffle0, Zposnat2Znat; auto.
             rewrite <- Zposnat2Znat; auto.
             rewrite <- Z.mul_assoc, Z.div_mul; simpl; auto.
             remember (Nat.compare (Z.to_nat pb₃) (S i)) as cmp₁.
             rename Heqcmp₁ into Hcmp₁.
             symmetry in Hcmp₁.
             destruct cmp₁; auto.
              apply nat_compare_eq in Hcmp₁.
              rewrite Hcmp₁ in H₂.
              exfalso; revert H₂; apply Nat.lt_irrefl.

              apply nat_compare_lt in Hcmp₁.
              exfalso; fast_omega H₂ Hcmp₁.

             apply Nat.nlt_ge in H₂.
             remember (i - Z.to_nat pb₃)%nat as id.
             unfold root_tail_series_from_cγ_list.
             assert (∀ j, nth_r j polb₂ nsb₂ = r) as Hrib₂.
              eapply all_same_r_next with (ns := nsb₁); try eassumption .
               erewrite <- nth_pol_n with (c := c₁); try eassumption .

               erewrite <- nth_ns_n with (c := c₁); try eassumption .
               erewrite <- nth_pol_n with (c := c₁); try eassumption .

               intros j.
               rewrite Hpolb₁, Hnsb₁.
               pose proof (Hri (S j + b)%nat) as H; simpl in H.
               rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
               rewrite nth_r_add in H; auto.

              rewrite find_coeff_iter_succ with (r := r); auto.
               symmetry.
               pose proof (Hri (S (S (S b)))) as H.
               erewrite nth_r_n in H; try eassumption .
               remember (S (S b)) as b₂; simpl in H.
               rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
               subst b₂; remember (S b) as b₁; simpl in H.
               rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
               subst b₁; simpl in H.
               rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in H.
               rewrite <- Hnsb₃ in H.
               erewrite nth_c_n in H; try eassumption .
               erewrite nth_pol_n with (c := c₂) in H; try eassumption .
               rewrite <- Hpolb₃, <- Hcb₃ in H.
               rename H into Hrb₃.
               symmetry in Hrb₃.
               remember Hnsb₃₁ as H; clear HeqH.
               eapply q_eq_1_any_r in H; try eassumption .
               rename H into Hqb₃.
               assert (∀ j, nth_r j polb₃ nsb₃ = r) as Hrib₃.
                intros j.
                eapply all_same_r_next with (ns := nsb₂); try eassumption .

                rewrite find_coeff_iter_succ with (r := r); auto.
                symmetry.
                remember (S i) as si.
                remember (S (S id)) as ssid; simpl.
                rewrite <- Hcb₂, <- Hpolb₃.
                erewrite <- nth_ns_n with (ns := ns₂); try eassumption .
                rewrite <- Hnsb₃.
                destruct i;
                 [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
                clear H₁.
                destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [H₁| H₁].
                 contradiction.

                 clear H₁.
                 erewrite next_pow_eq_p; try eassumption .
                 rewrite <- Hpb₃.
                 subst si ssid.
                 remember (S i) as si.
                 remember (S id) as sid; simpl.
                 destruct (ps_zerop R (ps_poly_nth 0 polb₃)) as [| H₁]; auto.
                 clear H₁.
                 subst si.
                 remember (Nat.compare (Z.to_nat pb₃) (S i)) as cmp₁
                  eqn:Hcmp₁ .
                 symmetry in Hcmp₁.
                 destruct cmp₁.
                  apply nat_compare_eq in Hcmp₁.
                  rewrite Hcmp₁, Nat.sub_diag in Heqid; subst id; reflexivity.

                  apply nat_compare_lt in Hcmp₁.
                  destruct id; [ exfalso; fast_omega Heqid Hcmp₁ | idtac ].
                  rewrite <- Hcb₃.
                  remember (next_pol polb₃ (β nsb₃) (γ nsb₃) cb₃) as polb₄.
                  remember (List.hd phony_ns (newton_segments polb₄)) as nsb₄.
                  rename Heqpolb₄ into Hpolb₄.
                  rename Heqnsb₄ into Hnsb₄.
                  assert (polb₄ = nth_pol (S (S (S b))) pol₁ ns₁)
                   as Hpolb₄pol₁.
                   rewrite Hpolb₄.
                   symmetry.
                   eapply nth_pol_n with (c := c); try eassumption .
                    rewrite Hpolb₃.
                    remember (S (S b)) as sb; simpl.
                    rewrite <- Hc, <- Hpol₁, <- Hns₁.
                    subst sb.
                    symmetry.
                    eapply nth_pol_n with (c := c); try eassumption .
                     rewrite Hpolb₂.
                     remember (S b) as sb; simpl.
                     rewrite <- Hc, <- Hpol₁, <- Hns₁.
                     subst sb; simpl.
                     rewrite <- Hc₁, <- Hpol₂, <- Hns₂; auto.

                     rewrite Hnsb₂.
                     remember (S b) as sb; simpl.
                     rewrite <- Hc, <- Hpol₁, <- Hns₁.
                     subst sb; simpl.
                     rewrite <- Hc₁, <- Hpol₂, <- Hns₂; auto.

                    rewrite Hnsb₃.
                    remember (S (S b)) as sb; simpl.
                    rewrite <- Hc, <- Hpol₁, <- Hns₁.
                    subst sb; remember (S b) as sb; simpl.
                    rewrite <- Hc₁, <- Hpol₂, <- Hns₂; auto.
                    subst sb; simpl.
                    rewrite <- Hc₂, <- Hpol₃, <- Hns₃; auto.

                   assert (nsb₄ = nth_ns (S (S (S b))) pol₁ ns₁) as Hnsb₄ns₁.
                    rewrite Hnsb₄; symmetry.
                    eapply nth_ns_n with (c := c); try eassumption .
                    rewrite Hpolb₄.
                    remember (S (S b)) as sb; simpl.
                    rewrite <- Hc, <- Hpol₁, <- Hns₁.
                    subst sb; remember (S b) as sb; simpl.
                    rewrite <- Hc₁, <- Hpol₂, <- Hns₂; auto.
                    subst sb; simpl.
                    rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
                    f_equal.
                     rewrite Hpolb₃.
                     symmetry.
                     eapply nth_pol_n with (c := c₂); try eassumption .

                     f_equal.
                     rewrite Hnsb₃; auto.

                     rewrite Hnsb₃; auto.

                     rewrite Hcb₃.
                     rewrite Hpolb₃, Hnsb₃.
                     f_equal; f_equal.
                     symmetry.
                     eapply nth_pol_n with (c := c₂); try eassumption .

                    subst sid.
                    remember (Z.to_nat pb₃) as x.
                    replace x with (0 + x)%nat by reflexivity.
                    rewrite next_pow_add.
                    replace (S i)%nat with (S i - x + x)%nat at 2
                     by fast_omega Hcmp₁.
                    rewrite find_coeff_add.
                    rewrite <- Heqid.
                    symmetry.
                    destruct (ps_zerop R (ps_poly_nth 0 polb₄)) as [H₁| H₁].
                     remember (S id) as sid; simpl.
                     destruct (ps_zerop R (ps_poly_nth 0 polb₄)) as [H₃| H₃].
                      reflexivity.

                      contradiction.

                     apply find_coeff_more_iter with (r := r); auto.
                      eapply List_hd_in; try eassumption .
                      remember Hnsb₃₁ as H; clear HeqH.
                      eapply next_has_root_0_or_newton_segments in H; try eassumption .
                      simpl in H.
                      rewrite <- Hcb₃, <- Hpolb₄ in H.
                      destruct H; [ contradiction | auto ].

                      eapply
                       first_n_pol_in_K_1_m_any_r
                        with (pol := polb₃) (n := 1%nat); 
                       try eassumption .
                       intros j Hj.
                       destruct j; auto.
                       destruct j; [ simpl | exfalso; fast_omega Hj ].
                       rewrite <- Hcb₃, <- Hpolb₄; auto.

                       simpl; rewrite <- Hcb₃; auto.

                      remember (ac_root (Φq polb₄ nsb₄)) as c₄ eqn:Hc₄ .
                      assert (root_multiplicity acf c₄ (Φq polb₄ nsb₄) = r)
                       as Hr₄.
                       rewrite <- Hri₁ with (i := S (S (S b))); symmetry.
                       apply nth_r_n; auto.
                       rewrite Hc₄.
                       symmetry.
                       apply nth_c_n; auto.

                       remember Hnsb₃₁ as H; clear HeqH.
                       eapply r_n_next_ns in H; try eassumption .
                       destruct H as (αjb₄, (αkb₄, H)).
                       destruct H as (Hinib₄, (Hfinb₄, (Hαjb₄, Hαkb₄))).
                       eapply q_eq_1_any_r with (pol := polb₄); try eassumption .
                        eapply List_hd_in; try eassumption .
                        eapply newton_segments_not_nil; try eassumption .

                        eapply
                         nth_pol_in_K_1_m with (ns := ns₁) (n := (3 + b)%nat);
                         try eassumption .
                        intros j Hj.
                        destruct (le_dec j (S b)) as [H₃| H₃].
                         apply Hpsi; auto.

                         apply Nat.nle_gt in H₃.
                         destruct (eq_nat_dec j (S (S b))) as [H₄| H₄].
                          subst j.
                          remember (S b) as sb; simpl.
                          rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
                          subst sb; simpl.
                          rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
                          erewrite nth_pol_n with (c := c₂); try eassumption .
                          rewrite <- Hpolb₃.
                          auto.

                          destruct (eq_nat_dec j (S (S (S b)))) as [H₅| H₅].
                           2: exfalso; fast_omega Hj H₃ H₄ H₅.

                           subst j.
                           remember (S (S b)) as sb; simpl.
                           rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
                           subst sb; remember (S b) as sb; simpl.
                           rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
                           subst sb; simpl.
                           remember (ac_root (Φq pol₃ ns₃)) as c₃ eqn:Hc₃ .
                           erewrite
                            nth_pol_n with (poln := polb₃) (c := c₃);
                            try eassumption .
                            rewrite <- Hpolb₄; auto.

                            erewrite nth_pol_n with (c := c₂); try eassumption .

                        rewrite Hr₄; auto.

                      intros j.
                      rewrite <- (Hri₁ (j + S (S (S b)))%nat).
                      rewrite nth_r_add; f_equal; auto.

                      fast_omega Heqid Hpb₃pos.

                  apply nat_compare_gt in Hcmp₁.
                  apply Nat.nle_gt in Hcmp₁.
                  contradiction.

               eapply q_eq_1_any_r with (pol := polb₂) (αk := αkb₂); try eassumption .
               pose proof (Hrib₂ O) as H; simpl in H.
               rewrite <- Hcb₂ in H.
               rewrite H; auto.

           apply Z.opp_le_mono.
           rewrite Z.opp_0.
           rewrite Z.opp_involutive.
           rewrite Hpb₃.
           apply Z.lt_le_incl.
           eapply p_is_pos; try eassumption .

          rewrite Pos2Z.inj_mul, Z.mul_assoc.
          apply Z.mul_cancel_r; auto.
          subst dd nd.
          rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
          do 2 rewrite Pos2Z.inj_mul.
          rewrite Z.mul_assoc.
          apply Z.mul_cancel_r; auto.
          symmetry.
          rewrite Z.mul_assoc, Z.mul_shuffle0.
          subst rq.
          rewrite Zposnat2Znat; auto.
          eapply αj_m_eq_p_r with (ns₁ := nsb₂); try eassumption .

          rewrite Pos.mul_comm, Pos.mul_assoc.
          reflexivity.

         apply Z.le_sub_le_add_l.
         rewrite Z.sub_diag.
         apply Z.mul_nonneg_nonneg; auto.
         apply Z.mul_nonneg_nonneg; auto.
         rewrite Hpb₃.
         apply Z.lt_le_incl.
         eapply p_is_pos; try eassumption .
Qed.
*)

Theorem root_tail_when_r_r : ∀ pol ns pol₁ ns₁ c m q₀ b r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (1 ≠ 0)%K
  → ∀ n,
    (∀ i, (i ≤ S n)%nat → (nth_r i pol ns = r))
    → zerop_1st_n_const_coeff n pol₁ ns₁ = false
    → (root_tail (m * q₀) b pol₁ ns₁ =
       root_head b n pol₁ ns₁ +
         ps_monom 1%K (γ_sum b n pol₁ ns₁) *
         root_tail (m * q₀) (b + S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b r Hns Hm Hq₀ Hc Hpol₁ Hns₁ H₀ n Hri Hnz.
remember (m * q₀)%positive as m₁.
revert pol ns pol₁ ns₁ Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hri Hnz.
revert b c m q₀ m₁ Heqm₁.
induction n; intros.
 unfold root_head; simpl.
 remember (zerop_1st_n_const_coeff b pol₁ ns₁) as z₁ eqn:Hz₁ .
 symmetry in Hz₁.
 destruct z₁.
  rewrite rng_add_0_l.
  unfold root_tail.
  rewrite Hz₁, Nat.add_1_r.
  rewrite zerop_1st_n_const_coeff_succ2.
  rewrite Hz₁, Bool.orb_true_l.
  rewrite rng_mul_0_r; reflexivity.

  rewrite Nat.add_0_r, rng_add_0_r, Heqm₁.
bbb.
  rewrite root_tail_from_0_const_r; try eassumption .
  unfold root_head.
  rewrite Hz₁.
  unfold root_head_from_cγ_list.
  rewrite Nat.add_0_r, rng_add_0_r.
  reflexivity.

 remember (zerop_1st_n_const_coeff b pol₁ ns₁) as z₁ eqn:Hz₁ .
 symmetry in Hz₁.
 destruct z₁.
  unfold root_head, root_tail.
  rewrite Hz₁.
  rewrite zerop_1st_n_const_coeff_true_if; auto.
  rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

  rewrite root_head_succ; auto.
  remember (zerop_1st_n_const_coeff (b + S n) pol₁ ns₁) as z eqn:Hz .
  symmetry in Hz.
  destruct z.
   rewrite rng_add_0_r, Nat.add_succ_r.
   rewrite IHn; try eassumption .
   apply rng_add_compat_l.
   unfold γ_sum at 2; simpl.
   rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
   rewrite fold_γ_sum, ps_monom_add_r.
   rewrite <- rng_mul_assoc.
   apply rng_mul_compat_l.
   unfold root_tail.
   rewrite Hz.
   remember (b + S n)%nat as x; rewrite <- Nat.add_1_r; subst x.
   rewrite zerop_1st_n_const_coeff_true_if; auto.
   rewrite rng_mul_0_r; reflexivity.

   rewrite IHn; try eassumption .
   rewrite <- rng_add_assoc.
   apply rng_add_compat_l; simpl.
   symmetry.
   rewrite ps_monom_split_mul.
   rewrite rng_mul_comm, <- rng_mul_add_distr_l.
   unfold γ_sum at 1; simpl.
   rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
   rewrite fold_γ_sum, ps_monom_add_r.
   rewrite <- rng_mul_assoc.
   apply rng_mul_compat_l.
   rewrite rng_mul_add_distr_l.
   rewrite rng_mul_comm; simpl.
   rewrite <- ps_monom_split_mul.
   symmetry.
   do 3 rewrite Nat.add_succ_r.
   rewrite Heqm₁.
   eapply root_tail_sep_1st_monom_any_r; try eassumption .
   rewrite <- Nat.add_succ_r.
   apply zerop_1st_n_const_coeff_false_iff.
   assumption.
Qed.
*)

Theorem zzz : ∀ pol ns c pol₁,
  ns ∈ newton_segments pol
  → (ps_poly_nth 0 pol ≠ 0)%ps
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ∃ s, (ps_pol_apply pol₁ s = 0)%ps.
Proof.
intros pol ns c pol₁ Hns Hnz₀ Hc Hpol₁.
remember (root_multiplicity acf c (Φq pol ns)) as r eqn:Hr .
symmetry in Hr.
revert pol ns c pol₁ Hns Hnz₀ Hc Hpol₁ Hr.
induction r using all_lt_all; intros.
destruct r.
 exfalso; revert Hr.
 apply multiplicity_neq_0; assumption.

 rename H into IHm.
 destruct (exists_or_not_forall (multiplicity_decreases pol ns)) as [Hn| Hn].
  destruct Hn as (n, Hn).
  unfold multiplicity_decreases in Hn.
  rewrite <- Hc, Hr in Hn.
  remember (nth_pol n pol ns) as poln eqn:Hpoln .
  remember (nth_ns n pol ns) as nsn eqn:Hnsn .
  remember (nth_c n pol ns) as cn eqn:Hcn .
  remember (root_multiplicity acf cn (Φq poln nsn)) as rn eqn:Hrn .
  symmetry in Hrn.
  destruct n.
   simpl in Hpoln, Hnsn, Hcn.
   subst poln nsn cn.
   rewrite <- Hc in Hrn.
   rewrite Hrn in Hr; subst rn.
   exfalso; revert Hn; apply Nat.lt_irrefl.

   remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
   erewrite <- nth_r_n in Hrn; try eassumption ; subst rn.
   apply lowest_i_such_that_ri_lt_r₀ in Hn; [ idtac | subst; auto ].
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
     symmetry in Hnsl.
     destruct nsl as [| ns₂].
      destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
       apply a₀_0_root_0 in H₁.
       exists 0%ps; assumption.

       remember Hnsl as H; clear HeqH.
       rewrite Hpolsi in H.
       simpl in H.
       rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
       apply nth_newton_segments_nil in H; auto.
        destruct H as (j, (Hjn, (Hjz, Hjnz))).
        destruct Hjz as [Hjz| Hjz].
         subst j.
         simpl in Hjnz.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁)).
          contradiction.

          discriminate Hjnz.

         eapply root_when_fin; try eassumption .

        eapply List_hd_in; try eassumption .
        clear H.
        remember Hns as H; clear HeqH.
        eapply next_has_root_0_or_newton_segments in H; try eassumption .
        simpl in H.
        rewrite <- Hc, <- Hpol₁ in H.
        destruct H; auto.

      remember (zerop_1st_n_const_coeff i pol₁ ns₁) as z eqn:Hz .
      symmetry in Hz.
      destruct z.
       apply lowest_zerop_1st_n_const_coeff in Hz.
       destruct Hz as (m, (Hmi, (Hle, Heq))).
       destruct Hle as [Hle| Hle].
        subst m.
        simpl in Heq.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
         exists 0%ps.
         apply a₀_0_root_0; assumption.

         discriminate Heq.

        eapply root_when_fin; try eassumption .

       eapply IHm with (pol := polsi) (ns := nssi) in Hri.
        destruct Hri as (s₁, Hs₁).
        remember (root_head 0 i pol₁ ns₁) as rh.
        remember (ps_monom 1%K (γ_sum 0 i pol₁ ns₁)) as mo.
        exists (rh + mo * s₁)%ps; subst rh mo.
        rewrite apply_nth_pol; auto.
        erewrite nth_pol_n; try eassumption .
        erewrite <- nth_c_n; try eassumption .
        rewrite Hs₁, rng_mul_0_r; reflexivity.

        eapply List_hd_in.
         subst nssi; simpl.
         eapply nth_ns_n; try eassumption .
          rewrite Hc; reflexivity.

          subst polsi; simpl.
          eapply nth_pol_n; try eassumption .
          rewrite Hc; reflexivity.

         intros H; rewrite H in Hnsl; discriminate Hnsl.

        rewrite zerop_1st_n_const_coeff_false_iff in Hz.
        pose proof (Hz i (Nat.le_refl i)) as H.
        rewrite Hpolsi; simpl.
        rewrite <- Hc, <- Hpol₁, <- Hns₁; auto.

        try eassumption .

        erewrite nth_c_n; try eassumption .

        symmetry.
        apply nth_r_n; try eassumption .
        erewrite nth_c_n; try eassumption .

  pose proof (exists_pol_ord R pol) as H.
  destruct H as (m, Hm).
  destruct (ac_zerop 1%K) as [H₀| H₀].
   exists 0%ps.
   unfold ps_pol_apply, apply_poly, apply_lap; simpl.
   remember (al pol₁) as la; clear Heqla.
   destruct la as [| a]; [ reflexivity | simpl ].
   rewrite rng_mul_0_r, rng_add_0_l.
   apply eq_1_0_ps_0; assumption.

   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
    exists 0%ps.
    apply a₀_0_root_0; assumption.

    remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
    remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
    remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
    remember (order (ps_pol_apply pol₁ s)) as ofs eqn:Hofs .
    symmetry in Hofs.
    destruct ofs as [ofs| ].
     subst s.
     remember (1 # 2 * m * q₀) as η eqn:Hη .
     remember (Z.to_nat (2 * ' m * ' q₀ * Qnum ofs)) as N eqn:HN .
     apply eq_Qbar_eq in Hofs.
     remember (zerop_1st_n_const_coeff N pol₁ ns₁) as z eqn:Hz .
     symmetry in Hz.
     destruct z.
      unfold root_tail in Hofs.
      destruct N.
       exists 0%ps.
       simpl in Hz.
       destruct (ps_zerop R (ps_poly_nth 0 pol₁)); [ contradiction | idtac ].
       discriminate Hz.

       apply lowest_zerop_1st_n_const_coeff in Hz.
       destruct Hz as (i, (Hin, (Hji, Hz))).
       destruct Hji as [Hi| Hpi].
        subst i.
        simpl in Hz.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)); [ contradiction | idtac ].
        discriminate Hz.

        eapply root_when_fin; try eassumption .
bbb.
     rewrite root_tail_when_r_r with (n := N) in Hofs; try eassumption .

bbb.
  pose proof (exists_pol_ord R pol) as H.
  destruct H as (m, Hm).
  destruct (ac_zerop 1%K) as [H₀| H₀].
   exists 0%ps.
   unfold ps_pol_apply, apply_poly, apply_lap; simpl.
   remember (al pol₁) as la; clear Heqla.
   destruct la as [| a]; [ reflexivity | simpl ].
   rewrite rng_mul_0_r, rng_add_0_l.
   apply eq_1_0_ps_0; assumption.

   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
    exists 0%ps.
    apply a₀_0_root_0; assumption.

    remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
    remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
    remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
(**)
    remember (order (ps_pol_apply pol₁ s)) as ofs eqn:Hofs .
    symmetry in Hofs.
    destruct ofs as [ofs| ].
     subst s.
     remember (1 # 2 * m * q₀) as η eqn:Hη .
     remember (Z.to_nat (2 * ' m * ' q₀ * Qnum ofs)) as N eqn:HN .
     apply eq_Qbar_eq in Hofs.
bbb.
     rewrite root_tail_when_r_r with (n := N) in Hofs; try eassumption .
      rewrite Nat.add_0_l in Hofs.
      remember (zerop_1st_n_const_coeff N pol₁ ns₁) as z eqn:Hz .
      symmetry in Hz.
      destruct z.
       unfold root_tail in Hofs.
       rewrite <- Nat.add_1_r in Hofs.
       rewrite zerop_1st_n_const_coeff_true_if in Hofs; auto.
       rewrite rng_mul_0_r, rng_add_0_r in Hofs.
       destruct N.
        exists 0%ps.
        simpl in Hz.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)); [ contradiction | idtac ].
        discriminate Hz.

        apply lowest_zerop_1st_n_const_coeff in Hz.
        destruct Hz as (i, (Hin, (Hji, Hz))).
        destruct Hji as [Hi| Hpi].
         subst i.
         simpl in Hz.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁));
          [ contradiction | idtac ].
         discriminate Hz.

         eapply root_when_fin; try eassumption .

       remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
       exists s.
       apply order_inf.
       rewrite apply_nth_pol in Hofs; auto.
       rewrite order_mul in Hofs; auto.
       rewrite ps_monom_order in Hofs; auto.
       remember Σ (i = 0, N), β (nth_ns i pol₁ ns₁) as u eqn:Hu .
       assert (ofs < u) as H.
        subst u.
        assert (∀ i, i ≤ N → η < β (nth_ns i pol₁ ns₁)).
         intros i Hi.
         subst c q₀.
         assert (zerop_1st_n_const_coeff i pol₁ ns₁ = false) as Hz₁.
          rewrite zerop_1st_n_const_coeff_false_iff in Hz.
          apply zerop_1st_n_const_coeff_false_iff.
          intros j Hj.
          apply Hz.
          transitivity i; assumption.

          eapply β_lower_bound_r_const with (n := i) (r := S r); try eassumption .
           apply Nat.lt_0_succ.

           intros j Hji.
           unfold multiplicity_decreases in Hn.
           rewrite Hr in Hn.
           pose proof (Hn j) as H.
           apply Nat.nlt_ge in H.
           erewrite <- nth_r_n in H; try eassumption .
           rename H into Hrj.
           symmetry.
           eapply r_le_eq_incl; try eassumption .
            intros k Hki.
            rewrite zerop_1st_n_const_coeff_false_iff in Hz₁.
            destruct k; try eassumption .
            apply Nat.succ_le_mono in Hki.
            apply Hz₁ in Hki; simpl.
            rewrite <- Hpol₁, <- Hns₁; auto.

            intros k Hki.
            pose proof (Hn k) as H.
            apply Nat.nlt_ge in H.
            erewrite nth_r_n; try eassumption .

         apply summation_all_lt in H.
         eapply Qle_lt_trans; try eassumption .
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
          rewrite <- Z.mul_1_r in |- * at 1.
          eapply Z.le_trans.
           apply Z.mul_le_mono_nonneg_l with (m := (' Qden ofs)%Z); auto.
           rewrite Z.one_succ.
           apply Zlt_le_succ.
           apply Pos2Z.is_pos.

           apply Z.le_sub_le_add_l.
           rewrite Z.sub_diag; auto.

          apply Zle_neg_pos.

        apply Qlt_not_le in H.
        exfalso; apply H.
        apply Qbar.qfin_le_mono.
        rewrite <- Hofs.
        apply Qbar.le_sub_le_add_l.
        rewrite Qbar.sub_diag.
        apply order_pol_apply_nonneg; auto.
         intros a Ha.
         remember (nth_pol N pol₁ ns₁) as polN eqn:HpolN .
         remember (nth_ns N pol₁ ns₁) as nsN eqn:HnsN .
         assert (List.In nsN (newton_segments polN)) as HnsNi.
          rewrite zerop_1st_n_const_coeff_false_iff in Hz.
          remember (m * q₀)%positive as m₁.
          eapply nth_in_newton_segments_any_r with (ns₁ := ns₁); try eassumption .
           clear H.
           remember Hns₁ as H; clear HeqH.
           eapply r_n_next_ns in H; try eassumption .
            destruct H as (αj₁, (αk₁, H)).
            destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
            eapply List_hd_in; try eassumption .
            intros H; rewrite H in Hns₁; subst ns₁; discriminate Hfin₁.

            unfold multiplicity_decreases in Hn.
            rewrite <- Hc, Hr in Hn.
            rewrite <- nth_r_n with (n := 1%nat) (pol := pol) (ns := ns).
             symmetry.
             eapply r_le_eq_incl; try eassumption .
              simpl.
              rewrite <- Hc; auto.

              intros i Hi.
              destruct i; auto; simpl.
              rewrite <- Hc, <- Hpol₁, <- Hns₁.
              apply Hz.
              apply Nat.succ_le_mono in Hi.
              apply Nat.le_0_r in Hi; subst i.
              apply Nat.le_0_l.

              intros i Hi.
              clear H.
              pose proof (Hn i) as H.
              apply Nat.nlt_ge in H.
              erewrite nth_r_n; try eassumption .

             simpl; rewrite <- Hc; assumption.

             simpl; rewrite <- Hc, <- Hpol₁; assumption.

             symmetry.
             apply nth_c_n.
              simpl; rewrite <- Hc; assumption.

              simpl; rewrite <- Hc, <- Hpol₁; assumption.

           rename H into Huofs.
           intros i HiN.
           symmetry.
           eapply r_le_eq_incl; try eassumption .
            eapply List_hd_in; try eassumption .
            remember Hns as H; clear HeqH.
            eapply next_has_root_0_or_newton_segments in H; try eassumption .
            destruct H as [H| H].
             simpl in H.
             rewrite <- Hc, <- Hpol₁ in H; contradiction.

             simpl in H.
             rewrite <- Hc, <- Hpol₁ in H; assumption.

            intros j HjN.
            rewrite Nat.add_0_r.
            unfold multiplicity_decreases in Hn.
            rewrite <- Hc, Hr in Hn.
            pose proof (Hn (S j)) as H.
            erewrite <- nth_r_n in H; try eassumption .
            apply Nat.nlt_ge in H.
            simpl in H.
            rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
            transitivity (S r); auto.
            rewrite <- Hr; simpl.
            rewrite <- nth_r_n with (n := 1%nat) (pol := pol) (ns := ns);
             auto.
             rewrite <- nth_r_n with (n := O) (pol := pol) (ns := ns); auto.
             eapply r₁_le_r₀; try eassumption .
             simpl; rewrite <- Hc, <- Hpol₁.
             clear H.
             pose proof (Hz O (Nat.le_0_l N)) as H.
             assumption.

             simpl; rewrite <- Hc; assumption.

             simpl; rewrite <- Hc, <- Hpol₁; assumption.

             symmetry.
             apply nth_c_n.
              simpl; rewrite <- Hc; assumption.

              simpl; rewrite <- Hc, <- Hpol₁; assumption.

          rename H into Huofs.
          remember HnsNi as H; clear HeqH.
          eapply f₁_orders in H; try eassumption .
          erewrite <- nth_pol_succ in H; try eassumption .
           destruct H as (H, _).
           apply List_In_nth with (d := 0%ps) in Ha.
           destruct Ha as (n, Hn₁).
           rewrite Hn₁.
           apply H.

           symmetry.
           apply nth_c_n; try eassumption .

         eapply order_root_tail_nonneg_any_r; try eassumption .
          intros i HiN.
          rewrite zerop_1st_n_const_coeff_false_iff in Hz.
          destruct i; auto.
          destruct i.
           simpl; rewrite <- Hc, <- Hpol₁; auto.

           remember (S i) as si in |- *; simpl.
           rewrite <- Hc, <- Hpol₁, <- Hns₁.
           subst si.
           do 2 apply le_S_n in HiN.
bbb.

      intros i.
      unfold multiplicity_decreases in Hn.
      rewrite <- Hc, Hr in Hn.
      pose proof (Hn i) as H.
      erewrite <- nth_r_n in H; try eassumption .
      apply Nat.nlt_ge in H.
      symmetry.
      eapply r_le_eq_incl; try eassumption .
       intros j HjN.
bbb.
Check order_root_tail_nonneg.

intros pol ns c pol₁ Hns Hnz₀ Hc Hpol₁.
remember (root_multiplicity acf c (Φq pol ns)) as r eqn:Hr .
symmetry in Hr.
revert pol ns c pol₁ Hns Hnz₀ Hc Hpol₁ Hr.
induction r using all_lt_all; intros.
destruct r.
 exfalso; revert Hr.
 apply multiplicity_neq_0; assumption.

 rename H into IHm.
 destruct (exists_or_not_forall (multiplicity_decreases pol ns)) as [Hn| Hn].
  destruct Hn as (n, Hn).
  unfold multiplicity_decreases in Hn.
  rewrite <- Hc, Hr in Hn.
  remember (nth_pol n pol ns) as poln eqn:Hpoln .
  remember (nth_ns n pol ns) as nsn eqn:Hnsn .
  remember (nth_c n pol ns) as cn eqn:Hcn .
  remember (root_multiplicity acf cn (Φq poln nsn)) as rn eqn:Hrn .
  symmetry in Hrn.
  destruct n.
   simpl in Hpoln, Hnsn, Hcn.
   subst poln nsn cn.
   rewrite <- Hc in Hrn.
   rewrite Hrn in Hr; subst rn.
   exfalso; revert Hn; apply Nat.lt_irrefl.

   remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
   erewrite <- nth_r_n in Hrn; try eassumption ; subst rn.
   apply lowest_i_such_that_ri_lt_r₀ in Hn; [ idtac | subst; auto ].
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
     symmetry in Hnsl.
     destruct nsl as [| ns₂].
      destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
       apply a₀_0_root_0 in H₁.
       exists 0%ps; assumption.

       remember Hnsl as H; clear HeqH.
       rewrite Hpolsi in H.
       simpl in H.
       rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
       apply nth_newton_segments_nil in H; auto.
        destruct H as (j, (Hjn, (Hjz, Hjnz))).
        destruct Hjz as [Hjz| Hjz].
         subst j.
         simpl in Hjnz.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁)).
          contradiction.

          discriminate Hjnz.

         eapply root_when_fin; try eassumption .

        eapply List_hd_in; try eassumption .
        clear H.
        remember Hns as H; clear HeqH.
        eapply next_has_root_0_or_newton_segments in H; try eassumption .
        simpl in H.
        rewrite <- Hc, <- Hpol₁ in H.
        destruct H; auto.

      remember (zerop_1st_n_const_coeff i pol₁ ns₁) as z eqn:Hz .
      symmetry in Hz.
      destruct z.
       apply lowest_zerop_1st_n_const_coeff in Hz.
       destruct Hz as (m, (Hmi, (Hle, Heq))).
       destruct Hle as [Hle| Hle].
        subst m.
        simpl in Heq.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
         exists 0%ps.
         apply a₀_0_root_0; assumption.

         discriminate Heq.

        eapply root_when_fin; try eassumption .

       eapply IHm with (pol := polsi) (ns := nssi) in Hri.
        destruct Hri as (s₁, Hs₁).
        remember (root_head 0 i pol₁ ns₁) as rh.
        remember (ps_monom 1%K (γ_sum 0 i pol₁ ns₁)) as mo.
        exists (rh + mo * s₁)%ps; subst rh mo.
        rewrite apply_nth_pol; auto.
        erewrite nth_pol_n; try eassumption .
        erewrite <- nth_c_n; try eassumption .
        rewrite Hs₁, rng_mul_0_r; reflexivity.

        eapply List_hd_in.
         subst nssi; simpl.
         eapply nth_ns_n; try eassumption .
          rewrite Hc; reflexivity.

          subst polsi; simpl.
          eapply nth_pol_n; try eassumption .
          rewrite Hc; reflexivity.

         intros H; rewrite H in Hnsl; discriminate Hnsl.

        rewrite zerop_1st_n_const_coeff_false_iff in Hz.
        pose proof (Hz i (Nat.le_refl i)) as H.
        rewrite Hpolsi; simpl.
        rewrite <- Hc, <- Hpol₁, <- Hns₁; auto.

        try eassumption .

        erewrite nth_c_n; try eassumption .

        symmetry.
        apply nth_r_n; try eassumption .
        erewrite nth_c_n; try eassumption .

  pose proof (exists_pol_ord R pol) as H.
  destruct H as (m, Hm).
  destruct (ac_zerop 1%K) as [H₀| H₀].
   exists 0%ps.
   unfold ps_pol_apply, apply_poly, apply_lap; simpl.
   remember (al pol₁) as la; clear Heqla.
   destruct la as [| a]; [ reflexivity | simpl ].
   rewrite rng_mul_0_r, rng_add_0_l.
   apply eq_1_0_ps_0; assumption.

   destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
    exists 0%ps.
    apply a₀_0_root_0; assumption.

    remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
    remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
    remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
    remember (order (ps_pol_apply pol₁ s)) as ofs eqn:Hofs .
    symmetry in Hofs.
    destruct ofs as [ofs| ].
     subst s.
     remember (1 # 2 * m * q₀) as η eqn:Hη .
     remember (Z.to_nat (2 * ' m * ' q₀ * Qnum ofs)) as N eqn:HN .
     apply eq_Qbar_eq in Hofs.
     rewrite root_tail_when_r_r with (n := N) in Hofs; try eassumption .
      rewrite Nat.add_0_l in Hofs.
      remember (zerop_1st_n_const_coeff N pol₁ ns₁) as z eqn:Hz .
      symmetry in Hz.
      destruct z.
       unfold root_tail in Hofs.
       rewrite <- Nat.add_1_r in Hofs.
       rewrite zerop_1st_n_const_coeff_true_if in Hofs; auto.
       rewrite rng_mul_0_r, rng_add_0_r in Hofs.
       destruct N.
        exists 0%ps.
        simpl in Hz.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)); [ contradiction | idtac ].
        discriminate Hz.

        apply lowest_zerop_1st_n_const_coeff in Hz.
        destruct Hz as (i, (Hin, (Hji, Hz))).
        destruct Hji as [Hi| Hpi].
         subst i.
         simpl in Hz.
         destruct (ps_zerop R (ps_poly_nth 0 pol₁));
          [ contradiction | idtac ].
         discriminate Hz.

         eapply root_when_fin; try eassumption .

       remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs .
       exists s.
       apply order_inf.
       rewrite apply_nth_pol in Hofs; auto.
       rewrite order_mul in Hofs; auto.
       rewrite ps_monom_order in Hofs; auto.
       remember Σ (i = 0, N), β (nth_ns i pol₁ ns₁) as u eqn:Hu .
       assert (ofs < u) as H.
        subst u.
        assert (∀ i, i ≤ N → η < β (nth_ns i pol₁ ns₁)).
         intros i Hi.
         subst c q₀.
         assert (zerop_1st_n_const_coeff i pol₁ ns₁ = false) as Hz₁.
          rewrite zerop_1st_n_const_coeff_false_iff in Hz.
          apply zerop_1st_n_const_coeff_false_iff.
          intros j Hj.
          apply Hz.
          transitivity i; assumption.

          eapply β_lower_bound_r_const with (n := i) (r := S r); try eassumption .
           apply Nat.lt_0_succ.

           intros j Hji.
           unfold multiplicity_decreases in Hn.
           rewrite Hr in Hn.
           pose proof (Hn j) as H.
           apply Nat.nlt_ge in H.
           erewrite <- nth_r_n in H; try eassumption .
           rename H into Hrj.
           symmetry.
           eapply r_le_eq_incl; try eassumption .
            intros k Hki.
            rewrite zerop_1st_n_const_coeff_false_iff in Hz₁.
            destruct k; try eassumption .
            apply Nat.succ_le_mono in Hki.
            apply Hz₁ in Hki; simpl.
            rewrite <- Hpol₁, <- Hns₁; auto.

            intros k Hki.
            pose proof (Hn k) as H.
            apply Nat.nlt_ge in H.
            erewrite nth_r_n; try eassumption .
bbb.
           Focus 1.
           eapply yyy; try eassumption .
            intros k Hki.
            rewrite zerop_1st_n_const_coeff_false_iff in Hz.
            destruct k.
             simpl.
             Focus 2.
             assert (k ≤ N) as H.
              transitivity i; auto.
              apply Nat.succ_le_mono; auto.

              apply Hz in H.
              simpl.
              rewrite <- Hpol₁, <- Hns₁; auto.

             Focus 2.
             intros k Hki.
bbb.

           2: apply Nat.lt_0_succ.

           Focus 2.
           apply summation_all_lt in H.
           eapply Qle_lt_trans; try eassumption .
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
            rewrite <- Z.mul_1_r in |- * at 1.
            eapply Z.le_trans.
             apply Z.mul_le_mono_nonneg_l with (m := (' Qden ofs)%Z); auto.
             rewrite Z.one_succ.
             apply Zlt_le_succ.
             apply Pos2Z.is_pos.

             apply Z.le_sub_le_add_l.
             rewrite Z.sub_diag; auto.

            apply Zle_neg_pos.

         Focus 2.
         apply Qlt_not_le in H.
         exfalso; apply H.
         apply Qbar.qfin_le_mono.
         rewrite <- Hofs.
         apply Qbar.le_sub_le_add_l.
         rewrite Qbar.sub_diag.
         apply order_pol_apply_nonneg.
          auto.

          Focus 2.
bbb.

  pose proof (exists_pol_ord R pol) as H.
  destruct H as (m, Hm).
  remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
bbb.
  remember (root_tail (m * q₀) 0 pol₁ ns₁) as s eqn:Hs.
  exists s.
  apply order_inf.
  unfold order; simpl.
  remember (ps_pol_apply pol₁ s) as ps₀ eqn:Hps₀ .
  remember (null_coeff_range_length R (ps_terms ps₀) 0) as ofs eqn:Hofs .
  symmetry in Hofs.
  destruct ofs as [ofs| ]; auto; exfalso.
  apply null_coeff_range_length_iff in Hofs.
  unfold null_coeff_range_length_prop in Hofs; simpl in Hofs.
  destruct Hofs as (Hofsi, Hofs).
bbb.



Theorem nth_r_add : ∀ pol ns i j,
  nth_r (i + j) pol ns = nth_r i (nth_pol j pol ns) (nth_ns j pol ns).
Proof.
intros pol ns i j.
revert pol ns j.
induction i; intros.
 simpl.
 apply nth_r_n; auto; symmetry.
 apply nth_c_n; auto.

 rewrite Nat.add_succ_l, <- Nat.add_succ_r; simpl.
 rewrite IHi; simpl.
 f_equal; [ eapply nth_pol_n; try eassumption | idtac ].
 eapply nth_ns_n; try eassumption .
Qed.

Theorem a₀_neq_0 : ∀ pol ns αj,
  ns ∈ newton_segments pol
  → ini_pt ns = (Qnat 0, αj)
  → (ps_poly_nth 0 pol ≠ 0)%ps.
Proof.
intros pol ns αj Hns Hini.
intros H₁.
unfold ps_poly_nth, ps_lap_nth in H₁.
remember Hns as H; clear HeqH.
remember (List.nth 0 (al pol) 0%ps) as jps eqn:Hjps .
eapply ord_coeff_non_zero_in_newt_segm with (hps := jps) in H; try eassumption .
 apply order_inf in H₁.
 unfold order in H₁; simpl in H₁.
 unfold order_coeff in H; simpl in H.
 remember (null_coeff_range_length R (ps_terms jps) 0) as v eqn:Hv .
 destruct v as [v| ].
  discriminate H₁.

  exfalso; apply H; reflexivity.

 left; symmetry; try eassumption .
Qed.

Theorem zerop_1st_n_const_coeff_more : ∀ pol ns n,
  zerop_1st_n_const_coeff n pol ns = false
  → (ps_poly_nth 0 (nth_pol (S n) pol ns) ≠ 0)%ps
  → zerop_1st_n_const_coeff (S n) pol ns = false.
Proof.
intros pol ns n Hz Hn.
rewrite zerop_1st_n_const_coeff_succ2.
rewrite Hz, Bool.orb_false_l.
remember (S n) as sn; simpl; subst sn.
destruct (ps_zerop R (ps_poly_nth 0 (nth_pol (S n) pol ns))); auto.
contradiction.
Qed.

Theorem root_tail_sep_1st_monom_any_r : ∀ pol ns pol₁ ns₁ c m q₀ n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
  → (∀ i, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (root_tail (m * q₀) n pol₁ ns₁ =
       ps_monom (nth_c n pol₁ ns₁) (nth_γ n pol₁ ns₁) +
       ps_monom 1%K (nth_γ n pol₁ ns₁) *
       root_tail (m * q₀) (S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ n r Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hpsi Hri H₀.
remember (zerop_1st_n_const_coeff n pol₁ ns₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁.
 apply zerop_1st_n_const_coeff_false_iff in Hpsi.
 rewrite Hpsi in Hz₁.
 discriminate Hz₁.

 remember (m * q₀)%positive as m₁.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 move Hc₁ before Hns₁.
 move c₁ before c.
 pose proof (Hri 0%nat) as Hr₀; simpl in Hr₀.
 pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
 rewrite <- Hc in Hr₀.
 rewrite <- Hc, <- Hpol₁, <- Hns₁, <- Hc₁ in Hr₁.
 assert (0 < r)%nat as Hrpos by (eapply multiplicity_is_pos; try eassumption ).
 pose proof (Hpsi O (Nat.le_0_l n)) as H; simpl in H.
 rename H into Hnz₁.
 remember Hns₁ as H; clear HeqH.
 eapply r_n_next_ns in H; try eassumption .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember Hns₁ as Hns₁i; clear HeqHns₁i.
 eapply hd_newton_segments in Hns₁i; try eassumption .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 remember Hns as H; clear HeqH.
 eapply next_pol_in_K_1_mq in H; try eassumption .
 rewrite <- Heqm₁ in H.
 rename H into HK₁; move HK₁ before Hns₁i.
 remember (nth_pol n pol₁ ns₁) as poln₁ eqn:Hpoln₁ .
 remember (nth_ns n pol₁ ns₁) as nsn₁ eqn:Hnsn₁ .
 remember (ac_root (Φq poln₁ nsn₁)) as cn₁ eqn:Hcn₁ .
 remember (nth_pol n pol₂ ns₂) as poln₂ eqn:Hpoln₂ .
 remember (nth_ns n pol₂ ns₂) as nsn₂ eqn:Hnsn₂ .
 remember Hns as H; clear HeqH.
 eapply r_n_nth_ns with (poln := poln₁) in H; try eassumption .
 destruct H as (αjn₁, (αkn₁, H)).
 destruct H as (Hinin₁, (Hfinn₁, (Hαjn₁, Hαkn₁))).
 remember Hnsn₁ as H; clear HeqH.
 erewrite nth_ns_n with (c := c) in H; try eassumption .
 erewrite <- nth_pol_n with (c := c) in H; try eassumption .
 rewrite <- Hpoln₁ in H.
 rename H into Hnsn₁h.
 remember Hnsn₁h as H; clear HeqH.
 eapply newton_segments_not_nil in H; try eassumption .
 rename H into Hns₁nz.
 remember Hnsn₁h as H; clear HeqH.
 apply List_hd_in in H; auto.
 rename H into Hnsn₁i.
 pose proof (Hri (S n)) as Hrn₁; simpl in Hrn₁.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hrn₁.
 erewrite nth_r_n in Hrn₁; try eassumption .
 erewrite nth_c_n in Hrn₁; try eassumption .
 rewrite <- Hcn₁ in Hrn₁.
 assert (∀ i, nth_r i pol₁ ns₁ = r) as Hri₁.
  intros i.
  pose proof (Hri (S i)) as H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; auto.

  move Hri₁ before HK₁.
  remember Hns₁i as H; clear HeqH.
  eapply nth_pol_in_K_1_m in H; try eassumption .
  rename H into HKn₁.
  remember (S n) as sn.
  unfold root_tail, ps_monom; simpl.
  do 2 rewrite fold_series_const.
  subst sn.
  rewrite zerop_1st_n_const_coeff_succ2.
  rewrite Hz₁.
  rewrite Bool.orb_false_l.
  simpl.
  rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
  rewrite <- Hpoln₂, <- Hnsn₂.
  rewrite <- Hpoln₁, <- Hnsn₁.
  erewrite nth_c_n; try eassumption .
  rewrite <- Hcn₁.
  destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
   rewrite ps_mul_0_r, ps_add_0_r.
   unfold root_tail_from_cγ_list; simpl.
   rewrite Hinin₁, Hfinn₁; simpl.
   rewrite Hαkn₁; simpl.
   rewrite Qnum_inv_Qnat_sub; auto.
   rewrite Qden_inv_Qnat_sub; auto.
   rewrite Z.mul_1_r, Z.add_0_r, Nat.sub_0_r.
   rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
   do 2 rewrite Pos2Z.inj_mul.
   rewrite Z.div_mul_cancel_r; simpl; auto.
   erewrite αj_m_eq_p_r with (ns₁ := nsn₁); try eassumption .
   rewrite Pos2Z.inj_mul.
   rewrite Z.mul_shuffle0, Zposnat2Znat; auto.
   rewrite <- Zposnat2Znat; auto.
   rewrite <- Z.mul_assoc, Z.div_mul; simpl; auto.
   remember (Qden (nth_γ n pol₁ ns₁)) as d₁ eqn:Hd₁ .
   rewrite ps_adjust_eq with (n := O) (k := d₁); symmetry.
   rewrite ps_adjust_eq with (n := O) (k := m₁); symmetry.
   unfold adjust_ps; simpl.
   do 2 rewrite series_shift_0.
   rewrite series_stretch_const.
   do 2 rewrite Z.sub_0_r.
   rewrite Pos.mul_comm.
   apply mkps_morphism; auto.
    rewrite <- series_stretch_const with (k := d₁).
    apply stretch_morph; auto.
    constructor; intros i; simpl.
    unfold root_tail_series_from_cγ_list; simpl.
    destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₁| H₁].
     exfalso; revert H₁.
     eapply a₀_neq_0; try eassumption .

     rewrite <- Hcn₁.
     erewrite <- nth_ns_n with (c := c₁); try eassumption .
     erewrite <- nth_pol_n with (c := c₁); try eassumption .
     rewrite <- Hpoln₂, <- Hnsn₂.
     destruct i; simpl; [ rewrite Hcn₁; try eassumption  | idtac ].
     destruct (ps_zerop R (ps_poly_nth 0 poln₂)); auto; contradiction.

    subst d₁.
    erewrite nth_γ_n; try eassumption ; simpl.
    rewrite Hαkn₁; simpl.
    rewrite Qnum_inv_Qnat_sub; auto.
    rewrite Qden_inv_Qnat_sub; auto.
    rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
    rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
    do 2 rewrite Pos2Z.inj_mul.
    rewrite Z.mul_assoc.
    apply Z.mul_cancel_r; auto.
    erewrite αj_m_eq_p_r; try eassumption .
    rewrite Zposnat2Znat; auto.
    rewrite Z.mul_assoc, Z.mul_shuffle0.
    reflexivity.

   rename H₂ into Hnzn₂; move Hnzn₂ before Hnsn₂.
   remember Hpoln₂ as H; clear HeqH.
   erewrite <- nth_pol_succ2 with (c := c₁) in H; try eassumption .
   rename H into Hpoln₂₁; move Hpoln₂₁ before Hpoln₂.
   remember Hnsn₂ as H; clear HeqH.
   erewrite <- nth_ns_succ2 with (c := c₁) in H; try eassumption .
   rename H into Hnsn₂₁; move Hnsn₂₁ before Hnsn₂.
   remember Hpsi as H; clear HeqH.
   apply zerop_1st_n_const_coeff_false_iff in H.
   remember Hnzn₂ as HH; clear HeqHH.
   rewrite Hpoln₂₁ in HH.
   apply zerop_1st_n_const_coeff_more in H; auto; clear HH.
   rewrite zerop_1st_n_const_coeff_false_iff in H.
   clear Hpsi; rename H into Hpsi; move Hpsi after Hri.
   remember Hns as H; clear HeqH.
   eapply r_n_nth_ns with (poln := poln₂) (n := S n) in H; try eassumption .
   destruct H as (αjn₂, (αkn₂, H)).
   destruct H as (Hinin₂, (Hfinn₂, (Hαjn₂, Hαkn₂))).
   unfold ps_add, ps_mul; simpl.
   unfold cm; simpl.
   unfold ps_terms_add, ps_ordnum_add; simpl.
   unfold root_tail_from_cγ_list; simpl.
   erewrite nth_γ_n; try eassumption ; simpl.
   rewrite Hinin₁, Hfinn₁, Hinin₂, Hfinn₂; simpl.
   rewrite Hαkn₁, Hαkn₂; simpl.
   rewrite Qnum_inv_Qnat_sub; auto.
   rewrite Qden_inv_Qnat_sub; auto.
   do 2 rewrite Z.add_0_r, Z.mul_1_r.
   rewrite Nat.sub_0_r.
   remember (Qnum αjn₁ * ' Qden αkn₁)%Z as nd₁ eqn:Hnd₁ .
   remember (Qden αjn₁ * Qden αkn₁ * Pos.of_nat r)%positive as dd₁ eqn:Hdd₁ .
   remember (Qnum αjn₂ * ' Qden αkn₂)%Z as nd₂ eqn:Hnd₂ .
   remember (Qden αjn₂ * Qden αkn₂ * Pos.of_nat r)%positive as dd₂ eqn:Hdd₂ .
   rewrite Z.mul_add_distr_r.
   rewrite Pos.mul_comm, Pos2Z.inj_mul, Z.mul_assoc.
   remember (nd₁ * ' m₁ * ' dd₁)%Z as x.
   remember (nd₂ * ' m₁ / ' dd₂ * ' dd₁ * ' dd₁)%Z as y.
   assert (x <= x + y)%Z as Hle; subst x y.
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.div_pos; [ subst nd₂ | apply Pos2Z.is_pos ].
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.lt_le_incl; auto.

    pose proof (Hpsi n (Nat.le_succ_diag_r n)) as H.
    rewrite <- Hpoln₁ in H.
    rename H into Hnzn₁; move Hnzn₁ before Hnsn₁.
    remember Hnsn₂ as H; clear HeqH.
    erewrite nth_ns_n with (c := c₁) in H; try eassumption .
    erewrite <- nth_pol_n with (c := c₁) in H; try eassumption .
    rewrite <- Hpoln₂ in H.
    rename H into Hnsn₂h; move Hnsn₂h before Hαkn₂.
    remember Hnsn₂h as H; clear HeqH.
    eapply newton_segments_not_nil in H; try eassumption .
    rename H into Hns₂nz; move Hns₂nz before Hnzn₂.
    remember Hnsn₂h as H; clear HeqH.
    eapply List_hd_in in H; try eassumption .
    rename H into Hnsn₂i; move Hnsn₂i before Hnsn₂h.
    remember Hpoln₂₁ as H; clear HeqH.
    eapply nth_pol_in_K_1_m in H; try eassumption .
    rename H into HKn₂; move HKn₂ before Hnsn₂i.
    remember (ac_root (Φq poln₂ nsn₂)) as cn₂ eqn:Hcn₂ .
    move Hcn₂ before Hnsn₂.
    pose proof (Hri₁ (S n)) as H.
    erewrite nth_r_n in H; try eassumption .
    erewrite nth_c_n in H; try eassumption .
    rewrite <- Hcn₂ in H.
    rename H into Hrn₂; move Hrn₂ after Hcn₂.
    rewrite Z.min_l; auto.
    rewrite Z.min_r; auto.
    rewrite Z.sub_diag; simpl.
    rewrite Z.add_simpl_l.
    unfold adjust_series at 1.
    rewrite series_shift_0, series_stretch_const.
    rewrite series_stretch_const, series_mul_1_l.
    rewrite Pos.mul_comm.
    rewrite ps_adjust_eq with (n := O) (k := (dd₁ * dd₁)%positive).
    unfold adjust_ps; simpl.
    rewrite series_shift_0, Z.sub_0_r, Pos.mul_assoc.
    apply mkps_morphism; auto.
     rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
     unfold adjust_series; simpl.
     rewrite <- series_stretch_stretch.
     rewrite Z2Nat_inj_mul_pos_r.
     rewrite <- stretch_shift_series_distr.
     rewrite <- series_stretch_const.
     rewrite <- series_stretch_add_distr.
     apply stretch_morph; auto.
     constructor; simpl; intros i.
     rewrite Hnd₂, Hdd₂.
     rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
     rewrite Pos2Z.inj_mul.
     rewrite Z.div_mul_cancel_r; auto.
     erewrite αj_m_eq_p_r with (pol₁ := poln₂); try eassumption .
     rewrite <- Zposnat2Znat; try eassumption .
     rewrite Z.mul_shuffle0, <- Z.mul_assoc.
     rewrite <- Pos2Z.inj_mul.
     rewrite Z.div_mul; auto.
     remember (p_of_m m₁ (γ nsn₂)) as pn₂ eqn:Hpn₂ .
     destruct i.
      simpl.
      destruct (lt_dec 0 (Z.to_nat pn₂)) as [H₁| H₁].
       rewrite rng_add_0_r.
       unfold root_tail_series_from_cγ_list; simpl.
       destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₂| H₂].
        contradiction.

        rewrite Hcn₁; reflexivity.

       exfalso; apply H₁; rewrite Hpn₂.
       rewrite <- Z2Nat.inj_0.
       apply Z2Nat.inj_lt; [ reflexivity | idtac | eapply p_is_pos; try eassumption ].
       apply Z.lt_le_incl.
       eapply p_is_pos; try eassumption .

      remember minus as f; simpl; subst f.
      rewrite rng_add_0_l.
      unfold root_tail_series_from_cγ_list.
      remember (S i) as si.
      remember (si - Z.to_nat pn₂)%nat as id eqn:Hid .
      symmetry in Hid.
      destruct (lt_dec si (Z.to_nat pn₂)) as [H₁| H₁].
       simpl.
       destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₂| H₂].
        contradiction.

        clear H₂.
        rewrite <- Hcn₁.
        erewrite <- nth_pol_n with (c := c₁); try eassumption .
        rewrite <- Hpoln₂.
        erewrite nth_pol_n with (c := c₁) in Hpoln₂; try eassumption .
        erewrite <- nth_ns_n with (c := c₁) (n := n); try eassumption .
        erewrite <- nth_pol_n with (c := c₁) in Hpoln₂; try eassumption .
        rewrite <- Hnsn₂.
        subst si; simpl.
        destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
         contradiction.

         clear H₂.
         erewrite next_pow_eq_p; try eassumption .
         rewrite <- Hpn₂.
         remember (Nat.compare (Z.to_nat pn₂) (S i)) as cmp₁ eqn:Hcmp₁ .
         symmetry in Hcmp₁.
         destruct cmp₁; [ idtac | idtac | reflexivity ].
          apply nat_compare_eq in Hcmp₁.
          rewrite Hcmp₁ in H₁.
          exfalso; revert H₁; apply Nat.lt_irrefl.

          apply nat_compare_lt in Hcmp₁.
          eapply Nat.lt_trans in H₁; try eassumption .
          exfalso; revert H₁; apply Nat.lt_irrefl.

       apply Nat.nlt_ge in H₁.
       symmetry in Hrn₁.
       remember Hnsn₁i as H; clear HeqH.
       eapply q_eq_1_any_r in H; try eassumption .
       rename H into Hqn₁; move Hqn₁ before HKn₁.
       symmetry in Hrn₂.
       remember Hnsn₂i as H; clear HeqH.
       eapply q_eq_1_any_r in H; try eassumption .
       rename H into Hqn₂; move Hqn₂ before HKn₂.
       assert (∀ j, nth_r j poln₁ nsn₁ = r) as Hrin₁.
        intros j; rewrite Hpoln₁, Hnsn₁, <- nth_r_add; apply Hri₁.

        assert (∀ j, nth_r j poln₂ nsn₂ = r) as Hrin₂.
         intros j; rewrite Hpoln₂₁, Hnsn₂₁, <- nth_r_add; apply Hri₁.

         move Hrin₁ before Hqn₁.
         move Hrin₂ before Hqn₂.
         rewrite find_coeff_iter_succ with (r := r); auto; symmetry.
         rewrite find_coeff_iter_succ with (r := r); auto; symmetry.
         remember (S (S si)) as ssi.
         remember (S id) as sid; simpl.
         rewrite <- Hcn₂.
         remember (next_pol poln₂ (β nsn₂) (γ nsn₂) cn₂) as poln₃ eqn:Hpoln₃ .
         remember (List.hd phony_ns (newton_segments poln₃)) as nsn₃.
         rename Heqnsn₃ into Hnsn₃h.
         destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
          contradiction.

          clear H₂.
          destruct id.
           subst sid.
           subst ssi; remember (S si) as ssi; simpl.
           destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₂| H₂].
            contradiction.

            clear H₂; subst si.
            rewrite <- Hcn₁.
            erewrite <- nth_pol_n with (c := c₁); try eassumption .
            rewrite <- Hpoln₂.
            remember Hpoln₂ as H; clear HeqH.
            erewrite nth_pol_n with (c := c₁) in H; try eassumption .
            erewrite <- nth_ns_n with (c := c₁) (poln := poln₁); try eassumption .
            clear H.
            subst ssi; remember (S i) as si; simpl; subst si.
            rewrite <- Hnsn₂, <- Hcn₂, <- Hpoln₃, <- Hnsn₃h.
            destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
             contradiction.

             clear H₂.
             symmetry in Hrn₂.
             erewrite next_pow_eq_p; try eassumption .
             rewrite <- Hpn₂.
             apply Nat.sub_0_le in Hid.
             eapply Nat.le_antisymm in Hid; try eassumption ; rewrite Hid.
             remember (Nat.compare (S i) (S i)) as cmp₁ eqn:Hcmp₁ .
             symmetry in Hcmp₁.
             destruct cmp₁; auto.
              apply nat_compare_lt in Hcmp₁.
              exfalso; revert Hcmp₁; apply Nat.lt_irrefl.

              apply nat_compare_gt in Hcmp₁.
              exfalso; revert Hcmp₁; apply Nat.lt_irrefl.

           subst ssi; remember (S si) as ssi; simpl.
           destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₂| H₂].
            contradiction.

            clear H₂; subst si.
            rewrite <- Hcn₁.
            erewrite <- nth_pol_n with (c := c₁); try eassumption .
            rewrite <- Hpoln₂.
            remember Hpoln₂ as H; clear HeqH.
            erewrite nth_pol_n with (c := c₁) in H; try eassumption .
            erewrite <- nth_ns_n with (c := c₁) (poln := poln₁); try eassumption .
            clear H.
            rewrite <- Hnsn₂.
            subst ssi; remember (S i) as si; simpl.
            rewrite <- Hcn₂, <- Hpoln₃, <- Hnsn₃h.
            destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
             contradiction.

             clear H₂.
             symmetry in Hrn₂.
             erewrite next_pow_eq_p; try eassumption .
             rewrite <- Hpn₂.
             remember (Nat.compare (Z.to_nat pn₂) si) as cmp₁ eqn:Hcmp₁ .
             symmetry in Hcmp₁.
             destruct cmp₁.
              apply nat_compare_eq in Hcmp₁.
              rewrite Hcmp₁, Nat.sub_diag in Hid.
              discriminate Hid.

              apply nat_compare_lt in Hcmp₁.
              replace (Z.to_nat pn₂) with (0 + Z.to_nat pn₂)%nat by auto.
              rewrite next_pow_add.
              apply Nat.add_sub_eq_nz in Hid.
               rewrite Nat.add_comm in Hid.
               rewrite <- Hid.
               rewrite find_coeff_add, Hid.
               subst si sid; symmetry.
               destruct (ps_zerop R (ps_poly_nth 0 poln₃)) as [H₂| H₂].
                remember (S id) as sid; simpl.
                destruct (ps_zerop R (ps_poly_nth 0 poln₃)) as [H₃| H₃].
                 reflexivity.

                 contradiction.

                rename H₂ into Hnzn₃; move Hnzn₃ before Hnsn₃h.
                remember Hnsn₂i as H; clear HeqH.
                eapply next_has_root_0_or_newton_segments in H; try eassumption .
                simpl in H.
                rewrite <- Hcn₂, <- Hpoln₃ in H.
                destruct H as [| H]; [ contradiction | idtac ].
                rename H into Hns₃nz; move Hns₃nz before Hnzn₃.
                remember Hnsn₃h as H; clear HeqH.
                apply List_hd_in in H; auto.
                rename H into Hnsn₃i.
                move Hnsn₃i before Hnsn₃h.
                remember Hpsi as H; clear HeqH.
                apply zerop_1st_n_const_coeff_false_iff in H.
                remember Hnzn₃ as HH; clear HeqHH.
                rewrite Hpoln₃ in HH.
                erewrite <- nth_pol_n with (c := c₁) in HH; try eassumption .
                erewrite <- nth_pol_succ2 with (c := c₁) in HH; try eassumption .
                apply zerop_1st_n_const_coeff_more in H; auto; clear HH.
                rewrite zerop_1st_n_const_coeff_false_iff in H.
                clear Hpsi; rename H into Hpsi; move Hpsi before Hri.
                remember Hns₁i as H; clear HeqH.
                eapply nth_pol_in_K_1_m with (c := c₁) in H; try eassumption .
                remember (S n) as sn in H; simpl in H.
                rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                subst sn.
                erewrite nth_pol_n with (c := c₁) in H; try eassumption .
                rewrite <- Hpoln₃ in H.
                rename H into HKn₃; move HKn₃ before Hns₃nz.
                remember Hns as H; clear HeqH.
                eapply r_n_nth_ns in H; try eassumption .
                remember (S n) as sn in H; simpl in H.
                rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                subst sn.
                erewrite nth_ns_n with (c := c₁) in H; try eassumption .
                rewrite <- Hnsn₃h in H.
                destruct H as (αjn₃, (αkn₃, H)).
                destruct H as (Hinin₃, (Hfinn₃, (Hαjn₃, Hαkn₃))).
                remember (ac_root (Φq poln₃ nsn₃)) as cn₃ eqn:Hcn₃ .
                move Hcn₃ before HKn₃.
                pose proof (Hri₁ (S (S n))) as H.
                remember (S n) as sn in H; simpl in H.
                rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
                subst sn.
                erewrite nth_r_n in H; try eassumption .
                erewrite nth_c_n in H; try eassumption .
                erewrite nth_ns_succ in H; try eassumption .
                erewrite nth_pol_n with (c := c₁) in H; try eassumption .
                rewrite <- Hpoln₃, <- Hnsn₃h, <- Hcn₃ in H.
                rename H into Hrn₃.
                move Hrn₃ before Hcn₃.
                symmetry in Hrn₃.
                remember Hnsn₃i as H; clear HeqH.
                eapply q_eq_1_any_r in H; try eassumption .
                rename H into Hqn₃; move Hqn₃ before HKn₃.
                apply find_coeff_more_iter with (r := r); auto.
                 intros j.
                 pose proof (Hrin₂ (S j)) as H; simpl in H.
                 rewrite <- Hcn₂, <- Hpoln₃, <- Hnsn₃h in H; auto.

                 remember Hinin₂ as H; clear HeqH.
                 eapply p_is_pos with (m := m₁) in H; try eassumption .
                 rewrite <- Hpn₂ in H.
                 apply Z2Nat.inj_lt in H; [ idtac | reflexivity | idtac ].
                  simpl in H.
                  rewrite <- Hid.
                  destruct (Z.to_nat pn₂) as [| pn].
                   exfalso; revert H; apply Nat.lt_irrefl.

                   rewrite Nat.add_succ_r, Nat.add_succ_l.
                   do 2 apply le_n_S.
                   apply Nat.le_add_r.

                  apply Z.lt_le_incl; auto.

               intros H; discriminate H.

              apply nat_compare_gt in Hcmp₁.
              apply Nat.nle_gt in Hcmp₁; contradiction.

     rewrite Pos2Z.inj_mul, Z.mul_assoc.
     apply Z.mul_cancel_r; auto.
     rewrite Z.mul_comm.
     rewrite <- Z.divide_div_mul_exact; auto.
      rewrite Z.mul_comm.
      rewrite Z.div_mul; auto.

      rewrite Hnd₁, Hdd₁.
      rewrite Pos_mul_shuffle0, Z.mul_shuffle0.
      do 2 rewrite Pos2Z.inj_mul.
      apply Z.mul_divide_cancel_r; auto.
      erewrite αj_m_eq_p_r with (ns₁ := nsn₁); try eassumption .
      rewrite <- Zposnat2Znat; try eassumption .
      rewrite Z.mul_shuffle0, <- Z.mul_assoc.
      rewrite <- Pos2Z.inj_mul.
      apply Z.divide_factor_r.
Qed.

Theorem β_lower_bound_r_const : ∀ pol ns pol₁ ns₁ m r η,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → (0 < r)%nat
  → (1 ≠ 0)%K
  → pol₁ = next_pol pol (β ns) (γ ns) (ac_root (Φq pol ns))
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → η = 1 # (2 * m * q_of_m m (γ ns))
  → ∀ n nsn,
    zerop_1st_n_const_coeff n pol₁ ns₁ = false
    → (∀ i, i ≤ S n → nth_r i pol ns = r)
    → nsn = nth_ns n pol₁ ns₁
    → η < β nsn.
Proof.
intros pol ns pol₁ ns₁ m r η Hns Hm Hr H₀ Hpol₁ Hns₁ Hη n nsn Hnz Hri Hnsn.
remember Hns as H; clear HeqH.
rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
eapply r_n_nth_ns in H; try eassumption .
destruct H as (αjn, (αkn, H)).
destruct H as (Hinin, (Hfinn, (Hαjn, Hαkn))).
unfold β.
rewrite Hinin; simpl.
unfold Qnat; simpl.
rewrite rng_mul_0_l, rng_add_0_r.
remember Hpol₁ as H; clear HeqH.
eapply next_pol_in_K_1_mq in H; try eassumption .
rename H into HK₁.
pose proof (Hnz O (Nat.le_0_l n)) as Hnz₀.
simpl in Hnz₀.
assert (0 ≤ S n)%nat as H by apply Nat.le_0_l.
apply Hri in H; simpl in H.
rename H into Hr₀.
assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
apply Hri in H; simpl in H.
rewrite <- Hpol₁, <- Hns₁ in H.
rename H into Hr₁.
remember Hns₁ as H; clear HeqH.
eapply r_n_next_ns in H; try eassumption .
destruct H as (αj₁, (αk₁, H)).
destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
remember Hns₁ as H; clear HeqH.
eapply hd_newton_segments in H; try eassumption .
rename H into Hns₁i.
remember HK₁ as H; clear HeqH.
eapply first_n_pol_in_K_1_m_any_r with (ns := ns₁) in H; try eassumption .
 rename H into HKn.
 remember (nth_pol n pol₁ ns₁) as poln eqn:Hpoln .
 remember Hns₁i as H; clear HeqH.
 eapply nth_in_newton_segments_any_r with (n := n) in H; try eassumption .
  rename H into Hnsni.
  remember HKn as H; clear HeqH.
  eapply pol_ord_of_ini_pt in H; try eassumption .
  rewrite Hη, H.
  rewrite <- Pos.mul_assoc.
  remember (m * q_of_m m (γ ns))%positive as m₁ eqn:Hm₁ .
  unfold mh_of_m.
  erewrite <- qden_αj_is_ps_polord; try eassumption .
  remember (2 * m₁)%positive as m₂.
  unfold Qlt; simpl; subst m₂.
  clear H.
  assert (0 < Qnum αjn * ' m₁ / ' Qden αjn)%Z as H.
   apply Z2Nat.inj_lt; [ reflexivity | idtac | idtac ].
    apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.lt_le_incl; assumption.

    eapply num_m_den_is_pos with (ns := nsn); try eassumption .

   rewrite Pos2Z.inj_mul, Z.mul_assoc.
   replace (' m₁)%Z with (1 * ' m₁)%Z at 1 by reflexivity.
   apply Z.mul_lt_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
   fast_omega H.

  intros i Hin.
  apply Nat.succ_le_mono in Hin.
  apply Hri in Hin; simpl in Hin.
  rewrite <- Hpol₁, <- Hns₁ in Hin.
  try eassumption .

 eapply q_eq_1_any_r with (ns := ns₁); try eassumption .
 rewrite Hr₁; try eassumption .

 intros i Hin.
 apply Nat.succ_le_mono in Hin.
 apply Hri in Hin; simpl in Hin.
 rewrite <- Hpol₁, <- Hns₁ in Hin.
 try eassumption .
Qed.

Theorem k_lt_pol_length : ∀ pol ns k αk,
  ns ∈ newton_segments pol
  → fin_pt ns = (Qnat k, αk)
  → (k < length (al pol))%nat.
Proof.
intros pol ns k αk Hns Hfin.
remember Hns as H; clear HeqH.
unfold newton_segments, points_of_ps_polynom in H.
unfold points_of_ps_lap, points_of_ps_lap_gen in H.
remember (qpower_list 0 (al pol)) as ppl eqn:Hppl .
remember (filter_finite_ord R ppl) as pts.
rename H into Hlch.
remember Hppl as H; clear HeqH.
remember (List.nth k (al pol) 0%ps) as kps eqn:Hkps .
eapply in_pts_in_ppl with (h := Qnat k) (hv := αk) (def := 0%ps) in H; try eassumption .
 simpl in H.
 rewrite Nat2Z.id, Nat.sub_0_r in H.
 rewrite <- Hkps in H.
 destruct H as (Hkppl, Hkord).
 remember Hkppl as H; clear HeqH.
 rewrite Hppl in H.
 apply in_power_list_lt in H.
 rewrite nat_num_Qnat in H; auto.

 eapply in_ppl_in_pts; try eassumption; [ apply Nat.le_0_l | idtac ].
 rewrite Nat.sub_0_r.
 eapply order_in_newton_segment; try eassumption .
 right; apply List.in_or_app.
 right; left; auto.
Qed.

Theorem pol_length_const : ∀ pol ns c pol₁,
  ns ∈ newton_segments pol
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → length (al pol₁) = length (al pol).
Proof.
intros pol ns c pol₁ Hns Hpol₁.
subst pol₁.
unfold next_pol; simpl.
unfold next_lap; simpl.
rewrite length_lap_mul; simpl.
rewrite length_lap_compose_deg_1; reflexivity.
Qed.

Theorem r₁_le_r₀ : ∀ pol ns pol₁,
  ns ∈ newton_segments pol
  → pol₁ = nth_pol 1 pol ns
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → nth_r 1 pol ns ≤ nth_r 0 pol ns.
Proof.
intros pol ns pol₁ Hns Hpol₁ Hnz₀; simpl.
simpl in Hpol₁; rewrite <- Hpol₁.
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
remember Hns₁ as H; clear HeqH.
apply exists_ini_pt_nat_fst_seg in H.
destruct H as (j₁, (αj₁, Hini₁)).
remember Hns₁ as H; clear HeqH.
apply exists_fin_pt_nat_fst_seg in H.
destruct H as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply j_0_k_betw_r₀_r₁ in H; try eassumption .
do 2 rewrite Nat.add_0_r in H.
destruct H as (Hj₁, (Hr₁, (Hr, _))).
transitivity k₁; auto.
Qed.

Theorem r_le_eq_incl : ∀ pol ns r n,
  ns ∈ newton_segments pol
  → nth_r 0 pol ns = r
  → (∀ i, i ≤ n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
  → (∀ i, i ≤ n → r ≤ nth_r i pol ns)
  → (∀ i, i ≤ n → r = nth_r i pol ns).
Proof.
intros pol ns r n Hns Hr₀ Hnz Hri i Hin.
remember Hin as H; clear HeqH.
apply Hri in H.
apply Nat.le_antisymm; auto.
clear H.
revert pol ns r n Hns Hr₀ Hnz Hri Hin.
induction i; intros; [ rewrite <- Hr₀; reflexivity | idtac ].
destruct n; [ exfalso; revert Hin; apply Nat.nle_succ_0 | idtac ].
remember Hin as H; clear HeqH.
apply Hri in H.
simpl in H; simpl.
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
eapply IHi; try eassumption .
 eapply List_hd_in; try eassumption .
 clear H.
 remember Hns as H; clear HeqH.
 eapply next_has_root_0_or_newton_segments in H; try eassumption .
 destruct H as [H₁| H₁].
  assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
  apply Hnz in H; contradiction.

  simpl in H₁.
  rewrite <- Hc, <- Hpol₁ in H₁; auto.

 apply Nat.le_antisymm.
  clear H.
  remember Hns as H; clear HeqH.
  eapply r₁_le_r₀ in H; try eassumption .
   rewrite Hr₀ in H; simpl in H.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; auto.

   clear H.
   assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
   apply Hnz in H; auto.

  clear H.
  assert (1 ≤ S n)%nat as H by apply le_n_S, Nat.le_0_l.
  apply Hri in H; simpl in H.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; auto.

 clear H.
 intros j Hji.
 apply Nat.succ_le_mono in Hji.
 eapply Nat.le_trans in Hin; try eassumption .
 apply Hnz in Hin; simpl in Hin.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin; auto.

 clear H.
 intros j Hji.
 apply Nat.succ_le_mono in Hji.
 eapply Nat.le_trans in Hin; try eassumption .
 apply Hri in Hin; simpl in Hin.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin; auto.
Qed.

Theorem order_root_tail_nonneg_any_r : ∀ pol ns c pol₁ ns₁ m q₀ n r,
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
 rewrite Qnum_inv_Qnat_sub; auto.
 rewrite Qden_inv_Qnat_sub; auto.
 rewrite Z.add_0_r, Z.mul_1_r.
 remember (root_tail_series_from_cγ_list m₁ pol₁ ns₁) as t.
 remember (null_coeff_range_length R {| terms := t |} 0) as v eqn:Hv .
 symmetry in Hv.
 destruct v; [ idtac | constructor ].
 apply Qbar.qfin_le_mono.
 rewrite Nat.sub_0_r.
 rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
 rewrite Pos2Z.inj_mul; auto.
 rewrite Z.div_mul_cancel_r; auto.
 erewrite αj_m_eq_p_r with (ns₁ := ns₁); try eassumption .
 rewrite Z.mul_shuffle0.
 rewrite <- Zposnat2Znat; auto.
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
 rewrite Z.div_mul; auto.
 unfold Qle; simpl.
 rewrite Z.mul_1_r.
 apply Z.add_nonneg_nonneg; [ idtac | apply Nat2Z.is_nonneg ].
 apply Z.lt_le_incl.
 eapply p_is_pos; try eassumption .

 simpl in Hz₁; simpl.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
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
   eapply q_eq_1_any_r with (pol := pol₁); try eassumption .

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

End theorems.
