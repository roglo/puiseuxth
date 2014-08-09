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
Require Import Puiseux.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Lemma root_tail_sep_1st_monom : ∀ pol ns pol₁ ns₁ c m q₀ n,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
  → (root_tail (m * q₀) n pol₁ ns₁ =
       ps_monom (nth_c n pol₁ ns₁) (nth_γ n pol₁ ns₁) +
       ps_monom 1%K (nth_γ n pol₁ ns₁) *
       root_tail (m * q₀) (S n) pol₁ ns₁)%ps.
Proof.
(* à nettoyer *)
intros pol ns pol₁ ns₁ c m q₀ n Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ Hpsi.
remember (m * q₀)%positive as m₁.
remember (S n) as sn.
unfold root_tail, ps_monom; simpl.
rewrite fold_series_const.
rewrite fold_series_const.
remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
remember (nth_pol n pol₁ ns₁) as poln₁ eqn:Hpoln₁ .
remember (nth_pol n pol₂ ns₂) as poln₂ eqn:Hpoln₂ .
subst sn.
rewrite zerop_1st_n_const_coeff_succ2.
remember (zerop_1st_n_const_coeff n pol₁ ns₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁.
 apply zerop_1st_n_const_coeff_false_iff in Hpsi.
 rewrite Hpsi in Hz₁.
 discriminate Hz₁.

 rewrite Bool.orb_false_l.
 pose proof (Hpsi O (Nat.le_0_l n)) as H; simpl in H.
 rename H into Hnz₁.
 remember Hns₁ as H; clear HeqH.
 eapply r_1_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (_, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
 remember Hns₁ as Hns₁i; clear HeqHns₁i.
 eapply hd_newton_segments in Hns₁i; eauto .
 remember Hr as H; clear HeqH.
 eapply multiplicity_1_remains in H; eauto .
 rename H into Hr₁.
 remember (nth_ns n pol₁ ns₁) as nsn₁ eqn:Hnsn₁ .
 simpl.
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
 rewrite <- Hpoln₂.
 remember (nth_ns n pol₂ ns₂) as nsn₂ eqn:Hnsn₂.
 destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
  rewrite ps_mul_0_r, ps_add_0_r.
  unfold root_tail_from_cγ_list; simpl.
  remember Hns as H; clear HeqH.
  eapply r_1_nth_ns with (poln := poln₁) in H; eauto .
  destruct H as (αjn₁, (αkn₁, H)).
  destruct H as (_, (Hinin₁, (Hfinn₁, (Hαjn₁, Hαkn₁)))).
  rewrite Hinin₁, Hfinn₁; simpl.
  rewrite Hαkn₁; simpl.
  rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r, Pos2Z.inj_mul.
  rewrite Z.mul_shuffle0, Z.div_mul_cancel_r; auto.
  erewrite nth_γ_n; eauto ; simpl.
  rewrite Hαkn₁; simpl.
  rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
  rewrite ps_adjust_eq with (n := O) (k := (Qden αjn₁ * Qden αkn₁)%positive).
  symmetry.
  rewrite ps_adjust_eq with (n := O) (k := m₁); symmetry.
  unfold adjust_ps; simpl.
  do 2 rewrite series_shift_0.
  rewrite series_stretch_const.
  rewrite Z.sub_0_r.
  rewrite Pos2Z.inj_mul, Z.mul_assoc.
  rewrite Z_div_mul_swap.
   rewrite Z.div_mul; auto.
   rewrite Z.mul_shuffle0, Z.sub_0_r.
   apply mkps_morphism; eauto .
    constructor; intros i; simpl.
    destruct (zerop (i mod Pos.to_nat (Qden αjn₁ * Qden αkn₁))) as [H₃| H₃].
     apply Nat.mod_divides in H₃; auto.
     destruct H₃ as (d, Hd).
     rewrite Nat.mul_comm in Hd; rewrite Hd in |- * at 1.
     rewrite Nat.div_mul; auto.
     destruct (zerop i) as [H₃| H₃].
      subst i.
      apply Nat.mul_eq_0_l in H₃; auto.
      subst d; simpl.
      unfold root_tail_series_from_cγ_list; simpl.
      destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₃| H₃].
       pose proof (Hpsi n (Nat.le_refl n)) as H.
       rewrite <- Hpoln₁ in H.
       contradiction.

       symmetry.
       apply nth_c_root; auto.

      unfold root_tail_series_from_cγ_list; simpl.
      destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [| H₄]; auto.
      clear H₄.
      destruct d.
       exfalso; subst i; revert H₃; apply Nat.lt_irrefl.

       remember (ac_root (Φq poln₁ nsn₁)) as cn₁ eqn:Hcn₁ .
       remember (next_pol poln₁ (β nsn₁) (γ nsn₁) cn₁) as poln₁s eqn:Hpoln₁s .
       erewrite nth_pol_n with (ns₁ := ns₁) in Hpoln₁s; eauto .
       rewrite <- Hpoln₂ in Hpoln₁s; subst poln₁s.
       remember (List.hd phony_ns (newton_segments poln₂)) as nsn₂'.
       simpl.
       destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₄| H₄]; auto.
       contradiction.

     destruct (zerop i) as [H₄| H₄]; auto.
     subst i; rewrite Nat.mod_0_l in H₃; auto.
     exfalso; revert H₃; apply Nat.lt_irrefl.

    apply Pos.mul_comm; reflexivity.

   remember Hns₁i as H; clear HeqH.
   eapply nth_in_newton_segments in H; eauto .
   rename H into Hnsn₁i.
   eapply den_αj_divides_num_αj_m with (ns := nsn₁); eauto .
   eapply lap_forall_nth with (ns := ns₁); eauto .
    rewrite Heqm₁.
    eapply q_eq_1 with (ns := ns); eauto .
    eapply next_pol_in_K_1_mq with (ns := ns); eauto .

    rewrite Heqm₁.
    eapply next_pol_in_K_1_mq with (ns := ns); eauto .

  remember Hns as H; clear HeqH.
  eapply r_1_nth_ns with (poln := poln₁) in H; eauto .
  destruct H as (αjn₁, (αkn₁, H)).
  destruct H as (_, (Hinin₁, (Hfinn₁, (Hαjn₁, Hαkn₁)))).
  assert (ps_poly_nth 0 pol₂ ≠ 0)%ps as Hps₂.
   destruct n; [ simpl in Hpoln₂; subst poln₂; assumption | idtac ].
   assert (1 ≤ S n)%nat as H by fast_omega .
   apply Hpsi in H; simpl in H.
   rewrite <- Hc₁, <- Hpol₂ in H; assumption.

   assert (ns₂ ∈ newton_segments pol₂) as Hns₂i.
    remember Hns₂ as H; clear HeqH.
    eapply r_1_next_ns with (pol := pol₁) in H; eauto .
    destruct H as (αj₂, (αk₂, H)).
    destruct H as (Hoth₂, (Hini₂, (Hfin₂, (Hαj₂, Hαk₂)))).
    eapply hd_newton_segments; eauto .

    remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
    assert (root_multiplicity acf c₂ (Φq pol₂ ns₂) = 1%nat) as Hr₂.
     eapply multiplicity_1_remains with (ns := ns₁); eauto .

     assert (ps_lap_forall (λ a, in_K_1_m a m₁) (al pol₁)) as Hps₁.
      rewrite Heqm₁.
      eapply next_pol_in_K_1_mq with (ns := ns); eauto .

      assert (q_of_m m₁ (γ ns₁) = 1%positive) as Hq₁.
       rewrite Heqm₁.
       eapply q_eq_1 with (ns := ns); eauto .
       eapply next_pol_in_K_1_mq with (ns := ns); eauto .

       assert (q_of_m m₁ (γ ns₂) = 1%positive) as Hq₂.
        replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
        eapply q_eq_1 with (ns := ns₁); eauto .
        eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .

        rename Hps₂ into Hnz₂.
        assert (ps_lap_forall (λ a, in_K_1_m a m₁) (al pol₂)) as Hps₂.
         replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
         eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .

         assert (ps_lap_forall (λ a, in_K_1_m a m₁) (al poln₂)) as Hpsn₂.
          eapply lap_forall_nth with (ns := ns₂); eauto .
          intros i Hin.
          destruct (eq_nat_dec i n) as [H₃| H₃].
           subst i.
           rewrite <- Hpoln₂; assumption.

           apply le_neq_lt in Hin; auto.
           apply Hpsi in Hin.
           simpl in Hin.
           rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
           assumption.

          remember Hns as H; clear HeqH.
          eapply r_1_nth_ns with (poln := poln₂) (n := S n) in H; eauto .
           destruct H as (αjn₂, (αkn₂, H)).
           destruct H as (_, (Hinin₂, (Hfinn₂, (Hαjn₂, Hαkn₂)))).
           simpl in Hinin₂, Hfinn₂.
           rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hinin₂, Hfinn₂.
           rewrite <- Hnsn₂ in Hinin₂, Hfinn₂.
           unfold ps_add, ps_mul; simpl.
           unfold cm; simpl.
           unfold ps_terms_add, ps_ordnum_add; simpl.
           unfold root_tail_from_cγ_list; simpl.
           rewrite Hinin₁, Hfinn₁, Hinin₂, Hfinn₂; simpl.
           rewrite Hαkn₁, Hαkn₂; simpl.
           rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
           erewrite nth_γ_n; eauto ; simpl.
           rewrite Hαkn₁; simpl.
           rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
           rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
           remember (Qnum αjn₁ * ' Qden αkn₁)%Z as nd₁ eqn:Hnd₁ .
           remember (Qden αjn₁ * Qden αkn₁)%positive as dd₁ eqn:Hdd₁ .
           remember (Qnum αjn₂ * ' Qden αkn₂)%Z as nd₂ eqn:Hnd₂ .
           remember (Qden αjn₂ * Qden αkn₂)%positive as dd₂ eqn:Hdd₂ .
           remember (nd₂ * ' m₁ / ' dd₂ * ' dd₁)%Z as x.
           rewrite Hnd₂, Hdd₂, Hdd₁ in Heqx.
           rewrite Pos2Z.inj_mul, Z.mul_shuffle0 in Heqx.
           rewrite Z.div_mul_cancel_r in Heqx; auto.
           rewrite <- Hdd₁ in Heqx.
           remember (Qnum αjn₂ * ' m₁ / ' Qden αjn₂)%Z as nmd₂ eqn:Hnmd₂ .
           subst x.
           rewrite Z.min_l.
            rewrite Z.min_r.
             rewrite Z.sub_diag; simpl.
             rewrite series_stretch_const.
             rewrite series_mul_1_l.
             rewrite Z.mul_add_distr_r.
             rewrite Pos2Z.inj_mul.
             rewrite Z.mul_shuffle0.
             rewrite Z.mul_assoc.
             rewrite Z.add_simpl_l.
             unfold adjust_series at 1.
             rewrite series_shift_0, series_stretch_const.
             rewrite ps_adjust_eq with (n := O) (k := (dd₁ * dd₁)%positive).
             unfold adjust_ps; simpl.
             rewrite series_shift_0, Z.sub_0_r.
             rewrite Pos2Z.inj_mul, Z.mul_assoc.
             rewrite Z_div_mul_swap.
              rewrite Z.div_mul; auto.
              rewrite Z.mul_shuffle0.
              apply mkps_morphism; auto.
               unfold adjust_series; simpl.
               rewrite <- series_stretch_stretch.
               rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
               rewrite Z2Nat_inj_mul_pos_r.
               rewrite <- stretch_shift_series_distr.
               rewrite
                <- series_stretch_const with (k := (dd₁ * dd₁)%positive).
               rewrite <- series_stretch_add_distr.
               apply stretch_morph; auto.
               constructor; intros i; simpl.
               assert (nsn₂ ∈ newton_segments poln₂) as Hnsn₂i.
                eapply hd_newton_segments; eauto .
                subst nsn₂.
                eapply nth_ns_n with (c := c₁); eauto .
                erewrite nth_pol_n with (c₁ := c₁); eauto .

                unfold root_tail_series_from_cγ_list; simpl.
                destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₃| H₃].
                 pose proof (Hpsi n (Nat.le_refl n)) as H.
                 rewrite <- Hpoln₁ in H.
                 contradiction.

                 clear H₃.
                 destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₃| H₃].
                  contradiction.

                  clear H₃.
                  remember (ac_root (Φq poln₁ nsn₁)) as cn₁ eqn:Hcn₁ .
                  remember (next_pol poln₁ (β nsn₁) (γ nsn₁) cn₁) as poln₁s
                   eqn:Hpoln₁s .
                  erewrite nth_pol_n with (ns₁ := ns₁) in Hpoln₁s; eauto .
                  rewrite <- Hpoln₂ in Hpoln₁s; subst poln₁s.
                  destruct i.
                   simpl.
                   destruct (lt_dec 0 (Z.to_nat nmd₂)) as [H₃| H₃].
                    rewrite rng_add_0_r; subst cn₁; symmetry.
                    apply nth_c_root; auto.

                    exfalso; apply H₃; subst nmd₂.
                    eapply num_m_den_is_pos with (ns := nsn₂) (pol := poln₂);
                     eauto .

                   remember Hnsn₂ as H; clear HeqH.
                   erewrite nth_ns_n with (c := c₁) in H; eauto .
                   erewrite nth_pol_n with (c₁ := c₁) in H; eauto .
                   rewrite <- Hpoln₂ in H.
                   rename H into Hnsn₂p.
                   rewrite <- Hnsn₂p.
                   remember (ac_root (Φq poln₂ nsn₂)) as cn₂ eqn:Hcn₂ .
                   remember (next_pol poln₂ (β nsn₂) (γ nsn₂) cn₂) as poln₃.
                   remember
                    (List.hd phony_ns (newton_segments poln₃)) as nsn₃.
                   remember (find_coeff (S i)) as f; simpl; subst f.
                   rewrite rng_add_0_l.
                   destruct (lt_dec (S i) (Z.to_nat nmd₂)) as [H₃| H₃].
                    remember (S i) as si.
                    unfold next_pow; simpl.
                    rewrite Hinin₂, Hfinn₂; simpl.
                    rewrite Hαkn₂; simpl.
                    rewrite Z.add_0_r, Z.mul_1_r.
                    do 2 rewrite Pos.mul_1_r.
                    rewrite Pos2Z.inj_mul, Z.mul_shuffle0.
                    rewrite Z.div_mul_cancel_r; auto.
                    subst si; simpl.
                    destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₄| H₄];
                     auto.
                    clear H₄.
                    rewrite <- Hnmd₂.
                    remember (Nat.compare (Z.to_nat nmd₂) (S i)) as cmp₂
                     eqn:Hcmp₂ .
                    symmetry in Hcmp₂.
                    destruct cmp₂; auto.
                     apply nat_compare_eq in Hcmp₂.
                     rewrite Hcmp₂ in H₃.
                     exfalso; revert H₃; apply Nat.lt_irrefl.

                     apply nat_compare_lt in Hcmp₂.
                     exfalso; fast_omega H₃ Hcmp₂.

                    apply Nat.nlt_ge in H₃.
                    remember (S i) as si.
                    unfold next_pow at 1; simpl.
                    rewrite Hinin₂, Hfinn₂; simpl.
                    rewrite Hαkn₂; simpl.
                    rewrite Z.add_0_r, Z.mul_1_r.
                    do 2 rewrite Pos.mul_1_r.
                    rewrite Pos2Z.inj_mul, Z.mul_shuffle0.
                    rewrite Z.div_mul_cancel_r; auto.
                    rewrite <- Hnmd₂.
                    subst si; simpl.
                    destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₄| H₄];
                     auto.
                     contradiction.

                     clear H₄.
                     remember (Nat.compare (Z.to_nat nmd₂) (S i)) as cmp₂
                      eqn:Hcmp₂ .
                     symmetry in Hcmp₂.
                     destruct cmp₂; auto.
                      apply nat_compare_eq in Hcmp₂.
                      rewrite Hcmp₂.
                      rewrite Nat.sub_diag; simpl.
                      symmetry.
                      rewrite Hcn₂; reflexivity.

                      apply nat_compare_lt in Hcmp₂.
                      rewrite <- Hcn₂, <- Heqpoln₃, <- Heqnsn₃.
                      remember (Z.to_nat nmd₂) as x eqn:Hx .
                      symmetry in Hx.
                      destruct x.
                       exfalso; symmetry in Hx; revert Hx.
                       apply lt_0_neq.
                       subst nmd₂.
                       eapply num_m_den_is_pos with (ns := nsn₂); eauto .

                       remember (i - x)%nat as ix.
                       destruct ix;
                        [ exfalso; fast_omega Heqix Hcmp₂ | idtac ].
                       replace (S x) with (0 + S x)%nat by fast_omega .
                       rewrite next_pow_add.
                       replace (S i) with (S ix + S x)%nat
                        by fast_omega Heqix.
                       rewrite find_coeff_add.
                       destruct i; [ exfalso; fast_omega Heqix | idtac ].
                       simpl.
                       destruct (ps_zerop R (ps_poly_nth 0 poln₃))
                        as [H₄| H₄]; auto.
                       remember
                        (Nat.compare (next_pow 0 nsn₃ m₁) (S ix)) as cmp₃
                        eqn:Hcmp₃ .
                       symmetry in Hcmp₃.
                       destruct cmp₃; auto.
                       remember (ac_root (Φq poln₃ nsn₃)) as cn₃ eqn:Hcn₃ .
                       remember
                        (next_pol poln₃ (β nsn₃) (γ nsn₃) cn₃) as poln₄
                        eqn:Hpoln₄ .
                       remember
                        (List.hd phony_ns (newton_segments poln₄)) as nsn₄
                        eqn:Hnsn₄ .
                       remember (next_pow 0 nsn₃ m₁) as np₁ eqn:Hnp₁ .
                       symmetry.
                       rewrite <- Nat.add_1_r.
                       symmetry.
                       rewrite Nat.add_1_r.
                       rewrite Heqix.
                       rewrite <- find_coeff_add with (dp := x).
                       replace (S i - x + x)%nat with 
                        (S i) by fast_omega Hcmp₂.
                       symmetry.
                       rewrite <- find_coeff_add with (dp := x).
                       replace (S i - x + x)%nat with 
                        (S i) by fast_omega Hcmp₂.
                       rewrite <- next_pow_add.
                       symmetry.
                       rewrite <- Nat.add_1_r.
                       replace ix with (S i - S x)%nat by fast_omega Heqix.
                       remember Heqnsn₃ as H; clear HeqH.
                       eapply r_1_next_ns with (pol := poln₂) in H; eauto .
                        destruct H as (αjn₃, (αkn₃, H)).
                        destruct H as (_, (Hinin₃, (Hfinn₃, (Hαjn₃, Hαkn₃)))).
                        assert (0 < np₁)%nat as Hnp₁p.
                         subst np₁.
                         unfold next_pow; simpl.
                         rewrite Hinin₃, Hfinn₃; simpl.
                         rewrite Hαkn₃; simpl.
                         rewrite Z.add_0_r, Z.mul_1_r.
                         do 2 rewrite Pos.mul_1_r.
                         rewrite Pos2Z.inj_mul, Z.mul_shuffle0.
                         rewrite Z.div_mul_cancel_r; auto.
                         eapply
                          num_m_den_is_pos with (ns := nsn₃) (pol := poln₃);
                          eauto .
                          eapply hd_newton_segments; eauto .

                          replace m₁ with (m₁ * 1)%positive
                           by apply Pos.mul_1_r.
                          eapply next_pol_in_K_1_mq with (ns := nsn₂); eauto .
                          symmetry.
                          replace m₁ with (m₁ * 1)%positive
                           by apply Pos.mul_1_r.
                          eapply q_eq_1 with (pol := poln₁) (ns := nsn₁);
                           eauto .
                           eapply hd_newton_segments; eauto .
                           rewrite Hnsn₁.
                           eapply nth_ns_n with (c := c); eauto .
                           erewrite nth_pol_n with (c₁ := c); eauto .

                           eapply lap_forall_nth with (ns := ns₁); eauto .

                           erewrite
                            nth_pol_n with (pol₁ := pol₁) (ns₁ := ns₁); 
                            eauto .
                           eapply lap_forall_nth with (ns := ns₂); eauto .
                            eapply q_eq_1 with (ns := ns₁); eauto .
                            eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .

                            clear i H₃ Hcmp₂ Heqix.
                            intros i Hisn.
                            destruct (eq_nat_dec i n) as [H₅| H₅].
                             subst i; simpl.
                             rewrite <- Hpoln₂.
                             assumption.

                             apply le_neq_lt in Hisn; auto.
                             apply Hpsi in Hisn; simpl in Hisn.
                             rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                             assumption.

                            eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .

                           eapply
                            multiplicity_1_remains_in_nth with (ns := ns);
                            eauto .

                           erewrite nth_pol_n with (c₁ := c₁); eauto .
                           rewrite <- Hpoln₂.
                           assumption.

                           erewrite nth_pol_n with (c₁ := c₁) (pol₂ := pol₂);
                            eauto .
                           rewrite <- Hpoln₂; assumption.

                         destruct (eq_nat_dec i x) as [H₅| H₅].
                          subst i.
                          rewrite minus_Sn_n in Heqix.
                          apply Nat.succ_inj in Heqix.
                          rewrite Nat.sub_diag; subst ix.
                          apply nat_compare_lt in Hcmp₃.
                          exfalso; fast_omega Hcmp₃ Hnp₁p.

                          eapply
                           find_coeff_step
                            with
                              (ns := nsn₃)
                              (pol := poln₃)
                              (dp := (np₁ - 1)%nat); 
                           eauto .
                           eapply hd_newton_segments; eauto .

                           replace m₁ with (m₁ * 1)%positive
                            by apply Pos.mul_1_r.
                           eapply next_pol_in_K_1_mq with (ns := nsn₂); eauto .
                           symmetry.
                           replace m₁ with (m₁ * 1)%positive
                            by apply Pos.mul_1_r.
                           eapply q_eq_1 with (pol := poln₁) (ns := nsn₁);
                            eauto .
                            eapply hd_newton_segments; eauto .
                            rewrite Hnsn₁.
                            eapply nth_ns_n with (c := c); eauto .
                            erewrite nth_pol_n with (c₁ := c); eauto .

                            eapply lap_forall_nth with (ns := ns₁); eauto .

                            erewrite
                             nth_pol_n with (pol₁ := pol₁) (ns₁ := ns₁);
                             eauto .
                            eapply lap_forall_nth with (ns := ns₂); eauto .
                             eapply q_eq_1 with (ns := ns₁); eauto .
                             eapply next_pol_in_K_1_mq with (ns := ns₁);
                              eauto .

                             clear i H₅ H₃ Hcmp₂ Heqix.
                             intros i Hisn.
                             destruct (eq_nat_dec i n) as [H₅| H₅].
                              subst i; simpl.
                              rewrite <- Hpoln₂.
                              assumption.

                              apply le_neq_lt in Hisn; auto.
                              apply Hpsi in Hisn; simpl in Hisn.
                              rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                              assumption.

                             eapply next_pol_in_K_1_mq with (ns := ns₁);
                              eauto .

                            eapply
                             multiplicity_1_remains_in_nth with (ns := ns);
                             eauto .

                            erewrite nth_pol_n with (c₁ := c₁); eauto .
                            rewrite <- Hpoln₂.
                            assumption.

                            erewrite nth_pol_n with (c₁ := c₁) (pol₂ := pol₂);
                             eauto .
                            rewrite <- Hpoln₂; assumption.

                           replace m₁ with (m₁ * 1)%positive
                            by apply Pos.mul_1_r.
                           eapply q_eq_1 with (pol := poln₂) (ns := nsn₂);
                            eauto .
                            eapply next_pol_in_K_1_mq with (ns := nsn₂);
                             eauto .
                            symmetry.
                            replace m₁ with (m₁ * 1)%positive
                             by apply Pos.mul_1_r.
                            eapply q_eq_1_nth with (ns := ns₁); eauto .
                             eapply next_pol_in_K_1_mq with (ns := ns₁);
                              eauto .

                             clear i H₅ H₃ Hcmp₂ Heqix.
                             intros i Hisn.
                             destruct (eq_nat_dec i n) as [H₅| H₅].
                              subst i; simpl.
                              rewrite <- Hpoln₂.
                              assumption.

                              apply le_neq_lt in Hisn; auto.
                              apply Hpsi in Hisn; simpl in Hisn.
                              rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                              assumption.

                            eapply
                             multiplicity_1_remains_in_nth with (ns := ns₁);
                             eauto .
                            clear i H₅ H₃ Hcmp₂ Heqix.
                            intros i Hisn.
                            destruct (eq_nat_dec i n) as [H₅| H₅].
                             subst i; simpl.
                             rewrite <- Hpoln₂.
                             assumption.

                             apply le_neq_lt in Hisn; auto.
                             apply Hpsi in Hisn; simpl in Hisn.
                             rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                             assumption.

                           eapply multiplicity_1_remains with (ns := nsn₂);
                            eauto .
                           eapply
                            multiplicity_1_remains_in_nth with (ns := ns₁);
                            eauto .
                           clear i H₅ H₃ Hcmp₂ Heqix.
                           intros i Hisn.
                           destruct (eq_nat_dec i n) as [H₅| H₅].
                            subst i; simpl.
                            rewrite <- Hpoln₂.
                            assumption.

                            apply le_neq_lt in Hisn; auto.
                            apply Hpsi in Hisn; simpl in Hisn.
                            rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                            assumption.

                           split; [ fast_omega  | idtac ].
                           fast_omega H₅ Hcmp₂.

                           fast_omega Hnp₁p.

                           replace (S x + (np₁ - 1))%nat with (np₁ + x)%nat ;
                            auto.
                           fast_omega Hnp₁p.

                        eapply multiplicity_1_remains_in_nth with (ns := ns₁);
                         eauto .
                        clear i H₃ Hcmp₂ Heqix.
                        intros i Hisn.
                        destruct (eq_nat_dec i n) as [H₅| H₅].
                         subst i; simpl.
                         rewrite <- Hpoln₂.
                         assumption.

                         apply le_neq_lt in Hisn; auto.
                         apply Hpsi in Hisn; simpl in Hisn.
                         rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                         assumption.

                      apply nat_compare_gt in Hcmp₂.
                      apply Nat.nle_gt in Hcmp₂; contradiction.

               rewrite Pos.mul_comm, Pos.mul_assoc; reflexivity.

              subst dd₁ nd₁.
              rewrite Pos2Z.inj_mul.
              rewrite Z.mul_shuffle0.
              apply Z.mul_divide_cancel_r; auto.
              eapply den_αj_divides_num_αj_m with (ns := nsn₁) (pol := poln₁);
               eauto .
               eapply hd_newton_segments; eauto .
               rewrite Hnsn₁.
               eapply nth_ns_n with (c := c); eauto .
               rewrite Hpoln₁.
               symmetry.
               eapply nth_pol_n with (c₁ := c); eauto .

               eapply lap_forall_nth with (ns := ns₁); eauto .

             rewrite Pos2Z.inj_mul, Z.mul_add_distr_r.
             rewrite Z.mul_assoc, Z.mul_shuffle0.
             apply Z.le_sub_le_add_l.
             rewrite Z.sub_diag.
             apply Z.mul_nonneg_nonneg; auto.
             apply Z.mul_nonneg_nonneg; auto.
             subst nmd₂.
             apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
             apply Z.mul_nonneg_nonneg; auto.
             apply Z.lt_le_incl; assumption.

            rewrite Pos2Z.inj_mul, Z.mul_add_distr_r.
            rewrite Z.mul_assoc, Z.mul_shuffle0.
            apply Z.le_sub_le_add_l.
            rewrite Z.sub_diag.
            apply Z.mul_nonneg_nonneg; auto.
            apply Z.mul_nonneg_nonneg; auto.
            subst nmd₂.
            apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
            apply Z.mul_nonneg_nonneg; auto.
            apply Z.lt_le_incl; assumption.

           intros i Hisn.
           destruct (eq_nat_dec i (S n)) as [H₃| H₃].
            subst i; simpl.
            rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
            rewrite <- Hpoln₂; assumption.

            apply le_neq_lt in Hisn; auto.
            apply Nat.succ_le_mono in Hisn.
            clear H₃.
            revert i Hisn; assumption.

           simpl.
           rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
           assumption.
Qed.

Lemma zerop_1st_n_const_coeff_true_if : ∀ pol ns b,
  zerop_1st_n_const_coeff b pol ns = true
  → ∀ n, zerop_1st_n_const_coeff (b + n) pol ns = true.
Proof.
intros pol ns b Hz n.
revert pol ns Hz n.
induction b; intros.
 simpl.
 revert pol ns Hz.
 induction n; intros; auto.
 simpl in Hz; simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
 discriminate Hz.

 simpl in Hz; simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
Qed.

Lemma root_head_from_cγ_list_succ : ∀ pol ns b n i,
  zerop_1st_n_const_coeff (b + i) pol ns = false
  → (root_head_from_cγ_list pol ns b (S n) i =
     root_head_from_cγ_list pol ns b n i +
      (if zerop_1st_n_const_coeff (b + i + n) pol ns then 0
       else
         ps_monom (nth_c (b + i + S n) pol ns)
           (γ_sum b (i + S n) pol ns)))%ps.
Proof.
(* à nettoyer *)
intros pol ns b n i Hz; simpl.
destruct (ps_zerop R (ps_poly_nth 0 (nth_pol (b + i) pol ns))) as [H₁| H₁].
 eapply zerop_1st_n_const_coeff_false_iff with (i := (b + i)%nat) in Hz.
  contradiction.

  apply Nat.le_refl.

 revert b i Hz H₁.
 induction n; intros; simpl.
  rewrite Nat.add_0_r.
bbb.
  do 2 rewrite rng_add_0_r.
  rewrite Hz, <- Nat.add_1_r, Nat.add_assoc.
  reflexivity.

  rewrite <- rng_add_assoc; simpl.
  apply rng_add_compat_l; simpl.
  destruct (ps_zerop R (ps_poly_nth 0 (nth_pol (b + i) pol ns))) as [H₂| H₂].
   contradiction.

   clear H₂.
   remember (zerop_1st_n_const_coeff (b + i + S n) pol ns) as z₁ eqn:Hz₁ .
   symmetry in Hz₁.
   destruct (ps_zerop R (ps_poly_nth 0 (nth_pol (b + S i) pol ns)))
    as [H₂| H₂].
    rewrite rng_add_0_r.
    destruct z₁.
     rewrite rng_add_0_r.
     destruct n.
      simpl.
      rewrite rng_add_0_r.
      reflexivity.

      simpl.
      destruct (ps_zerop R (ps_poly_nth 0 (nth_pol (b + S i) pol ns)))
       as [H₃| H₃].
       rewrite rng_add_0_r.
       reflexivity.

       contradiction.

     eapply zerop_1st_n_const_coeff_false_iff with (i := (b + S i)%nat)
      in Hz₁.
      contradiction.

      rewrite <- Nat.add_assoc.
      apply Nat.add_le_mono_l.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l.
      apply Nat.le_sub_le_add_l.
      rewrite Nat.sub_diag.
      apply Nat.le_0_l.

    remember (zerop_1st_n_const_coeff (b + S i) pol ns) as z₂ eqn:Hz₂ .
    symmetry in Hz₂.
    destruct z₂.
     Focus 2.
     rewrite IHn; auto.
     apply rng_add_compat_l.
     rewrite Nat.add_succ_r, Nat.add_succ_l, <- Nat.add_succ_r.
     rewrite Hz₁.
     destruct z₁; [ reflexivity | idtac ].
     rewrite Nat.add_succ_l, <- Nat.add_succ_r.
     rewrite Nat.add_succ_l, <- Nat.add_succ_r.
     reflexivity.

     destruct z₁.
      Focus 2.
      apply zerop_1st_n_const_coeff_true_if with (n := n) in Hz₂.
      rewrite Nat.add_succ_r, Nat.add_succ_l, <- Nat.add_succ_r in Hz₂.
      rewrite Hz₁ in Hz₂.
      discriminate Hz₂.

      (* a lemma here could be cool *)
      revert Hz H₂ Hz₂; clear; intros.
      exfalso; apply H₂; clear H₂.
      rewrite Nat.add_succ_r in Hz₂.
      rewrite Nat.add_succ_r.
      clear n.
      remember (b + i)%nat as n; clear Heqn.
      revert Hz Hz₂; clear; intros.
      revert pol ns Hz Hz₂.
      induction n; intros.
       simpl.
       simpl in Hz₂.
       simpl in Hz.
       destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
        discriminate Hz.

        clear Hz.
        remember (ac_root (Φq pol ns)) as c.
        remember (next_pol pol (β ns) (γ ns) c) as pol₁.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂].
         assumption.

         discriminate Hz₂.

       remember (S n) as sn; simpl; subst sn.
       remember (ac_root (Φq pol ns)) as c.
       remember (next_pol pol (β ns) (γ ns) c) as pol₁.
       remember (List.hd phony_ns (newton_segments pol₁)) as ns₁.
       apply IHn.
        simpl in Hz.
        destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
         discriminate Hz.

         subst; assumption.

        remember (S n) as sn; simpl in Hz₂; subst sn.
        simpl in Hz.
        destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
         discriminate Hz.

         subst; assumption.
Qed.

Lemma root_head_succ : ∀ pol ns b n,
  zerop_1st_n_const_coeff b pol ns = false
  → (root_head b (S n) pol ns =
     root_head b n pol ns +
     if zerop_1st_n_const_coeff (b + n) pol ns then 0
     else ps_monom (nth_c (b + S n) pol ns) (γ_sum b (S n) pol ns))%ps.
Proof.
intros pol ns b n Hz.
unfold root_head; rewrite Hz.
rewrite root_head_from_cγ_list_succ.
 rewrite Nat.add_0_r, Nat.add_0_l.
 reflexivity.

 rewrite Nat.add_0_r; assumption.
Qed.

Lemma root_tail_when_r_1 : ∀ pol ns pol₁ ns₁ c m q₀ b,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ∀ n,
    (∀ i, (i ≤ b + n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
    → (root_tail (m * q₀) b pol₁ ns₁ =
       root_head b n pol₁ ns₁ +
         ps_monom 1%K (γ_sum b n pol₁ ns₁) *
         root_tail (m * q₀) (b + S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ n Hpsi.
clear Hpsi.
remember (m * q₀)%positive as m₁.
revert pol ns pol₁ ns₁ Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁.
revert b c m q₀ m₁ Heqm₁.
induction n; intros.
 unfold root_head.
 simpl.
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
  rewrite root_tail_from_0; eauto .
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

bbb.
  Hz₁ : zerop_1st_n_const_coeff b pol₁ ns₁ = false
  ============================
   (root_tail m₁ b pol₁ ns₁ =
    root_head b (S n) pol₁ ns₁ +
    ps_monom 1%K (γ_sum b (S n) pol₁ ns₁) *
    root_tail m₁ (b + S (S n)) pol₁ ns₁)%ps

problème avec définition de root_head_from_cγ_list...

  rewrite root_head_succ; auto.
  remember (zerop_1st_n_const_coeff (b + n) pol₁ ns₁) as z eqn:Hz .
  symmetry in Hz.
  destruct z.
   rewrite rng_add_0_r, Nat.add_succ_r.
   rewrite IHn; eauto .
   apply rng_add_compat_l.
   unfold γ_sum at 2; simpl.
   rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
   rewrite fold_γ_sum, ps_monom_add_r.
   rewrite <- rng_mul_assoc.
   apply rng_mul_compat_l.
   unfold root_tail.
   rewrite <- Nat.add_1_r, Nat.add_assoc.
   rewrite zerop_1st_n_const_coeff_true_if; auto.
   rewrite <- Nat.add_succ_r.
   rewrite zerop_1st_n_const_coeff_true_if; auto.
   rewrite rng_mul_0_r; reflexivity.

(*
  Hz : zerop_1st_n_const_coeff (b + n) pol₁ ns₁ = false
  ============================
   (root_tail m₁ b pol₁ ns₁ =
    root_head b n pol₁ ns₁ +
    ps_monom (nth_c (b + S n) pol₁ ns₁) (γ_sum b (S n) pol₁ ns₁) +
    ps_monom 1%K (γ_sum b (S n) pol₁ ns₁) *
    root_tail m₁ (b + S (S n)) pol₁ ns₁)%ps
FAUX si nul à partir de b + S n parce que le terme
    ps_monom (nth_c (b + S n) pol₁ ns₁) (γ_sum b (S n) pol₁ ns₁)
reste alors qu'il n'aurait pas dû rester
*)
bbb.
   remember (zerop_1st_n_const_coeff (b + S (S n)) pol₁ ns₁) as z₂ eqn:Hz₂ .
   symmetry in Hz₂.
   destruct z₂.
    Focus 2.
    rewrite IHn; eauto .
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
    eapply root_tail_sep_1st_monom; eauto .
    intros i Hibn.
    destruct (eq_nat_dec i (S (b + n))) as [H₁| H₁].
     subst i.
     apply zerop_1st_n_const_coeff_false_iff with (i := S (b + n)) in Hz₂.
      assumption.

      do 2 rewrite Nat.add_succ_r.
      apply Nat.le_succ_r.
      left; reflexivity.

     apply le_neq_lt in Hibn; auto.
     apply Nat.succ_le_mono in Hibn.
     clear H₁.
     revert i Hibn.
     apply zerop_1st_n_const_coeff_false_iff; assumption.

bbb.
    unfold root_tail at 2.
    rewrite Hz₂, rng_mul_0_r, rng_add_0_r.
    remember (zerop_1st_n_const_coeff (S (b + n)) pol₁ ns₁) as z₃ eqn:Hz₃ .
    symmetry in Hz₃.
    destruct z₃.
     Focus 2.
     rewrite IHn; eauto .
     apply rng_add_compat_l; simpl.
     unfold γ_sum at 2; simpl.
     rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
     rewrite fold_γ_sum, ps_monom_add_r.
     rewrite <- ps_monom_add_r.
     rewrite rng_add_comm.
     rewrite ps_monom_add_r.
     rewrite rng_mul_comm.
     apply rng_mul_compat_r; simpl.
     rewrite Heqm₁.
     rewrite root_tail_sep_1st_monom; eauto .
      Focus 2.
      apply zerop_1st_n_const_coeff_false_iff.
      rewrite Nat.add_succ_r; assumption.

      unfold root_tail.
      rewrite <- Nat.add_succ_r.
      rewrite Hz₂.
      rewrite rng_mul_0_r, rng_add_0_r.
      reflexivity.
bbb.
  Hz₁ : zerop_1st_n_const_coeff b pol₁ ns₁ = false
  Hz : zerop_1st_n_const_coeff (b + n) pol₁ ns₁ = false
  Hz₂ : zerop_1st_n_const_coeff (b + S (S n)) pol₁ ns₁ = true
  Hz₃ : zerop_1st_n_const_coeff (S (b + n)) pol₁ ns₁ = true
  ============================
   (root_tail m₁ b pol₁ ns₁ =
    root_head b n pol₁ ns₁ +
    ps_monom (nth_c (b + S n) pol₁ ns₁) (γ_sum b (S n) pol₁ ns₁))%ps

 rewrite IHn; eauto .
 unfold γ_sum.
 rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
 rewrite ps_monom_add_r, fold_γ_sum.
 unfold root_head; simpl.
 rewrite Nat.add_0_r.
 remember (zerop_1st_n_const_coeff b pol₁ ns₁) as z₁ eqn:Hz₁ .
 symmetry in Hz₁.
 destruct z₁.
  do 2 rewrite rng_add_0_l.
  unfold root_tail.
  rewrite zerop_1st_n_const_coeff_true_if; auto.
  rewrite zerop_1st_n_const_coeff_true_if; auto.
  do 2 rewrite rng_mul_0_r; reflexivity.

  rewrite zerop_1st_n_const_coeff_false_iff in Hz₁.
  rename Hz₁ into Hpsi.
  destruct (ps_zerop R (ps_poly_nth 0 (nth_pol b pol₁ ns₁))) as [H₁| H₁].
   pose proof (Hpsi b (Nat.le_refl b)); contradiction.

   rewrite Heqm₁.
   unfold γ_sum at 2; simpl.
   unfold summation; simpl.
   rewrite Nat.add_0_r, rng_add_0_r.
bbb.
   rewrite root_tail_sep_1st_monom; eauto .
(* cf root_tail_nth too *)

bbb.
   unfold γ_sum at 3; simpl.
   rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
   rewrite ps_monom_add_r, fold_γ_sum.
   symmetry.
   rewrite ps_monom_split_mul in |- * at 1.
   unfold γ_sum at 1; simpl.
   unfold summation; simpl.
   rewrite Nat.add_0_r.
   rewrite rng_add_0_r.
bbb.


intros pol ns pol₁ ns₁ c m q₀ b Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ n Hpsi.
remember (m * q₀)%positive as m₁.
revert pol ns pol₁ ns₁ Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ Hpsi.
revert b c m q₀ m₁ Heqm₁.
induction n; intros.
 rewrite Nat.add_0_r in Hpsi; subst m₁.
 eapply root_tail_from_0; eauto .

 rewrite IHn; eauto ; [ idtac | intros i H; apply Hpsi; fast_omega H ].
 unfold root_head, root_head_from_cγ_list.
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  assert (0 ≤ b + S n) as H by fast_omega .
  apply Hpsi in H; contradiction.

  rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
  rewrite <- rng_add_assoc.
  apply rng_add_compat_l; simpl.
  unfold γ_sum at 3; simpl.
  rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
  rewrite ps_monom_add_r, fold_γ_sum.
  symmetry.
  rewrite ps_monom_split_mul in |- * at 1.
  unfold γ_sum at 1; simpl.
  rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
  rewrite ps_monom_add_r, fold_γ_sum.
  rewrite ps_mul_comm, <- ps_mul_assoc.
  rewrite <- ps_mul_assoc, <- ps_mul_add_distr_l.
  apply ps_mul_compat_l.
  symmetry.
  do 3 rewrite Nat.add_succ_r.
  rewrite ps_mul_comm.
  rewrite <- ps_monom_split_mul.
  subst m₁.
  eapply root_tail_sep_1st_monom; eauto .
  rewrite <- Nat.add_succ_r.
  assumption.
Qed.

bbb.

Lemma zzz : ∀ pol ns c₁ ps pol₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ps = root_when_r_1 pol ns
  → (ps_pol_apply pol ps = 0)%ps.
Proof.
intros pol ns c₁ ps pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hps.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁.
eapply f₁_root_f_root with (y₁ := ps₁); [ eassumption | idtac | idtac ].
 Focus 2.
 apply order_inf.
 unfold order.
 remember (ps_terms (ps_pol_apply pol₁ ps₁)) as s eqn:Hs .
 remember (null_coeff_range_length R s 0) as v eqn:Hv .
 symmetry in Hv.
 destruct v as [v| ]; [ exfalso | reflexivity ].
 apply null_coeff_range_length_iff in Hv.
 unfold null_coeff_range_length_prop in Hv; simpl in Hv.
 destruct Hv as (Hiv, Hv).
 apply Hv; clear Hv.
 rewrite Hs.
bbb.

intros pol ns c₁ ps pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hps.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁.
eapply f₁_root_f_root with (y₁ := ps₁); [ eassumption | idtac | idtac ].
 Focus 2.
 unfold ps_pol_apply; simpl.
 unfold apply_poly; simpl.
 rewrite Hpol₁; simpl.
 unfold next_lap; simpl.
 rewrite apply_lap_mul.
 simpl.
 rewrite ps_mul_0_l, ps_add_0_l.
 rewrite apply_lap_compose; simpl.
 rewrite ps_mul_0_l, ps_add_0_l.
 rewrite Hps₁; simpl.
 unfold root_when_r_1; simpl.
 rewrite Hini₁, Hfin₁; simpl.
 rewrite Z.mul_1_r, Pos.mul_1_r.
bbb.

intros pol ns c₁ ps pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hps.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁.
apply order_inf.
unfold order.
remember (ps_terms (ps_pol_apply pol ps)) as s eqn:Hs .
remember (null_coeff_range_length R s 0) as v eqn:Hv .
symmetry in Hv.
destruct v as [v| ]; [ exfalso | reflexivity ].
apply null_coeff_range_length_iff in Hv.
unfold null_coeff_range_length_prop in Hv; simpl in Hv.
destruct Hv as (Hiv, Hv).
apply Hv; clear Hv.
rewrite Hs.
bbb.

intros pol ns c₁ ps pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hps.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁.
bbb.

intros pol ns c₁ ps pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hps.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
 destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
 subst j₁ k₁.
bbb.
 eapply f₁_root_f_root with (y₁ := ps₁); [ eassumption | idtac | idtac ].
  Focus 2.
  apply order_inf.
  unfold order.
  remember (ps_terms (ps_pol_apply pol₁ ps₁)) as s₁ eqn:Hs₁ .
  remember (null_coeff_range_length R s₁ 0) as v₁ eqn:Hv₁ .
  symmetry in Hv₁.
  destruct v₁ as [v₁| ]; [ exfalso | reflexivity ].
  apply null_coeff_range_length_iff in Hv₁.
  unfold null_coeff_range_length_prop in Hv₁; simpl in Hv₁.
  destruct Hv₁ as (Hiv₁, Hv₁).
  apply Hv₁; clear Hv₁.
  rewrite Hs₁; simpl.
  rewrite Hps₁; simpl.
  unfold root_when_r_1; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Z.mul_1_r, Pos.mul_1_r.
  unfold Qeq in Hαk₁; simpl in Hαk₁.
  rewrite Z.mul_1_r in Hαk₁.
  rewrite Hαk₁.
  rewrite Z.mul_0_l, Z.add_0_r.
  unfold ps_pol_apply; simpl.
  unfold apply_poly; simpl.
  unfold apply_lap; simpl.
  assert ({| terms := root_term_when_r_1 pol₁ ns₁ |} = 0)%ser as Hsz.
   apply series_null_coeff_range_length_inf_iff.
   apply null_coeff_range_length_iff.
   unfold null_coeff_range_length_prop; simpl.
   intros i.
   unfold root_term_when_r_1; simpl.
   rewrite Hini₁, Hfin₁; simpl.
   rewrite Pos.mul_1_r.
bbb.

intros pol ns c₁ ps Hns Hc₁ Hr Hps.
remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
 destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
 subst j₁ k₁.
 apply order_inf.
 unfold order.
 remember (ps_terms (ps_pol_apply pol ps)) as s eqn:Hs .
 remember (null_coeff_range_length R s 0) as v eqn:Hv .
 symmetry in Hv.
 destruct v as [v| ]; [ exfalso | reflexivity ].
 apply null_coeff_range_length_iff in Hv.
 unfold null_coeff_range_length_prop in Hv; simpl in Hv.
 destruct Hv as (Hiv, Hv).
 apply Hv; clear Hv.
 rewrite Hs; simpl.
 rewrite Hps; simpl.
 unfold root_when_r_1; simpl.
 rewrite Hini, Hfin; simpl.
 rewrite Qnum_inv; simpl.
  rewrite Z.mul_1_r.
bbb.

intros pol ns c₁ ps Hns Hc₁ Hr Hps.
remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (root_when_r_1 pol₁ ns₁) as ps₁ eqn:Hps₁ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
 destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
 subst j₁ k₁.
 eapply f₁_root_f_root with (y₁ := ps₁); [ eassumption | idtac | idtac ].
  rewrite Hps, Hps₁.
  unfold ps_add, ps_mul; simpl.
  unfold cm; simpl.
  rewrite Hini, Hfin; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Pos.mul_1_r.
  rewrite Z.mul_1_r.
  unfold Qeq in Hαk₁.
  simpl in Hαk₁.
  rewrite Z.mul_1_r in Hαk₁.
  rewrite Hαk₁.
  rewrite Z.mul_0_l.
  rewrite Z.add_0_r.
  rewrite Pos2Z.inj_mul.
  rewrite Pos2Z.inj_mul.
  rewrite Pos2Z.inj_mul.
  rewrite Qden_inv.
   rewrite Qnum_inv.
bbb.

(*
Lemma zzz : ∀ pol ns m,
  ns = List.hd phony_ns (newton_segments pol)
  → polydromy_if_r_reaches_one acf m pol ≠ 0%nat
  → ∃ ps, (ps_pol_apply pol ps = 0)%ps.
Proof.
intros pol ns m Hns Hpnz.
revert pol ns Hns Hpnz.
induction m; intros; [ exfalso; apply Hpnz; reflexivity | idtac ].
simpl in Hpnz.
rewrite <- Hns in Hpnz.
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (root_multiplicity acf c (Φq pol ns)) as r eqn:Hr .
symmetry in Hr.
destruct (eq_nat_dec r 1) as [Hr1| Hrn1].
 subst r; clear Hpnz.
bbb.
 exists (root_when_r_1 pol ns).
 remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 remember (root_when_r_1 pol₁ ns₁) as y₁ eqn:Hy₁ .
 eapply f₁_root_f_root with (y₁ := y₁); try eassumption.
bbb.

intros pol ns c₁ c₂ pol₁ ns₁ m.
intros Hns Hc₁ Hr Hpol₁ Hps₀ Hns₁ Hc₂ Hpnz.
remember (polydromy_if_r_one acf m pol) as p eqn:Hp .
revert pol pol₁ Hns Hc₁ Hr Hpol₁ Hps₀ Hns₁ Hc₂ Hp.
induction m; [ contradiction | intros ].
simpl in Hp.
rewrite <- Hns in Hp.
destruct (ac_zerop (ac_root (Φq pol ns))) as [Hz| Hnz].
 remember Hpol₁ as H; clear HeqH.
 eapply multiplicity_1_remains in H; try eassumption.
bbb.

bbb.
remember Hpol₁ as H; clear HeqH.
eapply f₁_root_f_root in H; [ idtac | reflexivity | idtac ].
bbb.
*)

End theorems.
