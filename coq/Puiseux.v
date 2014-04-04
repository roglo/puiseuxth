(* Puiseux.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.
Require Import Sorted.

Require Import Misc.
Require Import Nbar.
Require Import Qbar.
Require Import Field.
Require Import Fpolynomial.
Require Import Fsummation.
Require Import Newton.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import PolyConvexHull.
Require Import Puiseux_base.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_mul.
Require Import Ps_div.
Require Import CharactPolyn.
Require Import F1Eq.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Let Kx := ps_ring R.

Lemma valuation_in_newton_segment : ∀ pol ns pl h αh,
  ns ∈ newton_segments R pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → (Qnat h, αh) ∈ pl
      → valuation (poly_nth R h pol) = qfin αh.
Proof.
intros pol ns pl h αh Hns Hpl Hαh.
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
unfold poly_nth, lap_nth; simpl.
edestruct in_pts_in_pol; try reflexivity; try eassumption.
subst pl.
simpl in Hαh.
destruct Hαh as [Hαh| Hαh].
 rewrite Hini in Hαh.
 injection Hαh; clear Hαh; intros HH H; subst αh.
 apply Nat2Z.inj in H; subst h.
 rewrite <- Hini.
 apply ini_fin_ns_in_init_pts; assumption.

 apply List.in_app_or in Hαh.
 destruct Hαh as [Hαh| Hαh].
  eapply oth_pts_in_init_pts; try reflexivity; try eassumption.

  destruct Hαh as [Hαh| Hαh]; [ idtac | contradiction ].
  rewrite Hfin in Hαh.
  injection Hαh; clear Hαh; intros HH H; subst αh.
  apply Nat2Z.inj in H; subst h.
  rewrite <- Hfin.
  apply ini_fin_ns_in_init_pts; assumption.
Qed.

Lemma coeff_of_hl_eq_valuation : ∀ h la li,
  h ∈ li
  → coeff_of_hl R la h li = valuation_coeff R (List.nth h la 0%ps).
Proof.
intros h la li Hh.
induction li as [| i]; [ contradiction | simpl ].
destruct (eq_nat_dec h i) as [| Hhi]; [ subst; reflexivity | idtac ].
apply IHli.
apply Nat.neq_sym in Hhi.
destruct Hh as [Hh| ]; [ contradiction | assumption ].
Qed.

(* [Walker, p 101] « O (āh - ah.x^αh) > 0 » (with fixed typo)
   What is called "O" (for "order") is actually the valuation. *)
Theorem valuation_āh_minus_ah_xαh_gt_αh : ∀ pol ns pl tl h āh ah αh,
  let _ := Kx in
  ns ∈ newton_segments R pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point R pol) pl
      → h ∈ List.map (λ t, power t) tl
        → āh = poly_nth R h pol
          → ah = ps_monom (coeff_of_term R h tl) 0
            → αh = val_of_pt h pl
              → (valuation (āh - ah * ps_monom 1%K αh)%ps > qfin αh)%Qbar.
Proof.
intros pol ns pl tl h āh ah αh f' Hns Hpl Htl Hh Hāh Hah Hαh.
remember Hns as Hval; clear HeqHval.
eapply valuation_in_newton_segment with (h := h) (αh := αh) in Hval; eauto .
 rewrite <- Hāh in Hval.
 unfold valuation, Qbar.gt.
 remember (āh - ah * ps_monom 1%K αh)%ps as s eqn:Hs .
 remember (null_coeff_range_length R (ps_terms s) 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ]; [ idtac | constructor ].
 apply Qbar.qfin_lt_mono.
 unfold valuation in Hval.
 remember (null_coeff_range_length R (ps_terms āh) 0) as m eqn:Hm .
 symmetry in Hm.
 destruct m as [m| ]; [ idtac | discriminate Hval ].
 injection Hval; clear Hval; intros Hval.
 rewrite <- Hval.
 subst s; simpl.
 unfold cm; simpl.
 unfold cm; simpl.
 subst ah; simpl.
 unfold ps_valnum_add; simpl.
 unfold cm, cm_factor; simpl.
 rewrite Z.mul_1_r.
 unfold Qlt; simpl.
 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_assoc.
 rewrite Z.mul_shuffle0.
 apply Z.mul_lt_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
 rewrite <- Hval; simpl.
 rewrite Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Z.min_l.
  rewrite Z.mul_add_distr_r.
  apply Z.add_lt_mono_l.
  rewrite <- positive_nat_Z, <- Nat2Z.inj_mul.
  apply Nat2Z.inj_lt.
  apply Nat.nle_gt; intros Hmn.
  apply null_coeff_range_length_iff in Hn.
  unfold null_coeff_range_length_prop in Hn.
  simpl in Hm.
  remember ps_add as f; simpl in Hn; subst f.
  destruct Hn as (Hni, Hn).
  remember (ps_monom (coeff_of_term R h tl) 0 * ps_monom 1%K αh)%ps as v.
  simpl in Hn.
  unfold cm, cm_factor in Hn; simpl in Hn.
  subst v; simpl in Hn.
  unfold cm in Hn; simpl in Hn.
  rewrite Z.mul_1_r in Hn.
  rewrite <- Hval in Hn; simpl in Hn.
  rewrite Z.min_l in Hn.
   rewrite Z.sub_diag in Hn; simpl in Hn.
   rewrite Nat.sub_0_r in Hn.
   rewrite Z.min_r in Hn.
    destruct (zerop (n mod Pos.to_nat (ps_polord āh))) as [Hnp| Hnp].
     apply Nat.mod_divides in Hnp; auto.
     destruct Hnp as (p, Hp).
     rewrite Nat.mul_comm in Hp.
     rewrite Hp in Hmn.
     apply Nat.mul_le_mono_pos_r in Hmn; [ idtac | apply Pos2Nat.is_pos ].
     rewrite Hp in Hn.
     rewrite Nat.div_mul in Hn; auto; simpl in Hn.
     rewrite Z.mul_add_distr_r in Hn.
     rewrite Z.add_simpl_l in Hn.
     rewrite Z2Nat.inj_mul in Hn; simpl in Hn.
      rewrite Nat2Z.id in Hn.
      rewrite <- Hp in Hn.
      destruct (eq_nat_dec p m) as [Hpm| Hpm].
       subst p.
       rewrite <- Hp, Nat.sub_diag in Hn.
       destruct (lt_dec n n) as [Hnn| Hnn].
        revert Hnn; apply Nat.lt_irrefl.

        rewrite Nat.mod_0_l in Hn; auto; simpl in Hn.
        rewrite Nat.div_0_l in Hn; auto; simpl in Hn.
        unfold convol_mul in Hn.
        simpl in Hn.
        unfold summation in Hn; simpl in Hn.
        rewrite Nat.mod_0_l in Hn; auto; simpl in Hn.
        rewrite Nat.div_0_l in Hn; auto; simpl in Hn.
        rewrite rng_mul_1_r, rng_add_0_r in Hn.
        rewrite Htl in Hn.
        rewrite coeff_of_term_pt_eq in Hn.
        rewrite Hāh in Hn; simpl in Hn.
        unfold poly_nth, lap_nth in Hn; simpl in Hn.
        rewrite Hāh in Hm.
        unfold coeff_of_pt in Hn.
        rewrite coeff_of_hl_eq_valuation in Hn.
         unfold valuation_coeff in Hn.
         unfold poly_nth, lap_nth in Hm.
         rewrite Hm in Hn.
         rewrite rng_add_opp_r in Hn.
         apply Hn; reflexivity.

         subst tl; simpl in Hh.
         revert Hh; clear; intros.
         induction pl as [| (i, ai)]; [ assumption | simpl ].
         simpl in Hh.
         destruct Hh as [Hh| Hh]; [ left; assumption | idtac ].
         right; apply IHpl; assumption.

       destruct (lt_dec n (m * Pos.to_nat (ps_polord āh))) as [Hnp| Hnp].
        apply null_coeff_range_length_iff in Hm.
        unfold null_coeff_range_length_prop in Hm.
        destruct Hm as (Hmi, Hm).
        apply le_neq_lt in Hmn; [ idtac | assumption ].
        apply Hmi in Hmn.
        rewrite rng_add_0_r in Hn; contradiction.

        apply Hnp.
        rewrite Hp.
        apply Nat.mul_lt_mono_pos_r; [ apply Pos2Nat.is_pos | idtac ].
        apply le_neq_lt; assumption.

      apply Nat2Z.is_nonneg.

      apply Pos2Z.is_nonneg.

     rewrite rng_add_0_l in Hn.
     rewrite Z.mul_add_distr_r in Hn.
     rewrite Z.add_simpl_l in Hn.
     rewrite Z2Nat.inj_mul in Hn; simpl in Hn.
      rewrite Nat2Z.id in Hn.
      destruct (lt_dec n (m * Pos.to_nat (ps_polord āh))) as [Hnm| Hnm].
       apply Hn; reflexivity.

       apply Hnm; clear Hnm.
       destruct (eq_nat_dec n (m * Pos.to_nat (ps_polord āh))) as [Heq| Hne].
        rewrite Heq in Hnp.
        rewrite Nat.mod_mul in Hnp; auto.
        exfalso; revert Hnp; apply Nat.lt_irrefl.

        apply le_neq_lt; assumption.

      apply Nat2Z.is_nonneg.

      apply Pos2Z.is_nonneg.

    rewrite Z.mul_add_distr_r.
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag, <- positive_nat_Z, <- Nat2Z.inj_mul.
    apply Nat2Z.is_nonneg.

   rewrite Z.mul_add_distr_r.
   apply Z.le_sub_le_add_l.
   rewrite Z.sub_diag, <- positive_nat_Z, <- Nat2Z.inj_mul.
   apply Nat2Z.is_nonneg.

  apply Z.le_sub_le_add_l.
  rewrite Z.sub_diag.
  apply Nat2Z.is_nonneg.

 rewrite Hαh.
 rewrite Htl in Hh; simpl in Hh.
 rewrite List.map_map in Hh.
 simpl in Hh.
 subst f'.
 apply val_is_val_of_pt; [ idtac | idtac | assumption ].
  rewrite Hpl.
  eapply ini_oth_fin_pts_sorted; eassumption.

  intros pt Hpt.
  eapply points_in_newton_segment_have_nat_abscissa; [ eassumption | idtac ].
  subst pl; assumption.
Qed.

(* [Walker, p 101] « O (āl.x^(l.γ₁)) > β₁ »
   What is called "O" (for "order") is actually the valuation. *)
Theorem zzz : ∀ pol ns pl tl l₁ l₂ l āl,
  let _ := Kx in
  ns ∈ newton_segments R pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point R pol) pl
      → l₁ = List.map (λ t, power t) tl
        → split_list (List.seq 0 (length (al pol))) l₁ l₂
          → l ∈ l₂
            → āl = poly_nth R l pol
              → (valuation (āl * ps_monom 1%K (Qnat l * γ ns))%ps >
                 qfin (β ns))%Qbar.
Proof.
intros pol ns pl tl l₁ l₂ l āl f' Hns Hpl Htl Hl₁ Hsl Hl Hāl.
remember (āl * ps_monom 1%K (Qnat l * γ ns))%ps as s eqn:Hs .
remember (null_coeff_range_length R (ps_terms s) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 Focus 2.
 unfold valuation; simpl.
 rewrite Hn; constructor.

 remember (points_of_ps_polynom R pol) as pts eqn:Hpts .
 remember Hpts as Hval; clear HeqHval.
 remember (valuation āl) as m eqn:Hm .
 symmetry in Hm.
 destruct m as [m| ].
  eapply in_pol_in_pts in Hval; try eassumption.
  eapply points_not_in_any_newton_segment in Hns; try eassumption.
   2: split; [ eassumption | idtac ].
   unfold valuation, Qbar.gt.
   rewrite Hn.
   apply Qbar.qfin_lt_mono.
   rewrite Hs, Hāl; simpl.
   unfold cm; simpl.
   rewrite <- Hāl.
   eapply Qlt_le_trans; [ eassumption | idtac ].
   unfold Qle; simpl.
   do 2 rewrite Pos2Z.inj_mul.
   do 2 rewrite Z.mul_assoc.
   apply Z.mul_le_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
   rewrite Z.mul_add_distr_r.
   rewrite Z.mul_add_distr_r.
   rewrite Z.mul_add_distr_r.
   rewrite Z.add_shuffle0.
   apply Z.add_le_mono.
    Focus 2.
    rewrite Z.mul_shuffle0; reflexivity.

    Focus 3.
    unfold valuation in Hm.
    remember (null_coeff_range_length R (ps_terms āl) 0) as v eqn:Hv .
    symmetry in Hv.
    destruct v; [ discriminate Hm | idtac ].
    apply null_coeff_range_length_inf_iff in Hv.
    assert (s = 0)%ps as Hsz.
     rewrite Hs.
     rewrite Hv.
     rewrite ps_mul_0_l; reflexivity.

     apply valuation_inf in Hsz.
     rewrite Hsz; constructor.

   unfold valuation in Hm.
   remember (null_coeff_range_length R (ps_terms āl) 0) as p eqn:Hp .
   symmetry in Hp.
   destruct p as [p| ]; [ idtac | discriminate Hm ].
   injection Hm; clear Hm; intros Hm.
   rewrite <- Hm; simpl.
   rewrite Z.mul_add_distr_r.
   rewrite Z.mul_add_distr_r.
   apply Z.add_le_mono_l.
   apply Z.mul_le_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
   rewrite <- positive_nat_Z.
   rewrite <- Nat2Z.inj_mul.
   apply Nat2Z.inj_le.
   rewrite Hs in Hn; simpl in Hn.
   unfold cm_factor in Hn; simpl in Hn.
   apply null_coeff_range_length_iff in Hn.
   apply null_coeff_range_length_iff in Hp.
   unfold null_coeff_range_length_prop in Hn, Hp.
   simpl in Hn, Hp.
   destruct Hn as (Hni, Hn).
   destruct Hp as (Hpi, Hp).
   unfold convol_mul in Hn.
   rewrite summation_only_one_non_0 with (v := n) in Hn.
    rewrite Nat.sub_diag in Hn; simpl in Hn.
    rewrite Nat.mod_0_l in Hn; auto; simpl in Hn.
    rewrite Nat.div_0_l in Hn; auto; simpl in Hn.
    rewrite rng_mul_1_r in Hn.
    destruct (zerop (n mod Pos.to_nat (Qden (γ ns)))) as [Hng| Hng].
     2: exfalso; apply Hn; reflexivity.

     apply Nat.mod_divides in Hng; auto.
     destruct Hng as (g, Hg).
     rewrite Hg, Nat.mul_comm.
     apply Nat.mul_le_mono_l.
     rewrite Hg in Hn.
     rewrite Nat.mul_comm in Hn.
     rewrite Nat.div_mul in Hn; auto.
     apply Nat.nlt_ge.
     intros H.
     apply Hpi in H.
     contradiction.

    split; [ apply Nat.le_0_l | reflexivity ].

    intros i (_, Hin) Hinn.
    apply rng_mul_eq_0.
    right.
    unfold series_stretch; simpl.
    destruct (zerop ((n - i) mod Pos.to_nat (ps_polord āl))) as [Hz| Hz].
     apply Nat.mod_divides in Hz; auto.
     destruct Hz as (c, Hc).
     rewrite Nat.mul_comm in Hc; rewrite Hc.
     rewrite Nat.div_mul; auto.
     destruct c; [ idtac | reflexivity ].
     rewrite Nat.mul_0_l in Hc.
     exfalso; fast_omega Hin Hinn Hc.

     reflexivity.
bbb.

intros pol ns pl tl l₁ l₂ l āl f' Hns Hpl Htl Hl₁ Hsl Hl Hāl.
remember (ps_valnum āl # ps_polord āl) as αl eqn:Hαl .
remember (points_of_ps_polynom R pol) as pts eqn:Hpts .
remember (āl * ps_monom 1%K (Qnat l * γ ns))%ps as s eqn:Hs .
remember (null_coeff_range_length R (ps_terms s) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 eapply points_not_in_any_newton_segment with (h := Qnat l) (αh := αl) in Hns.
  2: eassumption.

  rewrite Hαl in Hns.
  unfold Qnat in Hns; simpl in Hns.
  unfold Qplus, Qmult in Hns; simpl in Hns.
  unfold valuation, Qbar.gt.
  rewrite Hn.
  apply Qbar.qfin_lt_mono.
  eapply Qlt_le_trans; [ eassumption | idtac ].
  unfold Qle; simpl.
  rewrite Hs, Hāl; simpl.
  apply Z.mul_le_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
  apply Z.le_sub_le_add_l.
  rewrite Z.sub_diag.
  apply Nat2Z.is_nonneg.

  Focus 2.
  unfold valuation; simpl.
  rewrite Hn; constructor.

 split.
 (* cf in_pts_in_pol : ça peut peut-être me donner des idées... *)
bbb.

End theorems.
