(* Puiseux.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.
Require Import Sorted.

Require Import Misc.
Require Import Nbar.
Require Import Qbar.
Require Import SplitList.
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
Require Import AlgCloCharPol.
Require Import CharactPolyn.
Require Import F1Eq.

Set Implicit Arguments.

Lemma div_gcd_gcd_0_r : ∀ a b c d e f,
  (b / Z.gcd (Z.gcd a b) c)%Z = (e / Z.gcd (Z.gcd d e) f)%Z
  → e = 0%Z
    → (a * e)%Z = (d * b)%Z.
Proof.
intros a b c d e f Hb He.
subst e.
rewrite Z.mul_0_r.
rewrite Z.gcd_0_r in Hb.
destruct (Z_zerop d) as [Hd| Hd].
 subst d; rewrite Z.mul_0_l; reflexivity.

 rewrite Z.div_0_l in Hb.
  rewrite Z.gcd_comm, Z.gcd_assoc in Hb.
  pose proof (Z.gcd_divide_l b (Z.gcd c a)) as H.
  destruct H as (e, H).
  rewrite Z.gcd_comm in H.
  remember (Z.gcd (Z.gcd c a) b) as g.
  rewrite H in Hb.
  destruct (Z_zerop g) as [Hg| Hg].
   move Hg at top; subst g.
   rewrite Z.mul_0_r in H; subst b.
   rewrite Z.mul_0_r; reflexivity.

   rewrite Z.div_mul in Hb; [ idtac | assumption ].
   subst e b.
   rewrite Z.mul_0_l, Z.mul_0_r; reflexivity.

  intros H.
  apply Z.gcd_eq_0_l in H.
  apply Hd.
  apply Z.abs_0_iff; assumption.
Qed.

Lemma div_gcd_gcd_mul_compat : ∀ a b c d e f,
  (a / Z.gcd (Z.gcd a b) c)%Z = (d / Z.gcd (Z.gcd d e) f)%Z
  → (b / Z.gcd (Z.gcd a b) c)%Z = (e / Z.gcd (Z.gcd d e) f)%Z
    → (a * e)%Z = (d * b)%Z.
Proof.
intros a b c d e f Ha Hb.
destruct (Z_zerop e) as [He| He].
 eapply div_gcd_gcd_0_r; eassumption.

 destruct (Z_zerop d) as [Hd| Hd].
  rewrite Z.mul_comm; symmetry.
  rewrite Z.mul_comm; symmetry.
  symmetry.
  apply div_gcd_gcd_0_r with (c := c) (f := f); [ idtac | assumption ].
  replace (Z.gcd b a) with (Z.gcd a b) by apply Z.gcd_comm.
  replace (Z.gcd e d) with (Z.gcd d e) by apply Z.gcd_comm.
  assumption.

  apply Z.mul_cancel_r with (p := e) in Ha; [ idtac | assumption ].
  rewrite Z_div_mul_swap in Ha.
   rewrite Z_div_mul_swap in Ha.
    apply Z.mul_cancel_l with (p := d) in Hb; [ idtac | assumption ].
    rewrite Z.mul_comm in Hb.
    rewrite Z_div_mul_swap in Hb.
     symmetry in Hb.
     rewrite Z.mul_comm in Hb.
     rewrite Z_div_mul_swap in Hb.
      rewrite Z.mul_comm in Hb.
      rewrite Hb in Ha.
      apply Z_div_reg_r in Ha.
       rewrite Ha; apply Z.mul_comm.

       apply Z.divide_mul_l.
       rewrite <- Z.gcd_assoc.
       apply Z.gcd_divide_l.

       apply Z.divide_mul_l.
       rewrite Z.gcd_comm, Z.gcd_assoc.
       apply Z.gcd_divide_r.

      rewrite Z.gcd_comm, Z.gcd_assoc.
      apply Z.gcd_divide_r.

     rewrite Z.gcd_comm, Z.gcd_assoc.
     apply Z.gcd_divide_r.

    rewrite <- Z.gcd_assoc.
    apply Z.gcd_divide_l.

   rewrite <- Z.gcd_assoc.
   apply Z.gcd_divide_l.
Qed.

(* to be moved, perhaps, where order is defined *)
Add Parametric Morphism α (R : ring α) : (@order α R)
  with signature eq_ps ==> Qbar.qeq
  as order_morph.
Proof.
intros a b Hab.
inversion Hab; subst.
unfold canonic_ps in H; simpl in H.
unfold order.
remember (null_coeff_range_length R (ps_terms a) 0) as na eqn:Hna .
remember (null_coeff_range_length R (ps_terms b) 0) as nb eqn:Hnb .
symmetry in Hna, Hnb.
destruct na as [na| ].
 destruct nb as [nb| ].
  inversion_clear H.
  simpl in H0, H1, H2.
  unfold Qbar.qeq, Qeq; simpl.
  unfold canonify_series in H2.
  remember (greatest_series_x_power R (ps_terms a) na) as apn.
  remember (greatest_series_x_power R (ps_terms b) nb) as bpn.
  assert (0 < gcd_ps na apn a)%Z as Hpga by apply gcd_ps_is_pos.
  assert (0 < gcd_ps nb bpn b)%Z as Hpgb by apply gcd_ps_is_pos.
  unfold gcd_ps in H0, H1, H2, Hpga, Hpgb.
  remember (ps_ordnum a + Z.of_nat na)%Z as ao eqn:Hao .
  remember (ps_ordnum b + Z.of_nat nb)%Z as bo eqn:Hbo .
  remember (Z.of_nat apn) as ap eqn:Hap ; subst apn.
  remember (Z.of_nat bpn) as bp eqn:Hbp ; subst bpn.
  remember (' ps_polord a)%Z as oa eqn:Hoa .
  remember (' ps_polord b)%Z as ob eqn:Hob .
  apply Z2Pos.inj in H1.
   eapply div_gcd_gcd_mul_compat; eassumption.

   apply Z.div_str_pos.
   split; [ assumption | idtac ].
   rewrite Z.gcd_comm, Z.gcd_assoc, Hoa.
   apply Z_gcd_pos_r_le.

   apply Z.div_str_pos.
   split; [ assumption | idtac ].
   rewrite Z.gcd_comm, Z.gcd_assoc, Hob.
   apply Z_gcd_pos_r_le.

  apply null_coeff_range_length_inf_iff in Hnb.
  rewrite Hnb in Hab.
  apply null_coeff_range_length_inf_iff in Hab.
  rewrite Hab in Hna; discriminate Hna.

 apply null_coeff_range_length_inf_iff in Hna.
 rewrite Hna in Hab.
 symmetry in Hab.
 apply null_coeff_range_length_inf_iff in Hab.
 rewrite Hab in Hnb.
 subst nb; reflexivity.
Qed.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.
Let Kx := ps_ring R.

Lemma order_in_newton_segment : ∀ pol ns pl h αh,
  ns ∈ newton_segments R pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → (Qnat h, αh) ∈ pl
      → order (poly_nth R h pol) = qfin αh.
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

Lemma coeff_of_hl_eq_order : ∀ h la li,
  h ∈ li
  → coeff_of_hl R la h li = order_coeff R (List.nth h la 0%ps).
Proof.
intros h la li Hh.
induction li as [| i]; [ contradiction | simpl ].
destruct (eq_nat_dec h i) as [| Hhi]; [ subst; reflexivity | idtac ].
apply IHli.
apply Nat.neq_sym in Hhi.
destruct Hh as [Hh| ]; [ contradiction | assumption ].
Qed.

(* [Walker, p 101] « O(āh - ah.x^αh) > 0 » (with fixed typo) *)
Theorem order_āh_minus_ah_xαh_gt_αh : ∀ pol ns pl tl h āh ah αh,
  let _ := Kx in
  ns ∈ newton_segments R pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point R pol) pl
      → h ∈ List.map (λ t, power t) tl
        → āh = poly_nth R h pol
          → ah = ps_monom (coeff_of_term R h tl) 0
            → αh = ord_of_pt h pl
              → (order (āh - ah * ps_monom 1%K αh)%ps > qfin αh)%Qbar.
Proof.
intros pol ns pl tl h āh ah αh f' Hns Hpl Htl Hh Hāh Hah Hαh.
remember Hns as Hval; clear HeqHval.
eapply order_in_newton_segment with (h := h) (αh := αh) in Hval; eauto .
 rewrite <- Hāh in Hval.
 unfold order, Qbar.gt.
 remember (āh - ah * ps_monom 1%K αh)%ps as s eqn:Hs .
 remember (null_coeff_range_length R (ps_terms s) 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ]; [ idtac | constructor ].
 apply Qbar.qfin_lt_mono.
 unfold order in Hval.
 remember (null_coeff_range_length R (ps_terms āh) 0) as m eqn:Hm .
 symmetry in Hm.
 destruct m as [m| ]; [ idtac | discriminate Hval ].
 injection Hval; clear Hval; intros Hval.
 rewrite <- Hval.
 subst s; simpl.
 unfold cm; simpl.
 unfold cm; simpl.
 subst ah; simpl.
 unfold ps_ordnum_add; simpl.
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
        rewrite coeff_of_hl_eq_order in Hn.
         unfold order_coeff in Hn.
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
 apply ord_is_ord_of_pt; [ idtac | idtac | assumption ].
  rewrite Hpl.
  eapply ini_oth_fin_pts_sorted; eassumption.

  intros pt Hpt.
  eapply points_in_newton_segment_have_nat_abscissa; [ eassumption | idtac ].
  subst pl; assumption.
Qed.

(* [Walker, p 101] « O(āl.x^(l.γ₁)) > β₁ » *)
Theorem order_āl_xlγ₁_gt_β₁ : ∀ pol ns pl tl l₁ l₂ l āl,
  let _ := Kx in
  ns ∈ newton_segments R pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point R pol) pl
      → l₁ = List.map (λ t, power t) tl
        → split_list (List.seq 0 (length (al pol))) l₁ l₂
          → l ∈ l₂
            → āl = poly_nth R l pol
              → (order (āl * ps_monom 1%K (Qnat l * γ ns))%ps >
                 qfin (β ns))%Qbar.
Proof.
intros pol ns pl tl l₁ l₂ l āl f' Hns Hpl Htl Hl₁ Hsl Hl Hāl.
remember (āl * ps_monom 1%K (Qnat l * γ ns))%ps as s eqn:Hs .
remember (null_coeff_range_length R (ps_terms s) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 Focus 2.
 unfold order; simpl.
 rewrite Hn; constructor.

 remember (points_of_ps_polynom R pol) as pts eqn:Hpts .
 remember Hpts as Hval; clear HeqHval.
 remember (order āl) as m eqn:Hm .
 symmetry in Hm.
 destruct m as [m| ].
  eapply in_pol_in_pts in Hval; try eassumption.
  eapply points_not_in_any_newton_segment in Hns; try eassumption.
   2: split; [ eassumption | idtac ].
   unfold order, Qbar.gt.
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
    unfold order in Hm.
    remember (null_coeff_range_length R (ps_terms āl) 0) as v eqn:Hv .
    symmetry in Hv.
    destruct v; [ discriminate Hm | idtac ].
    apply null_coeff_range_length_inf_iff in Hv.
    assert (s = 0)%ps as Hsz.
     rewrite Hs.
     rewrite Hv.
     rewrite ps_mul_0_l; reflexivity.

     apply order_inf in Hsz.
     rewrite Hsz; constructor.

   unfold order in Hm.
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

  intros Hlm.
  apply split_list_comm in Hsl.
  eapply sorted_split_in_not_in in Hsl; try eassumption.
   apply Hsl; clear Hsl.
   subst l₁ tl pl.
   rewrite List.map_map; simpl.
   destruct Hlm as [Hlm| Hlm].
    left; rewrite Hlm; simpl.
    rewrite nofq_Qnat; reflexivity.

    right.
    rewrite List.map_app; simpl.
    apply List.in_or_app.
    destruct Hlm as [Hlm| Hlm].
     right; rewrite Hlm.
     left; simpl; rewrite nofq_Qnat; reflexivity.

     left.
     revert Hlm; clear; intros.
     remember (oth_pts ns) as pts; clear Heqpts.
     induction pts as [| (i, ai)]; [ contradiction | idtac ].
     destruct Hlm as [Hlm| Hlm].
      injection Hlm; clear Hlm; intros; subst; simpl.
      left; rewrite nofq_Qnat; reflexivity.

      right; apply IHpts, Hlm.

   remember (length (al pol)) as len; clear.
   remember 0%nat as b; clear Heqb.
   revert b.
   induction len; intros; [ constructor | simpl ].
   constructor; [ apply IHlen | idtac ].
   destruct len; constructor.
   apply Nat.lt_succ_diag_r.
Qed.

Definition g_of_ns pol ns :=
  let _ := Kx in (* coq seems not to see the type of Kx *)
  let c₁ := ac_root (Φq R pol ns) in
  let pl := [ini_pt ns … oth_pts ns ++ [fin_pt ns]] in
  let tl := List.map (term_of_point R pol) pl in
  let l₁ := List.map (λ t, power t) tl in
  let l₂ := list_seq_except 0 (length (al pol)) l₁ in
  (POL [ps_monom 1%K (- β ns)] *
   (poly_summation Kx l₁
      (λ h,
       let āh := poly_nth R h pol in
       let ah := ps_monom (coeff_of_term R h tl) 0 in
       let αh := ord_of_pt h pl in
       POL [((āh - ah * ps_monom 1%K αh) *
             ps_monom 1%K (Qnat h * γ ns))%ps] *
       POL [ps_monom c₁ 0; 1%ps … []] ^ h) +
    poly_summation Kx l₂
      (λ l,
       let āl := poly_nth R l pol in
       POL [(āl * ps_monom 1%K (Qnat l * γ ns))%ps] *
       POL [ps_monom c₁ 0; 1%ps … []] ^ l)))%pol.

Lemma ps_list_in_split : ∀ (a : puiseux_series α) la,
  let _ := Kx in (* coq seems not to see the type of Kx *)
  a ∈ la
  → ∃ l1 l2, (la = l1 ++ [a … l2])%lap.
Proof.
intros a la f' Ha.
subst f'.
induction la as [| b]; [ contradiction | idtac ].
destruct Ha as [Ha| Ha].
 subst b.
 exists [], la; reflexivity.

 apply IHla in Ha.
 destruct Ha as (lb, (lc, Ha)).
 exists [b … lb], lc.
 rewrite Ha; reflexivity.
Qed.

Lemma order_mul : ∀ a b,
  (order (a * b)%ps = order a + order b)%Qbar.
Proof.
intros a b.
symmetry.
pose proof (ps_adjust_eq R a 0 (ps_polord b)) as Ha.
pose proof (ps_adjust_eq R b 0 (ps_polord a)) as Hb.
rewrite Hb in |- * at 1.
rewrite Ha in |- * at 1.
unfold order; simpl.
unfold cm_factor, cm; simpl.
rewrite series_shift_0.
rewrite series_shift_0.
remember (series_stretch R (ps_polord b) (ps_terms a)) as sa eqn:Hsa .
remember (series_stretch R (ps_polord a) (ps_terms b)) as sb eqn:Hsb .
remember (null_coeff_range_length R sa 0) as na eqn:Hna .
remember (null_coeff_range_length R sb 0) as nb eqn:Hnb .
remember (null_coeff_range_length R (sa * sb)%ser 0) as nc eqn:Hnc .
symmetry in Hna, Hnb, Hnc.
destruct na as [na| ].
 destruct nb as [nb| ].
  destruct nc as [nc| ].
   Focus 1.
   simpl.
   rewrite Z.sub_0_r.
   rewrite Z.sub_0_r.
   unfold Qeq; simpl.
   symmetry.
   rewrite Pos2Z.inj_mul.
   rewrite Z.mul_assoc.
   rewrite Z.mul_shuffle0.
   apply Z.mul_cancel_r; [ apply Pos2Z_ne_0 | idtac ].
   symmetry.
   rewrite Pos2Z.inj_mul.
   rewrite Z.mul_assoc.
   rewrite Z.add_comm.
   rewrite Pos2Z.inj_mul.
   rewrite Z.mul_assoc.
   rewrite Z.mul_shuffle0.
   rewrite <- Z.mul_add_distr_r.
   rewrite <- Z.mul_add_distr_r.
   rewrite <- Z.mul_assoc.
   apply Z.mul_cancel_r; [ apply Pos2Z_ne_0 | idtac ].
   rewrite Z.add_comm.
   rewrite Z.add_shuffle1.
   rewrite <- Z.add_assoc.
   rewrite <- Z.add_assoc.
   apply Z.add_cancel_l.
   apply Z.add_cancel_l.
   apply null_coeff_range_length_iff in Hna.
   apply null_coeff_range_length_iff in Hnb.
   apply null_coeff_range_length_iff in Hnc.
   unfold null_coeff_range_length_prop in Hna.
   unfold null_coeff_range_length_prop in Hnb.
   unfold null_coeff_range_length_prop in Hnc.
   simpl in Hna, Hnb, Hnc.
   destruct Hna as (Hia, Hna).
   destruct Hnb as (Hib, Hnb).
   destruct Hnc as (Hic, Hnc).
   rewrite <- Nat2Z.inj_add.
   apply Nat2Z.inj_iff.
   destruct (lt_dec (na + nb) nc) as [Hlt| Hge].
    apply Hic in Hlt.
    unfold convol_mul in Hlt.
    rewrite summation_only_one_non_0 with (v := na) in Hlt.
     rewrite Nat.add_comm, Nat.add_sub in Hlt.
     apply fld_eq_mul_0_l in Hlt; try assumption; contradiction.

     split; [ apply Nat.le_0_l | apply le_plus_l ].

     intros i (_, Hiab) Hina.
     destruct (lt_dec i na) as [Hilt| Hige].
      rewrite Hia; [ idtac | assumption ].
      rewrite rng_mul_0_l; reflexivity.

      apply Nat.nlt_ge in Hige.
      rewrite Hib; [ idtac | fast_omega Hiab Hina Hige ].
      rewrite rng_mul_0_r; reflexivity.

    apply Nat.nlt_ge in Hge.
    destruct (lt_dec nc (na + nb)) as [Hclt| Hcge].

bbb.

unfold order; simpl.
unfold cm_factor, cm; simpl.
remember (null_coeff_range_length R (ps_terms a) 0) as na eqn:Hna .
remember (null_coeff_range_length R (ps_terms b) 0) as nb eqn:Hnb .
symmetry in Hna, Hnb.
destruct na as [na| ].
 destruct nb as [nb| ].
  Focus 1.
  remember (series_stretch R (ps_polord b) (ps_terms a)) as sa eqn:Hsa .
  remember (series_stretch R (ps_polord a) (ps_terms b)) as sb eqn:Hsb .
  remember (null_coeff_range_length R (sa * sb)%ser 0) as nc eqn:Hnc .
  symmetry in Hnc.
  destruct nc as [nc| ].
   simpl.
   unfold Qeq; simpl.
   apply Z.mul_cancel_r; [ apply Pos2Z_ne_0 | idtac ].
   rewrite Z.mul_add_distr_r.
   rewrite Z.mul_add_distr_r.
   rewrite <- Z.add_assoc.
   rewrite <- Z.add_assoc.
   apply Z.add_cancel_l.
   symmetry.
   rewrite Z.add_comm, <- Z.add_assoc.
   apply Z.add_cancel_l.
bbb.

Lemma xxx : ∀ a lb,
  let _ := Kx in (* coq seems not to see the type of Kx *)
  List.map order ([a] * lb)%lap =
  List.map (λ b, (order a + order b)%Qbar) lb.
Proof.
intros a lb f'.
induction lb as [| b]; intros; [ reflexivity | simpl ].
subst f'.
unfold summation; simpl.
f_equal.
(* problème parce qu'il s'agit de eq et non Qeq *)
bbb.

Lemma yyy : ∀ pol ns g,
  ns ∈ newton_segments R pol
  → g = g_of_ns pol ns
    → ∀ m, m ∈ al g → (order m > 0)%Qbar.
Proof.
intros pol ns g Hns Hg m Hm.
subst g.
unfold g_of_ns in Hm.
remember (ac_root (Φq R pol ns)) as c₁ eqn:Hc₁ .
remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl eqn:Hpl .
remember (List.map (term_of_point R pol) pl) as tl eqn:Htl .
remember (List.map (λ t, power t) tl) as l₁ eqn:Hl₁ .
remember (list_seq_except 0 (length (al pol)) l₁) as l₂ eqn:Hl₂ .
simpl in Hm.
apply List.in_map with (f := order) in Hm.
rewrite xxx in Hm.
rewrite <- List.map_map in Hm.
bbb.

apply ps_list_in_split in Hm.
destruct Hm as (l1, (l2, Hm)).
rewrite lap_mul_add_distr_l in Hm.
bbb.

(* [Walker, p 101] «
     Since O(āh - ah.x^αh) > 0 and O(āl.x^(l.γ₁)) > β₁ we obtain
       f₁(x,y₁) = b₁.y₁^r + b₂.y₁^(r+1) + ... + g(x,y₁),
     where b₁ = c₁^j.Ψ(c₁) ≠ 0 and each power of y₁ in g(x,y₁) has
     a coefficient of positive order.
   »

     Specifically, according to our theorem f₁_eq_term_with_Ψ_plus_sum,
     g must be
       g(x,y₁) = x^(-β₁).[Σ(āh-ah.x^αh).x^(h.γ₁).(c₁+y₁)^h +
                          Σāl.x^(l.γ₁).(c₁+y₁)^l]
     and the i of the bi run from 0 to k - r in the development of
       y₁^r.(c₁+y₁)^j.Ψ(c₁+y₁)
     since the degree of this polynomial is
       r + j + (k - j - r)
 *)
Theorem zzz : ∀ pol ns j αj k αk c₁ r Ψ f₁ b₁ g,
  let _ := Kx in (* coq seems not to see the type of Kx *)
  ns ∈ newton_segments R pol
  → ini_pt ns = (Qnat j, αj)
    → fin_pt ns = (Qnat k, αk)
      → c₁ = ac_root (Φq R pol ns)
        → r = root_multiplicity acf c₁ (Φq R pol ns)
          → Ψ = quotient_phi_x_sub_c_pow_r R (Φq R pol ns) c₁ r
            → f₁ = pol₁ R pol (β ns) (γ ns) c₁
              → (b₁ = c₁ ^ j * apply_poly R Ψ c₁)%K
                → g = g_of_ns pol ns
                  → ∃ lb,
                    (∀ m, m ∈ al g → (order m > 0)%Qbar) ∧
                    (f₁ =
                     poly_summation Kx (List.seq 0 (k - r))
                       (λ h,
                        let bh := List.nth h [b₁ … lb] 0%K in
                        POL [0%ps; ps_monom bh 1 … []] ^ (r + h)) +
                     g)%pol.
Proof.
intros pol ns j αj k αk c₁ r Ψ f₁ b₁ g f' Hns Hini Hfin Hc₁ Hr HΨ Hf₁ Hb₁ Hg.
bbb.

End theorems.
