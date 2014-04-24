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

Fixpoint lap_ps_in α (R : ring α) a l :=
  match l with
  | [] => False
  | [b … m] => ¬(@lap_eq _ (ps_ring R) l []) ∧ (b = a)%ps ∨ lap_ps_in R a m
  end.

Arguments lap_ps_in _ _ a%ps l%lap.

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

Lemma lap_ps_in_compat : ∀ α (R : ring α) a b la lb,
  (a = b)%ps
  → @lap_eq _ (ps_ring R) la lb
    → lap_ps_in R a la
      → lap_ps_in R b lb.
Proof.
intros α R a b la lb Hab Hlab Hla.
revert a b Hab lb Hlab Hla.
induction la as [| c]; intros; [ contradiction | idtac ].
simpl in Hla.
destruct Hla as [(Hcla, Hca)| Hla].
 destruct lb as [| d]; [ contradiction | idtac ].
 apply lap_eq_cons_inv in Hlab.
 destruct Hlab as (Hcd, Hlab).
 left.
 split.
  intros H; apply Hcla; clear Hcla.
  rewrite <- H.
  constructor; assumption.

  rewrite <- Hcd, <- Hab; assumption.

 simpl.
 destruct lb as [| d].
  apply lap_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Hc, Hlab).
  eapply IHla; eassumption.

  apply lap_eq_cons_inv in Hlab.
  destruct Hlab as (Hcd, Hlab).
  right.
  eapply IHla; eassumption.
Qed.

Add Parametric Morphism α (R : ring α) : (lap_ps_in R)
  with signature eq_ps ==> (@lap_eq _ (ps_ring R)) ==> iff
  as list_in_eq_ps_morph.
Proof.
intros a b Hab la lb Hlab.
split; intros Hl.
 eapply lap_ps_in_compat; eassumption.

 symmetry in Hab, Hlab.
 eapply lap_ps_in_compat; eassumption.
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

  apply ps_null_coeff_range_length_inf_iff in Hnb.
  rewrite Hnb in Hab.
  apply ps_null_coeff_range_length_inf_iff in Hab.
  rewrite Hab in Hna; discriminate Hna.

 apply ps_null_coeff_range_length_inf_iff in Hna.
 rewrite Hna in Hab.
 symmetry in Hab.
 apply ps_null_coeff_range_length_inf_iff in Hab.
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
    apply ps_null_coeff_range_length_inf_iff in Hv.
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

Lemma order_mul : ∀ a b, (order (a * b)%ps = order a + order b)%Qbar.
Proof.
intros a b.
symmetry.
pose proof (ps_adjust_eq R a 0 (ps_polord b)) as Ha.
pose proof (ps_adjust_eq R b 0 (ps_polord a)) as Hb.
rewrite Hb in |- * at 1.
rewrite Ha in |- * at 1.
unfold order; simpl.
unfold cm_factor, cm; simpl.
do 2 rewrite series_shift_0.
remember (series_stretch R (ps_polord b) (ps_terms a)) as sa eqn:Hsa .
remember (series_stretch R (ps_polord a) (ps_terms b)) as sb eqn:Hsb .
remember (null_coeff_range_length R sa 0) as na eqn:Hna .
remember (null_coeff_range_length R sb 0) as nb eqn:Hnb .
remember (null_coeff_range_length R (sa * sb)%ser 0) as nc eqn:Hnc .
symmetry in Hna, Hnb, Hnc.
destruct na as [na| ].
 destruct nb as [nb| ].
  destruct nc as [nc| ].
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
     unfold convol_mul in Hnc.
     rewrite all_0_summation_0 in Hnc.
      exfalso; apply Hnc; reflexivity.

      intros h (_, Hhc).
      destruct (lt_dec h na) as [Hha| Hha].
       rewrite Hia; [ idtac | assumption ].
       rewrite rng_mul_0_l; reflexivity.

       destruct (lt_dec (nc - h) nb) as [Hhb| Hhb].
        rewrite Hib; [ idtac | assumption ].
        rewrite rng_mul_0_r; reflexivity.

        exfalso; fast_omega Hclt Hhc Hha Hhb.

     apply Nat.nlt_ge in Hcge.
     apply Nat.le_antisymm; assumption.

   exfalso.
   apply null_coeff_range_length_iff in Hna.
   apply null_coeff_range_length_iff in Hnb.
   apply null_coeff_range_length_iff in Hnc.
   unfold null_coeff_range_length_prop in Hna, Hnb, Hnc.
   simpl in Hna, Hnb, Hnc.
   destruct Hna as (Hia, Hna).
   destruct Hnb as (Hib, Hnb).
   pose proof (Hnc (na + nb)%nat) as Hnab.
   unfold convol_mul in Hnab.
   destruct (le_dec na nb) as [Hab| Hab].
    rewrite summation_only_one_non_0 with (v := na) in Hnab.
     rewrite Nat.add_comm, Nat.add_sub in Hnab.
     apply fld_eq_mul_0_l in Hnab; try assumption; contradiction.

     split; [ apply Nat.le_0_l | apply le_plus_l ].

     intros i (_, Hiab) Hina.
     destruct (lt_dec i na) as [Hilt| Hige].
      rewrite Hia; [ idtac | assumption ].
      rewrite rng_mul_0_l; reflexivity.

      apply Nat.nlt_ge in Hige.
      rewrite Hib; [ idtac | fast_omega Hiab Hina Hige ].
      rewrite rng_mul_0_r; reflexivity.

    apply Nat.nle_gt in Hab.
    rewrite summation_only_one_non_0 with (v := na) in Hnab.
     rewrite Nat.add_comm, Nat.add_sub in Hnab.
     apply fld_eq_mul_0_l in Hnab; try assumption; contradiction.

     split; [ apply Nat.le_0_l | apply le_plus_l ].

     intros i (_, Hiab) Hina.
     destruct (lt_dec i na) as [Hilt| Hige].
      rewrite Hia; [ idtac | assumption ].
      rewrite rng_mul_0_l; reflexivity.

      apply Nat.nlt_ge in Hige.
      rewrite Hib; [ idtac | fast_omega Hiab Hina Hige ].
      rewrite rng_mul_0_r; reflexivity.

  simpl.
  apply series_null_coeff_range_length_inf_iff in Hnb.
  rewrite Hnb in Hnc.
  rewrite rng_mul_0_r in Hnc.
  simpl in Hnc.
  rewrite null_coeff_range_length_series_0 in Hnc.
  subst nc; constructor.

 simpl.
 apply series_null_coeff_range_length_inf_iff in Hna.
 rewrite Hna in Hnc.
 rewrite rng_mul_0_l in Hnc.
 simpl in Hnc.
 rewrite null_coeff_range_length_series_0 in Hnc.
 subst nc; constructor.
Qed.

Lemma order_add : ∀ a b,
  (order (a + b)%ps ≥ Qbar.min (order a) (order b))%Qbar.
Proof.
intros a b.
unfold Qbar.ge.
set (k₁ := cm_factor a b).
set (k₂ := cm_factor b a).
set (v₁ := (ps_ordnum a * ' k₁)%Z).
set (v₂ := (ps_ordnum b * ' k₂)%Z).
set (n₁ := Z.to_nat (v₂ - Z.min v₁ v₂)).
set (n₂ := Z.to_nat (v₁ - Z.min v₁ v₂)).
pose proof (ps_adjust_eq R a n₂ k₁) as Ha.
pose proof (ps_adjust_eq R b n₁ k₂) as Hb.
rewrite Hb in |- * at 1.
rewrite Ha in |- * at 1.
rewrite eq_ps_add_add₂.
unfold ps_add₂.
unfold adjust_ps_from.
fold k₁ k₂.
fold v₁ v₂.
rewrite Z.min_comm.
fold n₁ n₂.
remember (adjust_ps R n₂ k₁ a) as pa eqn:Hpa .
remember (adjust_ps R n₁ k₂ b) as pb eqn:Hpb .
unfold order; simpl.
remember (ps_terms pa) as sa eqn:Hsa .
remember (ps_terms pb) as sb eqn:Hsb .
remember (null_coeff_range_length R sa 0) as na eqn:Hna .
remember (null_coeff_range_length R sb 0) as nb eqn:Hnb .
remember (null_coeff_range_length R (sa + sb)%ser 0) as nc eqn:Hnc .
symmetry in Hna, Hnb, Hnc.
destruct na as [na| ].
 destruct nb as [nb| ].
  destruct nc as [nc| ]; [ simpl | constructor ].
  apply Qbar.le_qfin.
  rewrite Hpa, Hpb; simpl.
  subst k₁ k₂ n₁ n₂; simpl.
  unfold cm_factor; simpl.
  subst v₁ v₂; simpl.
  unfold cm_factor; simpl.
  rewrite Pos.mul_comm.
  rewrite Qmin_same_den.
  unfold Qle; simpl.
  apply Z.mul_le_mono_nonneg_r; [ apply Pos2Z.is_nonneg | idtac ].
  remember (ps_ordnum a * ' ps_polord b)%Z as ab.
  remember (ps_ordnum b * ' ps_polord a)%Z as ba.
  rewrite Z2Nat.id.
   rewrite Z2Nat.id.
    rewrite Z.sub_sub_distr.
    rewrite Z.sub_diag, Z.add_0_l.
    rewrite Z.sub_sub_distr.
    rewrite Z.sub_diag, Z.add_0_l.
    rewrite Z.add_min_distr_l.
    apply Z.add_le_mono_l.
    rewrite <- Nat2Z.inj_min.
    apply Nat2Z.inj_le.
    apply null_coeff_range_length_iff in Hna.
    apply null_coeff_range_length_iff in Hnb.
    apply null_coeff_range_length_iff in Hnc.
    unfold null_coeff_range_length_prop in Hna, Hnb, Hnc.
    simpl in Hna, Hnb.
    remember ps_terms_add as f; simpl in Hnc; subst f.
    destruct Hna as (Hina, Hna).
    destruct Hnb as (Hinb, Hnb).
    destruct Hnc as (Hinc, Hnc).
    apply Nat.nlt_ge.
    intros Hc.
    apply Nat.min_glb_lt_iff in Hc.
    destruct Hc as (Hca, Hcb).
    apply Hina in Hca.
    apply Hinb in Hcb.
    rewrite Hca, Hcb in Hnc.
    rewrite rng_add_0_l in Hnc.
    apply Hnc; reflexivity.

    rewrite <- Z.sub_max_distr_l.
    rewrite Z.sub_diag.
    rewrite Z.max_comm, <- Z2Nat_id_max.
    apply Nat2Z.is_nonneg.

   rewrite <- Z.sub_max_distr_l.
   rewrite Z.sub_diag.
   rewrite <- Z2Nat_id_max.
   apply Nat2Z.is_nonneg.

  destruct nc as [nc| ]; [ simpl | constructor ].
  apply Qbar.le_qfin.
  unfold Qle; simpl.
  apply Z.mul_le_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
  apply Z.add_le_mono_l.
  apply Nat2Z.inj_le.
  apply series_null_coeff_range_length_inf_iff in Hnb.
  rewrite Hnb in Hnc.
  rewrite rng_add_0_r in Hnc.
  rewrite Hna in Hnc.
  injection Hnc; intros; subst na; reflexivity.

 simpl.
 apply series_null_coeff_range_length_inf_iff in Hna.
 rewrite Hna in Hnc.
 rewrite rng_add_0_l in Hnc.
 rewrite Hnb in Hnc; subst nc.
 destruct nb as [nb| ]; [ idtac | constructor ].
 apply Qbar.le_qfin.
 rewrite Hpa, Hpb; simpl.
 subst k₁ k₂ n₁ n₂; simpl.
 unfold cm_factor; simpl.
 subst v₁ v₂; simpl.
 unfold cm_factor; simpl.
 rewrite Pos.mul_comm.
 unfold Qle; simpl.
 apply Z.mul_le_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
 apply Z.add_le_mono_r.
 rewrite Z2Nat.id.
  rewrite Z2Nat.id.
   do 2 rewrite Z.sub_sub_distr.
   do 2 rewrite Z.sub_diag; simpl.
   reflexivity.

   rewrite <- Z.sub_max_distr_l.
   rewrite Z.sub_diag.
   rewrite <- Z2Nat_id_max.
   apply Nat2Z.is_nonneg.

  rewrite <- Z.sub_max_distr_l.
  rewrite Z.sub_diag.
  rewrite Z.max_comm.
  rewrite <- Z2Nat_id_max.
  apply Nat2Z.is_nonneg.
Qed.

(* to be moved *)
Theorem ps_zerop : ∀ a, {(a = 0)%ps} + {(a ≠ 0)%ps}.
Proof.
intros a.
destruct (Qbar.eq_dec (order a) Qbar.qinf) as [H| H].
 left.
 apply order_inf.
 unfold Qbar.qeq in H.
 destruct (order a); [ contradiction | reflexivity ].

 right.
 intros HH; apply H.
 apply order_inf in HH.
 rewrite HH; reflexivity.
Qed.

(* to be moved *)
Theorem ps_eq_dec : ∀ a b, {(a = b)%ps} + {(a ≠ b)%ps}.
Proof.
intros a b.
destruct (ps_zerop (a - b)%ps) as [H| H].
 left.
 apply rng_add_compat_r with (c := b) in H.
 rewrite <- rng_add_assoc in H.
 rewrite rng_add_opp_l in H.
 rewrite rng_add_0_r, rng_add_0_l in H.
 assumption.

 right.
 intros HH; apply H; clear H; rename HH into H.
 rewrite H.
 apply ps_add_opp_r.
Qed.

Lemma list_in_lap_ps_in : ∀ a l,
  (a ≠ 0)%ps
  → a ∈ l
    → lap_ps_in R a l.
Proof.
intros a l Ha Hal.
revert a Ha Hal.
induction l as [| x]; intros; [ assumption | idtac ].
destruct Hal as [Hal| Hal].
 subst a; left; split; [ idtac | reflexivity ].
 intros H.
 apply lap_eq_cons_nil_inv in H.
 destruct H; contradiction.

 right; apply IHl; assumption.
Qed.

(* to be moved *)
Lemma order_0 : order 0%ps = Qbar.qinf.
Proof.
unfold order; simpl.
rewrite null_coeff_range_length_series_0; reflexivity.
Qed.

Lemma lap_ps_nilp : ∀ la : list (puiseux_series α),
  {@lap_eq _ (ps_ring R) la []} +
  {not (@lap_eq _ (ps_ring R) la [])}.
Proof.
intros la.
induction la as [| a]; [ left; reflexivity | idtac ].
destruct IHla as [IHla| IHla].
 destruct (ps_zerop a) as [Ha| Ha].
  left.
  rewrite IHla, Ha.
  constructor; reflexivity.

  right.
  intros H; apply Ha.
  apply lap_eq_cons_nil_inv in H.
  destruct H; assumption.

 right.
 intros H; apply IHla.
 apply lap_eq_cons_nil_inv in H.
 destruct H; assumption.
Qed.

Lemma lap_ps_in_add : ∀ la lb,
  let _ := Kx in (* coq seems not to see the type of Kx *)
  (∀ m, lap_ps_in R m la → (order m > 0)%Qbar)
  → (∀ m, lap_ps_in R m lb → (order m > 0)%Qbar)
    → (∀ m, lap_ps_in R m (la + lb)%lap → (order m > 0)%Qbar).
Proof.
intros la lb f' Hla Hlb m Hlab; subst f'.
destruct (lap_ps_nilp la) as [Hlaz| Hlanz].
 rewrite Hlaz in Hlab.
 rewrite lap_add_nil_l in Hlab.
 apply Hlb; assumption.

 destruct (lap_ps_nilp lb) as [Hlbz| Hlbnz].
  rewrite Hlbz in Hlab.
  rewrite lap_add_nil_r in Hlab.
  apply Hla; assumption.

  revert lb Hlb Hlab Hlbnz.
  induction la as [| a]; intros.
   simpl in Hlab.
   apply Hlb; assumption.

   rename m into n.
   simpl in Hlab.
   destruct lb as [| b]; [ apply Hla; assumption | idtac ].
   simpl in Hlab.
   destruct Hlab as [(Hlab, Hab)| Hlab].
    unfold Qbar.gt.
    rewrite <- Hab.
    pose proof (order_add a b) as H.
    assert (order a > 0)%Qbar as Ha.
     apply Hla.
     left; split; [ assumption | reflexivity ].

     assert (order b > 0)%Qbar as Hb.
      apply Hlb.
      left; split; [ assumption | reflexivity ].

      unfold Qbar.ge in H.
      unfold Qbar.gt in Ha, Hb.
      destruct (Qbar.min_dec (order a) (order b)) as [Hoab| Hoab].
       rewrite Hoab in H.
       eapply Qbar.lt_le_trans; [ idtac | eassumption ].
       assumption.

       rewrite Hoab in H.
       eapply Qbar.lt_le_trans; [ idtac | eassumption ].
       assumption.

    destruct (ps_zerop a) as [Haz| Hanz].
     rewrite Haz in Hlanz.
     destruct (ps_zerop b) as [Hbz| Hbnz].
      rewrite Hbz in Hlbnz.
      eapply IHla.
       intros m Hm; apply Hla; right; assumption.

       intros HH; apply Hlanz.
       constructor; [ reflexivity | assumption ].

       intros m Hm; apply Hlb; right; eassumption.

       assumption.

       intros HH; apply Hlbnz.
       constructor; [ reflexivity | assumption ].

      clear Hlbnz.
      destruct (lap_ps_nilp lb) as [Hlbz| Hlbnz].
       rewrite Hlbz in Hlab.
       rewrite lap_add_nil_r in Hlab.
       apply Hla; right; assumption.

       eapply IHla.
        intros m Hm; apply Hla; right; assumption.

        intros HH; apply Hlanz.
        constructor; [ reflexivity | assumption ].

        intros m Hm; apply Hlb; right; eassumption.

        assumption.

        assumption.

     destruct (ps_zerop b) as [Hbz| Hbnz].
      rewrite Hbz in Hlbnz.
      clear Hlanz.
      destruct (lap_ps_nilp la) as [Hlaz| Hlanz].
       rewrite Hlaz in Hlab.
       rewrite lap_add_nil_l in Hlab.
       apply Hlb; right; assumption.

       eapply IHla.
        intros m Hm; apply Hla; right; assumption.

        assumption.

        intros m Hm; apply Hlb; right; eassumption.

        assumption.

        intros HH; apply Hlbnz.
        constructor; [ reflexivity | assumption ].

      clear Hlanz.
      clear Hlbnz.
      destruct (lap_ps_nilp la) as [Hlaz| Hlanz].
       rewrite Hlaz in Hlab.
       rewrite lap_add_nil_l in Hlab.
       apply Hlb; right; assumption.

       destruct (lap_ps_nilp lb) as [Hlbz| Hlbnz].
        rewrite Hlbz in Hlab.
        rewrite lap_add_nil_r in Hlab.
        apply Hla; right; assumption.

        eapply IHla.
         intros m Hm; apply Hla; right; assumption.

         assumption.

         intros m Hm; apply Hlb; right; eassumption.

         assumption.

         assumption.
Qed.

(* very close to 'lap_ps_in_add'. Is there a way to have only one lemma?
   or a lemma grouping these two together? *)
Lemma lap_ps_in_add_ge : ∀ la lb,
  let _ := Kx in (* coq seems not to see the type of Kx *)
  (∀ m, lap_ps_in R m la → (order m ≥ 0)%Qbar)
  → (∀ m, lap_ps_in R m lb → (order m ≥ 0)%Qbar)
    → (∀ m, lap_ps_in R m (la + lb)%lap → (order m ≥ 0)%Qbar).
Proof.
intros la lb f' Hla Hlb m Hlab; subst f'.
destruct (lap_ps_nilp la) as [Hlaz| Hlanz].
 rewrite Hlaz in Hlab.
 rewrite lap_add_nil_l in Hlab.
 apply Hlb; assumption.

 destruct (lap_ps_nilp lb) as [Hlbz| Hlbnz].
  rewrite Hlbz in Hlab.
  rewrite lap_add_nil_r in Hlab.
  apply Hla; assumption.

  revert lb Hlb Hlab Hlbnz.
  induction la as [| a]; intros.
   simpl in Hlab.
   apply Hlb; assumption.

   rename m into n.
   simpl in Hlab.
   destruct lb as [| b]; [ apply Hla; assumption | idtac ].
   simpl in Hlab.
   destruct Hlab as [(Hlab, Hab)| Hlab].
    unfold Qbar.gt.
    rewrite <- Hab.
    pose proof (order_add a b) as H.
    assert (order a ≥ 0)%Qbar as Ha.
     apply Hla.
     left; split; [ assumption | reflexivity ].

     assert (order b ≥ 0)%Qbar as Hb.
      apply Hlb.
      left; split; [ assumption | reflexivity ].

      unfold Qbar.ge in H.
      unfold Qbar.gt in Ha, Hb.
      destruct (Qbar.min_dec (order a) (order b)) as [Hoab| Hoab].
       rewrite Hoab in H.
       eapply Qbar.le_trans; [ idtac | eassumption ].
       assumption.

       rewrite Hoab in H.
       eapply Qbar.le_trans; [ idtac | eassumption ].
       assumption.

    destruct (ps_zerop a) as [Haz| Hanz].
     rewrite Haz in Hlanz.
     destruct (ps_zerop b) as [Hbz| Hbnz].
      rewrite Hbz in Hlbnz.
      eapply IHla.
       intros m Hm; apply Hla; right; assumption.

       intros HH; apply Hlanz.
       constructor; [ reflexivity | assumption ].

       intros m Hm; apply Hlb; right; eassumption.

       assumption.

       intros HH; apply Hlbnz.
       constructor; [ reflexivity | assumption ].

      clear Hlbnz.
      destruct (lap_ps_nilp lb) as [Hlbz| Hlbnz].
       rewrite Hlbz in Hlab.
       rewrite lap_add_nil_r in Hlab.
       apply Hla; right; assumption.

       eapply IHla.
        intros m Hm; apply Hla; right; assumption.

        intros HH; apply Hlanz.
        constructor; [ reflexivity | assumption ].

        intros m Hm; apply Hlb; right; eassumption.

        assumption.

        assumption.

     destruct (ps_zerop b) as [Hbz| Hbnz].
      rewrite Hbz in Hlbnz.
      clear Hlanz.
      destruct (lap_ps_nilp la) as [Hlaz| Hlanz].
       rewrite Hlaz in Hlab.
       rewrite lap_add_nil_l in Hlab.
       apply Hlb; right; assumption.

       eapply IHla.
        intros m Hm; apply Hla; right; assumption.

        assumption.

        intros m Hm; apply Hlb; right; eassumption.

        assumption.

        intros HH; apply Hlbnz.
        constructor; [ reflexivity | assumption ].

      clear Hlanz.
      clear Hlbnz.
      destruct (lap_ps_nilp la) as [Hlaz| Hlanz].
       rewrite Hlaz in Hlab.
       rewrite lap_add_nil_l in Hlab.
       apply Hlb; right; assumption.

       destruct (lap_ps_nilp lb) as [Hlbz| Hlbnz].
        rewrite Hlbz in Hlab.
        rewrite lap_add_nil_r in Hlab.
        apply Hla; right; assumption.

        eapply IHla.
         intros m Hm; apply Hla; right; assumption.

         assumption.

         intros m Hm; apply Hlb; right; eassumption.

         assumption.

         assumption.
Qed.

Lemma lap_ps_in_mul : ∀ la lb,
  let _ := Kx in (* coq seems not to see the type of Kx *)
  (∀ m, lap_ps_in R m la → (order m > 0)%Qbar)
  → (∀ m, lap_ps_in R m lb → (order m ≥ 0)%Qbar)
    → (∀ m, lap_ps_in R m (la * lb)%lap → (order m > 0)%Qbar).
Proof.
(* à nettoyer, surtout vers la fin : faire des lemmes *)
intros la lb f' Hla Hlb m Hlab; subst f'.
revert m lb Hlb Hlab.
induction la as [| a]; intros.
 rewrite lap_mul_nil_l in Hlab; contradiction.

 rewrite lap_mul_cons_l in Hlab.
 eapply lap_ps_in_add; [ idtac | idtac | eassumption ].
  intros n Hn.
  destruct (ps_zerop a) as [Ha| Ha].
   rewrite Ha in Hn.
   rewrite lap_eq_0 in Hn.
   rewrite lap_mul_nil_l in Hn; contradiction.

   assert (order a > 0)%Qbar as Hoa.
    apply Hla; left; split; [ idtac | reflexivity ].
    intros H.
    apply lap_eq_cons_nil_inv in H.
    destruct H; contradiction.

    rewrite lap_mul_const_l in Hn.
    revert Hlb Hn Hoa; clear; intros.
    induction lb as [| b]; [ contradiction | idtac ].
    simpl in Hn.
    destruct Hn as [(Hab, Hn)| Hn].
     simpl in Hn.
     pose proof (order_mul a b) as Ho.
     rewrite Hn in Ho.
     unfold Qbar.gt.
     rewrite Ho.
     remember (order a) as oa.
     remember (order b) as ob.
     symmetry in Heqoa, Heqob.
     destruct oa as [oa| ]; [ idtac | constructor ].
     destruct ob as [ob| ]; [ idtac | constructor ].
     unfold Qbar.add; simpl.
     apply Qbar.lt_qfin.
     apply Qlt_le_trans with (y := oa).
      apply Qbar.qfin_lt_mono.
      assumption.

      replace oa with (oa + 0) at 1 .
       apply Qplus_le_r.
       destruct (ps_zerop b) as [Hb| Hb].
        apply order_inf in Hb.
        rewrite Heqob in Hb; discriminate Hb.

        assert (lap_ps_in R b [b … lb]) as H.
         left.
         split; [ idtac | reflexivity ].
         intros H.
         apply lap_eq_cons_nil_inv in H.
         destruct H; contradiction.

         apply Hlb in H.
         rewrite Heqob in H.
         inversion H; assumption.

       unfold Qplus; simpl.
       rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
       destruct oa; reflexivity.

     apply IHlb; [ idtac | assumption ].
     intros p Hp.
     apply Hlb; right; assumption.

  intros n Hn.
  simpl in Hn.
  destruct Hn as [(Hab, Hn)| Hn].
   symmetry in Hn.
   apply order_inf in Hn.
   rewrite Hn; constructor.

   eapply IHla; try eassumption.
   intros p Hp.
   apply Hla; right; assumption.
Qed.

Lemma lap_ps_in_mul_ge : ∀ la lb,
  let _ := Kx in (* coq seems not to see the type of Kx *)
  (∀ m, lap_ps_in R m la → (order m ≥ 0)%Qbar)
  → (∀ m, lap_ps_in R m lb → (order m ≥ 0)%Qbar)
    → (∀ m, lap_ps_in R m (la * lb)%lap → (order m ≥ 0)%Qbar).
Proof.
intros la lb f' Hla Hlb m Hlab; subst f'.
revert m lb Hlb Hlab.
induction la as [| a]; intros.
 rewrite lap_mul_nil_l in Hlab; contradiction.

 rewrite lap_mul_cons_l in Hlab.
 eapply lap_ps_in_add_ge; [ idtac | idtac | eassumption ].
  intros n Hn.
  destruct (ps_zerop a) as [Ha| Ha].
   rewrite Ha in Hn.
   rewrite lap_eq_0 in Hn.
   rewrite lap_mul_nil_l in Hn; contradiction.

   assert (order a ≥ 0)%Qbar as Hoa.
    apply Hla; left; split; [ idtac | reflexivity ].
    intros H.
    apply lap_eq_cons_nil_inv in H.
    destruct H; contradiction.

    rewrite lap_mul_const_l in Hn.
    revert Hlb Hn Hoa; clear; intros.
bbb.
*)

Lemma lap_ps_in_summation : ∀ f l,
  (∀ i, i ∈ l → ∀ m, lap_ps_in R m (f i) → (order m > 0)%Qbar)
  → (∀ m, lap_ps_in R m (lap_summation Kx l f)%lap → (order m > 0)%Qbar).
Proof.
intros f l Hi m Hm.
revert m Hm.
induction l as [| j]; intros; [ contradiction | idtac ].
simpl in Hm.
apply lap_ps_in_add in Hm; [ assumption | idtac | idtac ].
 intros n Hn.
 apply IHl; [ idtac | assumption ].
 intros k Hk p Hp.
 eapply Hi; [ idtac | eassumption ].
 right; assumption.

 intros k Hk.
 eapply Hi; [ idtac | eassumption ].
 left; reflexivity.
Qed.

(* to be moved to the good file *)
Lemma lap_mul_summation : ∀ α (Kx : ring (puiseux_series α)) la l f,
  (la * lap_summation Kx l f = lap_summation Kx l (λ i, la * f i))%lap.
Proof.
clear.
intros α Kx la l f.
induction l as [| j]; intros; simpl.
 rewrite lap_mul_nil_r; reflexivity.

 rewrite lap_mul_add_distr_l, IHl.
 reflexivity.
Qed.

Lemma ps_monom_order : ∀ c n, (c ≠ 0)%K → order (ps_monom c n) = qfin n.
Proof.
intros c n Hc.
unfold order.
remember (null_coeff_range_length R (ps_terms (ps_monom c n)) 0) as m eqn:Hm .
symmetry in Hm.
apply null_coeff_range_length_iff in Hm.
unfold null_coeff_range_length_prop in Hm.
simpl in Hm; simpl.
destruct m as [m| ].
 destruct Hm as (Him, Hm).
 destruct m as [| m]; [ simpl | exfalso; apply Hm; reflexivity ].
 simpl in Hm.
 rewrite Z.add_0_r; destruct n; reflexivity.

 pose proof (Hm 0%nat); contradiction.
Qed.

Lemma ps_monom_order_ge : ∀ c n, (order (ps_monom c n) ≥ qfin n)%Qbar.
Proof.
intros c n.
unfold order.
remember (null_coeff_range_length R (ps_terms (ps_monom c n)) 0) as m eqn:Hm .
symmetry in Hm.
unfold Qbar.ge.
destruct m as [m| ]; [ idtac | constructor ].
apply Qbar.le_qfin.
apply null_coeff_range_length_iff in Hm.
unfold null_coeff_range_length_prop in Hm.
simpl in Hm; simpl.
destruct Hm as (Him, Hm).
destruct m as [| m]; [ simpl | exfalso; apply Hm; reflexivity ].
simpl in Hm.
rewrite Z.add_0_r; destruct n; simpl.
unfold Qle; simpl; reflexivity.
Qed.

Lemma lap_ps_in_power : ∀ la n,
  let _ := Kx in (* coq seems not to see the type of Kx *)
  (∀ a, lap_ps_in R a la → (order a ≥ 0)%Qbar)
  → (∀ m, lap_ps_in R m (la ^ n) → (order m ≥ 0)%Qbar).
Proof.
intros la n f' Ha m Hm.
revert m la Ha Hm.
induction n; intros.
 simpl in Hm.
 destruct Hm as [(H₁, Hm)| ]; [ idtac | contradiction ].
 unfold Qbar.ge.
 rewrite <- Hm.
 apply ps_monom_order_ge.

 simpl in Hm.
 eapply lap_ps_in_mul_ge in Hm; try eassumption.
 intros p Hp.
 eapply IHn; eassumption.
Qed.

Lemma yyy : ∀ pol ns g,
  ns ∈ newton_segments R pol
  → g = g_of_ns pol ns
    → ∀ m, m ∈ al g → (order m > 0)%Qbar.
Proof.
intros pol ns g Hns Hg m Hm.
remember (al g) as la eqn:Hla .
subst g.
unfold g_of_ns in Hla.
remember (ac_root (Φq R pol ns)) as c₁ eqn:Hc₁ .
remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl eqn:Hpl .
remember (List.map (term_of_point R pol) pl) as tl eqn:Htl .
remember (List.map (λ t, power t) tl) as l₁ eqn:Hl₁ .
remember (list_seq_except 0 (length (al pol)) l₁) as l₂ eqn:Hl₂ .
simpl in Hla.
remember (order m) as om eqn:Hom .
symmetry in Hom.
destruct om as [om| ]; [ idtac | constructor ].
assert (m ≠ 0)%ps as Hmnz.
 intros H.
 apply order_inf in H.
 rewrite H in Hom; discriminate Hom.

 subst la.
 apply list_in_lap_ps_in in Hm; [ idtac | assumption ].
 rewrite lap_mul_add_distr_l in Hm.
 rewrite <- Hom.
 apply lap_ps_in_add in Hm; [ assumption | idtac | idtac ].
  clear m om Hom Hmnz Hm.
  intros m Hm.
  rewrite lap_mul_summation in Hm.
  eapply lap_ps_in_summation; [ idtac | eassumption ].
  clear m Hm.
  intros h Hh m Hm.
  simpl in Hm.
  rewrite lap_mul_assoc in Hm.
  apply lap_ps_in_mul in Hm; [ assumption | idtac | idtac ].
   clear m Hm.
   intros m Hm.
   remember (poly_nth R h pol) as āh eqn:Hāh .
   remember (ps_monom (coeff_of_term R h tl) 0) as ah eqn:Hah .
   remember (ord_of_pt h pl) as αh eqn:Hαh .
   rewrite lap_mul_const_l in Hm; simpl in Hm.
   destruct Hm as [(Hmnz, Hm)| ]; [ idtac | contradiction ].
   unfold Qbar.gt.
   rewrite <- Hm; simpl.
   rewrite order_mul.
   remember (āh - ah * ps_monom 1%K αh)%ps as aa.
   remember (ps_monom 1%K (Qnat h * γ ns))%ps as bb.
   remember (ps_monom 1%K (- β ns)) as cc.
   remember (order (aa * bb)) as oaa.
   apply Qbar.lt_le_trans with (m := (qfin (- β ns) + oaa)%Qbar).
    Focus 2.
    destruct oaa as [oaa| ].
     apply Qbar.add_le_mono_r; [ intros H; discriminate H | idtac ].
     subst cc; apply ps_monom_order_ge.

     simpl.
     rewrite Qbar.add_comm; constructor.

    subst oaa.
    rewrite order_mul.
    rewrite Qbar.add_comm.
    rewrite Heqaa, Heqbb.
    apply Qbar.le_lt_trans with (m := qfin (αh + Qnat h * γ ns - β ns)).
     apply Qbar.le_qfin.
     apply Qplus_le_l with (z := β ns).
     rewrite <- Qminus_minus_assoc.
     rewrite Qminus_diag.
     rewrite Qplus_0_l.
     unfold Qminus, Qopp; simpl.
     rewrite Qplus_0_r.
     remember (points_of_ps_polynom R pol) as pts.
     eapply points_in_convex; try eassumption.
     eapply in_pol_in_pts; try eassumption.
     rewrite Hāh.
     eapply order_in_newton_segment; try eassumption.
     rewrite Hαh.
     apply ord_is_ord_of_pt.
      rewrite Hpl.
      eapply ini_oth_fin_pts_sorted; eassumption.

      intros pt Hpt.
      rewrite Hpl in Hpt.
      eapply points_in_newton_segment_have_nat_abscissa; eassumption.

      rewrite Hl₁, Htl in Hh.
      rewrite List.map_map in Hh; assumption.

     unfold Qminus.
     rewrite Qbar.qfin_inj_add.
     apply Qbar.add_lt_mono_r; [ intros H; discriminate H | idtac ].
     rewrite Qbar.qfin_inj_add.
     apply Qbar.add_lt_le_mono; [ intros H; discriminate H | idtac | idtac ].
      rewrite Hl₁ in Hh.
      eapply order_āh_minus_ah_xαh_gt_αh; eassumption.

      apply ps_monom_order_ge.

   clear m Hm.
   intros m Hm.
   eapply lap_ps_in_power; [ idtac | eassumption ].
   clear m Hm.
   intros m Hm.
   simpl in Hm.
   destruct Hm as [(Hn, Hm)| Hm].
    rewrite <- Hm.
    apply ps_monom_order_ge.

    destruct Hm as [(Hn, Hm)| ]; [ idtac | contradiction ].
    rewrite <- Hm.
    apply ps_monom_order_ge.

  clear m om Hom Hmnz Hm.
  intros m Hm.
  rewrite lap_mul_summation in Hm.
  eapply lap_ps_in_summation; [ idtac | eassumption ].
  clear m Hm.
  intros h Hh m Hm.
  simpl in Hm.
  rewrite lap_mul_assoc in Hm.
bbb.
Check order_āl_xlγ₁_gt_β₁

  apply lap_ps_in_mul in Hm; [ assumption | idtac | idtac ].
   clear m Hm.
   intros m Hm.
   simpl in Hm.
   destruct Hm as [(H₁, H₂)| Hm]; [ idtac | contradiction ].
   unfold summation in H₁, H₂; simpl in H₁, H₂.
   rewrite ps_add_0_r in H₂.
   rewrite <- H₂.
   rewrite order_mul.
   rewrite order_mul.
bbb.
Check order_āl_xlγ₁_gt_β₁

    eapply list_in_eq_ps_compat in Hm; [ idtac | assumption | idtac ].
     2: rewrite lap_mul_summation; reflexivity.

     eapply list_in_eq_summation; [ idtac | eassumption ].
     clear m Hom Hmnz Hm.
     intros h Hh m Hm; simpl in Hm.
     remember (poly_nth R h pol) as āh eqn:Hāh .
     remember (ps_monom (coeff_of_term R h tl) 0) as ah eqn:Hah .
     remember (ord_of_pt h pl) as αh eqn:Hαh .
     clear om.
     remember (order m) as om eqn:Hom .
     symmetry in Hom.
     destruct om as [om| ]; [ idtac | constructor ].
     assert (m ≠ 0)%ps as Hmnz.
      intros H.
      apply order_inf in H.
      rewrite H in Hom; discriminate Hom.

      rewrite <- Hom.
      eapply list_in_eq_ps_compat in Hm; [ idtac | assumption | idtac ].
       2: rewrite lap_mul_assoc; reflexivity.

       eapply list_in_eq_mul; [ idtac | idtac | eassumption ].
bbb.

apply List.in_map with (f := order) in Hm.
unfold Qbar.gt; simpl.
bbb.

remember (order m) as mo eqn:Hmo .
symmetry in Hmo.
destruct mo as [mo| ]; [ idtac | constructor ].
apply Qbar.lt_qfin.
unfold Qlt; simpl.
rewrite Z.mul_1_r.
bbb.

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
