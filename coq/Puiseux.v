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

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Lemma order_in_newton_segment : ∀ pol ns pl h αh,
  ns ∈ newton_segments pol
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
  ns ∈ newton_segments pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point R pol) pl
      → h ∈ List.map (λ t, power t) tl
        → āh = poly_nth R h pol
          → ah = ps_monom (coeff_of_term R h tl) 0
            → αh = ord_of_pt h pl
              → (order (āh - ah * ps_monom 1%K αh)%ps > qfin αh)%Qbar.
Proof.
intros pol ns pl tl h āh ah αh Hns Hpl Htl Hh Hāh Hah Hαh.
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
 apply ord_is_ord_of_pt; [ idtac | idtac | assumption ].
  rewrite Hpl.
  eapply ini_oth_fin_pts_sorted; eassumption.

  intros pt Hpt.
  eapply points_in_newton_segment_have_nat_abscissa; [ eassumption | idtac ].
  subst pl; assumption.
Qed.

(* [Walker, p 101] « O(āl.x^(l.γ₁)) > β₁ » *)
Theorem order_āl_xlγ₁_gt_β₁ : ∀ pol ns pl tl l₁ l₂ l āl,
  ns ∈ newton_segments pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point R pol) pl
      → l₁ = List.map (λ t, power t) tl
        → split_list (List.seq 0 (length (al pol))) l₁ l₂
          → l ∈ l₂
            → āl = poly_nth R l pol
              → (order (āl * ps_monom 1%K (Qnat l * γ ns))%ps >
                 qfin (β ns))%Qbar.
Proof.
intros pol ns pl tl l₁ l₂ l āl Hns Hpl Htl Hl₁ Hsl Hl Hāl.
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

Definition g_lap_of_ns pol ns :=
  let c₁ := ac_root (Φq R pol ns) in
  let pl := [ini_pt ns … oth_pts ns ++ [fin_pt ns]] in
  let tl := List.map (term_of_point R pol) pl in
  let l₁ := List.map (λ t, power t) tl in
  let l₂ := list_seq_except 0 (length (al pol)) l₁ in
  ([ps_monom 1%K (- β ns)] *
   (ps_lap_summ l₁
      (λ h,
       let āh := poly_nth R h pol in
       let ah := ps_monom (coeff_of_term R h tl) 0 in
       let αh := ord_of_pt h pl in
       [((āh - ah * ps_monom 1%K αh) * ps_monom 1%K (Qnat h * γ ns))%ps] *
       [ps_monom c₁ 0; 1%ps … []] ^ h) +
    ps_lap_summ l₂
      (λ l,
       let āl := poly_nth R l pol in
       [(āl * ps_monom 1%K (Qnat l * γ ns))%ps] *
       [ps_monom c₁ 0; 1%ps … []] ^ l)))%pslap.

Definition g_of_ns pol ns := (POL (g_lap_of_ns pol ns))%pol.

(*
Definition g_of_ns pol ns :=
  let c₁ := ac_root (Φq R pol ns) in
  let pl := [ini_pt ns … oth_pts ns ++ [fin_pt ns]] in
  let tl := List.map (term_of_point R pol) pl in
  let l₁ := List.map (λ t, power t) tl in
  let l₂ := list_seq_except 0 (length (al pol)) l₁ in
  (POL [ps_monom 1%K (- β ns)] *
   (ps_pol_summ l₁
      (λ h,
       let āh := poly_nth R h pol in
       let ah := ps_monom (coeff_of_term R h tl) 0 in
       let αh := ord_of_pt h pl in
       POL [((āh - ah * ps_monom 1%K αh) *
             ps_monom 1%K (Qnat h * γ ns))%ps] *
       POL [ps_monom c₁ 0; 1%ps … []] ^ h) +
    ps_pol_summ l₂
      (λ l,
       let āl := poly_nth R l pol in
       POL [(āl * ps_monom 1%K (Qnat l * γ ns))%ps] *
       POL [ps_monom c₁ 0; 1%ps … []] ^ l)))%pspol.
*)

Lemma ps_list_in_split : ∀ (a : puiseux_series α) la,
  a ∈ la
  → ∃ l1 l2, (la = l1 ++ [a … l2])%pslap.
Proof.
intros a la Ha.
unfold ps_lap_eq.
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

Lemma lap_ps_nilp : ∀ la : list (puiseux_series α),
  {@lap_eq _ (ps_ring R) la []} +
  {not (@lap_eq _ (ps_ring R) la [])}.
Proof.
intros la.
induction la as [| a]; [ left; reflexivity | idtac ].
destruct IHla as [IHla| IHla].
 destruct (ps_zerop _ a) as [Ha| Ha].
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
  (∀ m, lap_ps_in R m la → (order m > 0)%Qbar)
  → (∀ m, lap_ps_in R m lb → (order m > 0)%Qbar)
    → (∀ m, lap_ps_in R m (la + lb)%pslap → (order m > 0)%Qbar).
Proof.
intros la lb Hla Hlb m Hlab.
unfold ps_lap_add in Hlab.
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

    destruct (ps_zerop _ a) as [Haz| Hanz].
     rewrite Haz in Hlanz.
     destruct (ps_zerop _ b) as [Hbz| Hbnz].
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

     destruct (ps_zerop _ b) as [Hbz| Hbnz].
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
  (∀ m, lap_ps_in R m la → (order m ≥ 0)%Qbar)
  → (∀ m, lap_ps_in R m lb → (order m ≥ 0)%Qbar)
    → (∀ m, lap_ps_in R m (la + lb)%pslap → (order m ≥ 0)%Qbar).
Proof.
intros la lb Hla Hlb m Hlab.
unfold ps_lap_add in Hlab.
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

    destruct (ps_zerop _ a) as [Haz| Hanz].
     rewrite Haz in Hlanz.
     destruct (ps_zerop _ b) as [Hbz| Hbnz].
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

     destruct (ps_zerop _ b) as [Hbz| Hbnz].
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
  (∀ m, lap_ps_in R m la → (order m > 0)%Qbar)
  → (∀ m, lap_ps_in R m lb → (order m ≥ 0)%Qbar)
    → (∀ m, lap_ps_in R m (la * lb)%pslap → (order m > 0)%Qbar).
Proof.
intros la lb Hla Hlb m Hlab.
unfold ps_lap_mul in Hlab.
revert m lb Hlb Hlab.
induction la as [| a]; intros.
 rewrite lap_mul_nil_l in Hlab; contradiction.

 rewrite lap_mul_cons_l in Hlab.
 eapply lap_ps_in_add; [ idtac | idtac | eassumption ].
  intros n Hn.
  destruct (ps_zerop _ a) as [Ha| Ha].
   rewrite Ha in Hn.
   rewrite lap_eq_0 in Hn.
   rewrite lap_mul_nil_l in Hn; contradiction.

   assert (order a > 0)%Qbar as Hoa.
    apply Hla; left; split; [ idtac | reflexivity ].
    intros H.
    apply lap_eq_cons_nil_inv in H.
    destruct H; contradiction.

    revert Hlb Hn Hoa; clear; intros.
    rewrite lap_mul_const_l in Hn.
    induction lb as [| b]; [ contradiction | idtac ].
    simpl in Hn.
    destruct Hn as [(Hab, Hn)| Hn].
     rewrite <- Hn, order_mul.
     eapply Qbar.lt_le_trans; [ eassumption | idtac ].
     apply Qbar.le_sub_le_add_l.
     rewrite Qbar.sub_diag.
     destruct (ps_zerop _ b) as [Hb| Hb].
      rewrite Hb, order_0; constructor.

      apply Hlb; left; split; [ idtac | reflexivity ].
      intros H; apply Hb.
      apply lap_eq_cons_nil_inv in H.
      destruct H; assumption.

     apply IHlb; [ idtac | assumption ].
     intros p Hp.
     apply Hlb; right; assumption.

  intros n Hn.
  simpl in Hn.
  destruct Hn as [(Hab, Hn)| Hn].
   symmetry in Hn.
   rewrite Hn, order_0; constructor.

   eapply IHla; try eassumption.
   intros p Hp.
   apply Hla; right; assumption.
Qed.

Lemma lap_ps_in_mul_ge : ∀ la lb,
  (∀ m, lap_ps_in R m la → (order m ≥ 0)%Qbar)
  → (∀ m, lap_ps_in R m lb → (order m ≥ 0)%Qbar)
    → (∀ m, lap_ps_in R m (la * lb)%pslap → (order m ≥ 0)%Qbar).
Proof.
intros la lb Hla Hlb m Hlab.
unfold ps_lap_mul in Hlab.
revert m lb Hlb Hlab.
induction la as [| a]; intros.
 rewrite lap_mul_nil_l in Hlab; contradiction.

 rewrite lap_mul_cons_l in Hlab.
 eapply lap_ps_in_add_ge; [ idtac | idtac | eassumption ].
  intros n Hn.
  destruct (ps_zerop _ a) as [Ha| Ha].
   rewrite Ha in Hn.
   rewrite lap_eq_0 in Hn.
   rewrite lap_mul_nil_l in Hn; contradiction.

   assert (order a ≥ 0)%Qbar as Hoa.
    apply Hla; left; split; [ idtac | reflexivity ].
    intros H.
    apply lap_eq_cons_nil_inv in H.
    destruct H; contradiction.

    revert Hlb Hn Hoa; clear; intros.
    rewrite lap_mul_const_l in Hn.
    induction lb as [| b]; [ contradiction | idtac ].
    simpl in Hn.
    destruct Hn as [(Hab, Hn)| Hn].
     rewrite <- Hn, order_mul.
     eapply Qbar.le_trans; [ eassumption | idtac ].
     apply Qbar.le_sub_le_add_l.
     rewrite Qbar.sub_diag.
     destruct (ps_zerop _ b) as [Hb| Hb].
      rewrite Hb, order_0; constructor.

      apply Hlb; left; split; [ idtac | reflexivity ].
      intros H; apply Hb.
      apply lap_eq_cons_nil_inv in H.
      destruct H; assumption.

     apply IHlb; [ idtac | assumption ].
     intros p Hp.
     apply Hlb; right; assumption.

  intros n Hn.
  simpl in Hn.
  destruct Hn as [(Hab, Hn)| Hn].
   symmetry in Hn.
   rewrite Hn, order_0; constructor.

   eapply IHla; try eassumption.
   intros p Hp.
   apply Hla; right; assumption.
Qed.

Lemma lap_ps_in_summation : ∀ f l,
  (∀ i, i ∈ l → ∀ m, lap_ps_in R m (f i) → (order m > 0)%Qbar)
  → (∀ m, lap_ps_in R m (ps_lap_summ l f)%lap → (order m > 0)%Qbar).
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

Lemma ps_monom_0_order : ∀ c n, (c = 0)%K → order (ps_monom c n) = qinf.
Proof.
intros c n Hc.
unfold order.
remember (null_coeff_range_length R (ps_terms (ps_monom c n)) 0) as m eqn:Hm .
symmetry in Hm.
apply null_coeff_range_length_iff in Hm.
unfold null_coeff_range_length_prop in Hm.
simpl in Hm; simpl.
destruct m as [m| ]; [ exfalso | reflexivity ].
destruct Hm as (Him, Hm).
destruct m as [| m]; apply Hm; [ assumption | reflexivity ].
Qed.

Lemma ps_const_order : ∀ a c,
  (c ≠ 0)%K
  → a = ps_monom c 0
    → (order a = 0)%Qbar.
Proof.
intros a c Hc Ha; subst a.
rewrite ps_monom_order; [ reflexivity | assumption ].
Qed.

Lemma ps_monom_order_opp_r : ∀ c n,
  (c ≠ 0)%K
  → order (ps_monom c (- n)) = (- order (ps_monom c n))%Qbar.
Proof.
intros c n Hc.
rewrite ps_monom_order; [ idtac | assumption ].
rewrite ps_monom_order; [ idtac | assumption ].
reflexivity.
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
  (∀ a, lap_ps_in R a la → (order a ≥ 0)%Qbar)
  → (∀ m, lap_ps_in R m (la ^ n)%pslap → (order m ≥ 0)%Qbar).
Proof.
intros la n Ha m Hm.
revert m la Ha Hm.
induction n; intros.
 simpl in Hm.
 destruct Hm as [(H₁, Hm)| ]; [ idtac | contradiction ].
 rewrite <- Hm.
 apply ps_monom_order_ge.

 simpl in Hm.
 eapply lap_ps_in_mul_ge in Hm; try eassumption.
 intros p Hp.
 eapply IHn; eassumption.
Qed.

(* [Walker, p 101: « each power of y₁ in g(x,y₁) has a coefficient of
   positive order » *)
Lemma each_power_of_y₁_has_coeff_pos_ord : ∀ pol ns g,
  ns ∈ newton_segments pol
  → g = g_of_ns pol ns
    → ∀ m, m ∈ al g → (order m > 0)%Qbar.
Proof.
intros pol ns g Hns Hg m Hm.
remember (al g) as la eqn:Hla .
subst g.
unfold g_of_ns, g_lap_of_ns in Hla.
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
 progress unfold ps_lap_add in Hm.
 progress unfold ps_lap_mul in Hm.
 rewrite lap_mul_add_distr_l in Hm.
 rewrite <- Hom.
 apply lap_ps_in_add in Hm; [ assumption | idtac | idtac ].
  clear m om Hom Hmnz Hm.
  intros m Hm.
  progress unfold ps_lap_summ in Hm.
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
  progress unfold ps_lap_summ in Hm.
  rewrite lap_mul_summation in Hm.
  eapply lap_ps_in_summation; [ idtac | eassumption ].
  clear m Hm.
  intros h Hh m Hm.
  simpl in Hm.
  rewrite lap_mul_assoc in Hm.
  apply lap_ps_in_mul in Hm; [ assumption | idtac | idtac ].
   clear m Hm.
   intros m Hm.
   simpl in Hm.
   destruct Hm as [(H₁, H₂)| Hm]; [ idtac | contradiction ].
   unfold summation in H₁, H₂; simpl in H₁, H₂.
   rewrite ps_add_0_r in H₂.
   rewrite <- H₂.
   rewrite order_mul.
   remember (poly_nth R h pol) as āh.
   apply Qbar.lt_sub_lt_add_l; [ intros H; discriminate H | idtac ].
   rewrite Qbar.sub_0_l.
   destruct (ac_zerop 1%K) as [Hoz| Honz].
    rewrite ps_monom_0_order; [ simpl | assumption ].
    rewrite order_mul.
    rewrite ps_monom_0_order; [ simpl | assumption ].
    rewrite Qbar.add_comm; constructor.

    rewrite ps_monom_order; [ simpl | assumption ].
    rewrite Qopp_opp.
    eapply order_āl_xlγ₁_gt_β₁; try eassumption.
    apply except_split_seq; [ idtac | idtac | assumption ].
     subst l₁ tl.
     rewrite List.map_map; simpl.
     apply Sorted_map; simpl.
     remember Hns as Hsort; clear HeqHsort.
     apply ini_oth_fin_pts_sorted in Hsort.
     rewrite <- Hpl in Hsort.
     pose proof (points_in_newton_segment_have_nat_abscissa R pol ns Hns)
      as Hnat.
     rewrite <- Hpl in Hnat.
     revert Hsort Hnat; clear; intros.
     induction pl as [| p]; [ constructor | idtac ].
     apply Sorted_inv in Hsort.
     destruct Hsort as (Hsort, Hrel).
     constructor.
      apply IHpl; [ assumption | idtac ].
      intros pt Hpt.
      apply Hnat; right; assumption.

      revert Hrel Hnat; clear; intros.
      induction pl as [| q]; constructor.
      apply HdRel_inv in Hrel.
      unfold fst_lt in Hrel; simpl.
      unfold nofq; simpl.
      assert (p ∈ [p; q … pl]) as Hp by (left; reflexivity).
      assert (q ∈ [p; q … pl]) as Hq by (right; left; reflexivity).
      apply Hnat in Hp.
      apply Hnat in Hq.
      destruct Hp as (h, (αh, Hp)).
      destruct Hq as (i, (αi, Hq)).
      subst p q; simpl in Hrel; simpl.
      do 2 rewrite Nat2Z.id.
      unfold Qnat in Hrel.
      unfold Qlt in Hrel; simpl in Hrel.
      do 2 rewrite Z.mul_1_r in Hrel.
      apply Nat2Z.inj_lt in Hrel.
      assumption.

     subst l₁; simpl.
     apply List.Forall_forall; intros i Hi.
     split; [ apply Nat.le_0_l | idtac ].
     subst tl; simpl in Hi.
     rewrite List.map_map in Hi.
     simpl in Hi.
     revert Hns Hpl Hi; clear; intros.
     apply ord_is_ord_of_pt in Hi.
      rewrite Hpl in Hi at 2.
      unfold newton_segments in Hns.
      eapply ns_in_init_pts in Hi; [ idtac | eassumption ].
      eapply in_pts_in_pol with (def := 0%ps) in Hi; try reflexivity.
      destruct Hi as (Hi, Ho).
      apply Nat.nle_gt.
      intros H.
      apply List.nth_overflow with (d := 0%ps) in H.
      rewrite H in Ho.
      rewrite order_0 in Ho.
      discriminate Ho.

      rewrite Hpl.
      eapply ini_oth_fin_pts_sorted; eassumption.

      intros pt Hpt.
      subst pl.
      eapply points_in_newton_segment_have_nat_abscissa; eassumption.

   clear m Hm.
   intros m Hm.
   eapply lap_ps_in_power; [ idtac | eassumption ].
   intros a Ha.
   simpl in Ha.
   destruct Ha as [(Hn, Ha)| Ha].
    rewrite <- Ha.
    apply ps_monom_order_ge.

    destruct Ha as [(_, Ha)| Ha]; [ idtac | contradiction ].
    rewrite <- Ha; simpl.
    apply ps_monom_order_ge.
Qed.

Lemma lap_nth_add : ∀ n la lb,
  (lap_nth R n (la + lb) = lap_nth R n la + lap_nth R n lb)%ps.
Proof.
intros n la lb.
unfold ps_lap_add; simpl.
unfold lap_nth; simpl.
revert n lb.
induction la as [| a]; intros; simpl.
 rewrite match_id, ps_add_0_l; reflexivity.

 destruct lb as [| b]; simpl.
  rewrite match_id, ps_add_0_r; reflexivity.

  destruct n; [ reflexivity | apply IHla ].
Qed.

Lemma eq_poly_lap_add : ∀ α (R : ring α) la lb,
  (POL la + POL lb = POL (la + lb)%lap)%pol.
Proof. reflexivity. Qed.

Lemma eq_poly_lap_mul : ∀ α (R : ring α) la lb,
  (POL la * POL lb = POL (la * lb)%lap)%pol.
Proof. reflexivity. Qed.

Lemma eq_poly_lap_pow : ∀ α (R : ring α) la n,
  (POL la ^ n = POL (la ^ n)%lap)%pol.
Proof. reflexivity. Qed.

Lemma ps_poly_lap_summ : ∀ f g l,
  (∀ i, (f i = POL (g i))%pspol)
  → (ps_pol_summ l f = POL (ps_lap_summ l g))%pspol.
Proof.
intros f g l Hi.
unfold ps_pol_eq, ps_pol in Hi.
unfold ps_pol_eq, ps_pol, ps_pol_summ, ps_lap_summ.
induction l as [| x]; [ reflexivity | simpl ].
rewrite <- eq_poly_lap_add.
rewrite <- IHl, <- Hi.
reflexivity.
Qed.

(* things similar with order_add, perhaps good lemmas? *)
Lemma order_neq_min : ∀ a b,
  (order a ≠ order b)%Qbar
  → (order (a + b) = Qbar.min (order a) (order b))%Qbar.
Proof.
intros a b Hab.
set (k₁ := cm_factor a b).
set (k₂ := cm_factor b a).
set (v₁ := (ps_ordnum a * ' k₁)%Z).
set (v₂ := (ps_ordnum b * ' k₂)%Z).
set (n₁ := Z.to_nat (v₂ - Z.min v₁ v₂)).
set (n₂ := Z.to_nat (v₁ - Z.min v₁ v₂)).
pose proof (ps_adjust_eq R a n₂ k₁) as Ha.
pose proof (ps_adjust_eq R b n₁ k₂) as Hb.
symmetry.
rewrite Hb in Hab.
rewrite Ha in Hab.
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
remember (order pa) as opa eqn:Hopa .
remember (order pb) as opb eqn:Hopb .
progress unfold order in Hopa, Hopb.
progress unfold order; simpl.
remember (ps_terms pa) as sa eqn:Hsa .
remember (ps_terms pb) as sb eqn:Hsb .
remember (null_coeff_range_length R sa 0) as na eqn:Hna .
remember (null_coeff_range_length R sb 0) as nb eqn:Hnb .
remember (null_coeff_range_length R (sa + sb)%ser 0) as nc eqn:Hnc .
symmetry in Hna, Hnb, Hnc.
clear Hsa Hsb Ha Hb.
apply null_coeff_range_length_iff in Hna.
apply null_coeff_range_length_iff in Hnb.
apply null_coeff_range_length_iff in Hnc.
unfold null_coeff_range_length_prop in Hna, Hnb, Hnc.
simpl in Hna, Hnb, Hnc.
destruct na as [na| ].
 destruct Hna as (Hina, Hna).
 destruct nb as [nb| ].
  destruct Hnb as (Hinb, Hnb).
  subst pa pb; simpl in Hopa, Hopb; simpl.
  subst k₁ k₂ n₁ n₂; simpl in Hopa, Hopb; simpl.
  progress unfold cm_factor in Hopa, Hopb; simpl in Hopa, Hopb.
  subst v₁ v₂; simpl in Hopa, Hopb.
  progress unfold cm_factor in Hopa, Hopb; simpl in Hopa, Hopb.
  rewrite Pos.mul_comm in Hopb.
  rewrite Z2Nat.id in Hopa.
   rewrite Z2Nat.id in Hopb.
    rewrite Z.sub_sub_distr in Hopa, Hopb.
    rewrite Z.sub_diag, Z.add_0_l in Hopa, Hopb.
    unfold cm_factor; simpl.
    rewrite Z2Nat.id.
     rewrite Z.sub_sub_distr.
     rewrite Z.sub_diag, Z.add_0_l.
     subst opa opb; simpl.
     rewrite Qmin_same_den.
     unfold Qeq; simpl.
     simpl in Hab.
     unfold Qeq in Hab; simpl in Hab.
     destruct nc as [nc| ].
      destruct Hnc as (Hinc, Hnc).
      apply Z.mul_cancel_r; [ apply Pos2Z_ne_0 | idtac ].
      rewrite Z.add_min_distr_l.
      apply Z.add_cancel_l.
      rewrite <- Nat2Z.inj_min.
      apply Nat2Z.inj_iff.
      destruct (eq_nat_dec (min na nb) nc) as [| H]; [ assumption | idtac ].
      exfalso; apply Hab; clear Hab.
      apply Z.mul_cancel_r; [ apply Pos2Z_ne_0 | idtac ].
      apply Z.add_cancel_l.
      apply Nat2Z.inj_iff.
      destruct (eq_nat_dec na nb) as [| Hab]; [ assumption | idtac ].
      exfalso; apply H; clear H.
      destruct (le_dec na nb) as [H₁| H₁].
       apply le_neq_lt in H₁; [ idtac | assumption ].
       destruct (lt_dec na nc) as [H₂| H₂].
        apply Hinb in H₁.
        apply Hinc in H₂.
        rewrite H₁, rng_add_0_r in H₂; contradiction.

        apply Nat.nlt_ge in H₂.
        destruct (eq_nat_dec na nc) as [H₃| H₃].
         rewrite Nat.min_l; [ assumption | idtac ].
         apply Nat.lt_le_incl; assumption.

         apply Nat.neq_sym in H₃.
         apply le_neq_lt in H₂; [ idtac | assumption ].
         eapply Nat.lt_trans in H₁; [ idtac | eassumption ].
         apply Hina in H₂.
         apply Hinb in H₁.
         rewrite H₂, H₁ in Hnc.
         rewrite rng_add_0_l in Hnc.
         exfalso; apply Hnc; reflexivity.

       apply Nat.nle_gt in H₁.
       destruct (lt_dec nb nc) as [H₂| H₂].
        apply Hina in H₁.
        apply Hinc in H₂.
        rewrite H₁, rng_add_0_l in H₂; contradiction.

        apply Nat.nlt_ge in H₂.
        destruct (eq_nat_dec nb nc) as [H₃| H₃].
         rewrite Nat.min_r; [ assumption | idtac ].
         apply Nat.lt_le_incl; assumption.

         apply Nat.neq_sym in H₃.
         apply le_neq_lt in H₂; [ idtac | assumption ].
         eapply Nat.lt_trans in H₁; [ idtac | eassumption ].
         apply Hinb in H₂.
         apply Hina in H₁.
         rewrite H₂, H₁ in Hnc.
         rewrite rng_add_0_l in Hnc.
         exfalso; apply Hnc; reflexivity.

      simpl in Hab.
      apply Hab; clear Hab.
      apply Z.mul_cancel_r; [ apply Pos2Z_ne_0 | idtac ].
      apply Z.add_cancel_l.
      apply Nat2Z.inj_iff.
      destruct (eq_nat_dec na nb) as [| Hab]; [ assumption | idtac ].
      destruct (le_dec na nb) as [H₁| H₁].
       apply le_neq_lt in H₁; [ idtac | assumption ].
       apply Hinb in H₁.
       pose proof (Hnc na) as H.
       rewrite H₁, rng_add_0_r in H.
       contradiction.

       apply Nat.nle_gt in H₁.
       apply Hina in H₁.
       pose proof (Hnc nb) as H.
       rewrite H₁, rng_add_0_l in H.
       contradiction.

     rewrite <- Z.sub_max_distr_l.
     rewrite Z.sub_diag.
     rewrite <- Z2Nat_id_max.
     apply Nat2Z.is_nonneg.

    rewrite <- Z.sub_max_distr_l.
    rewrite Z.sub_diag.
    rewrite Z.max_comm, <- Z2Nat_id_max.
    apply Nat2Z.is_nonneg.

   rewrite <- Z.sub_max_distr_l.
   rewrite Z.sub_diag.
   rewrite <- Z2Nat_id_max.
   apply Nat2Z.is_nonneg.

  subst opb; simpl.
  rewrite Qbar.min_comm; simpl.
  destruct nc as [nc| ].
   destruct Hnc as (Hinc, Hnc).
   subst opa.
   apply Qbar.qfin_inj_wd.
   unfold Qeq; simpl.
   apply Z.mul_cancel_r; [ apply Pos2Z_ne_0 | idtac ].
   apply Z.add_cancel_l.
   apply Nat2Z.inj_iff.
   destruct (eq_nat_dec na nc) as [| Hac]; [ assumption | idtac ].
   destruct (le_dec na nc) as [H₁| H₁].
    apply le_neq_lt in H₁; [ idtac | assumption ].
    apply Hinc in H₁.
    rewrite Hnb, rng_add_0_r in H₁.
    contradiction.

    apply Nat.nle_gt in H₁.
    apply Hina in H₁.
    rewrite H₁, Hnb, rng_add_0_l in Hnc.
    exfalso; apply Hnc; reflexivity.

   pose proof (Hnc na) as H.
   rewrite Hnb, rng_add_0_r in H.
   contradiction.

 subst opa; simpl.
 destruct nb as [nb| ].
  destruct Hnb as (Hinb, Hnb).
  destruct nc as [nc| ].
   destruct Hnc as (Hinc, Hnc).
   destruct (eq_nat_dec nb nc) as [| Hbc]; [ subst nb | idtac ].
    subst.
    subst n₁ n₂ v₁ v₂ k₁ k₂; simpl.
    unfold cm_factor; simpl.
    rewrite Z2Nat.id.
     rewrite Z2Nat.id.
      do 2 rewrite Z.sub_sub_distr.
      do 2 rewrite Z.sub_diag, Z.add_0_l.
      rewrite Pos.mul_comm; reflexivity.

      rewrite <- Z.sub_max_distr_l.
      rewrite Z.sub_diag.
      rewrite <- Z2Nat_id_max.
      apply Nat2Z.is_nonneg.

     rewrite <- Z.sub_max_distr_l.
     rewrite Z.sub_diag.
     rewrite Z.max_comm, <- Z2Nat_id_max.
     apply Nat2Z.is_nonneg.

    destruct (le_dec nb nc) as [H₁| H₁].
     apply le_neq_lt in H₁; [ idtac | assumption ].
     apply Hinc in H₁.
     rewrite Hna, rng_add_0_l in H₁.
     contradiction.

     apply Nat.nle_gt in H₁.
     apply Hinb in H₁.
     rewrite Hna, rng_add_0_l in Hnc.
     contradiction.

   pose proof (Hnc nb) as H.
   rewrite Hna, rng_add_0_l in H.
   contradiction.

  subst opb.
  exfalso; apply Hab; reflexivity.
Qed.

(* [Walker, p 101] « O(br) = 0 » *)
Theorem xxx : ∀ pol ns c₁ r f₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq R pol ns)
    → r = root_multiplicity acf c₁ (Φq R pol ns)
      → f₁ = pol₁ R pol (β ns) (γ ns) c₁
        → (order (poly_nth R r f₁) = 0)%Qbar.
Proof.
intros pol ns c₁ r f₁ Hns Hc₁ Hr Hf₁.
subst f₁.
remember (g_lap_of_ns pol ns) as gg.
remember Heqgg as H; clear HeqH.
unfold g_lap_of_ns in H; subst gg.
rewrite <- Hc₁ in H.
remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl eqn:Hpl .
remember (List.map (term_of_point R pol) pl) as tl eqn:Htl .
remember (List.map (λ t : term α nat, power t) tl) as l₁ eqn:Hl₁ .
remember (list_seq_except 0 (length (al pol)) l₁) as l₂ eqn:Hl₂ .
remember (quotient_phi_x_sub_c_pow_r R (Φq R pol ns) c₁ r) as Ψ eqn:HΨ .
symmetry in Hc₁.
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
rewrite f₁_eq_term_with_Ψ_plus_sum with (l₂ := l₂); try eassumption.
 rewrite ps_poly_lap_summ; [ idtac | intros i; simpl; apply lap_eq_refl ].
 rewrite ps_poly_lap_summ; [ simpl | intros i; simpl; apply lap_eq_refl ].
 unfold ps_pol_add, poly_add; simpl.
 unfold ps_lap_add in H; simpl in H.
 unfold ps_lap_mul in H; simpl in H.
 progress unfold ps_lap_pow in H.
 simpl in H; rewrite <- H; clear H.
 unfold poly_nth; simpl.
 rewrite fold_ps_lap_add.
 rewrite lap_nth_add.
 assert (order (lap_nth R r (g_lap_of_ns pol ns)) > 0)%Qbar as Hog.
  destruct (lt_dec r (length (g_lap_of_ns pol ns))) as [Hlt| Hge].
   eapply each_power_of_y₁_has_coeff_pos_ord; try eassumption.
    reflexivity.

    unfold g_of_ns; simpl.
    unfold lap_nth.
    apply list_nth_in; assumption.

   apply Nat.nlt_ge in Hge.
   unfold lap_nth.
   rewrite List.nth_overflow; [ idtac | assumption ].
   rewrite order_0; constructor.

  rewrite order_neq_min.
   rewrite Qbar.min_l.
    do 2 rewrite fold_ps_lap_mul.
    do 2 rewrite fold_ps_lap_pow.
    rewrite fold_ps_lap_comp.
bbb.
    eapply ps_const_order.

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
  ns ∈ newton_segments pol
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
                     ps_pol_summ (List.seq 0 (k - r))
                       (λ h,
                        let bh := List.nth h [b₁ … lb] 0%K in
                        POL [0%ps; ps_monom bh 1 … []] ^ (r + h)) +
                     g)%pspol.
Proof.
intros pol ns j αj k αk c₁ r Ψ f₁ b₁ g Hns Hini Hfin Hc₁ Hr HΨ Hf₁ Hb₁ Hg.
bbb.

Theorem yyy : ∀ pol ns c₁ f₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq R pol ns)
    → f₁ = pol₁ R pol (β ns) (γ ns) c₁
      → ∀ i, (order (poly_nth R i f₁) ≥ 0)%Qbar.
Proof.
intros pol ns c₁ f₁ Hns Hc₁ Hf₁ i.
bbb.

End theorems.
