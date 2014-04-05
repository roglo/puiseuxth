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

Lemma split_list_comm : ∀ α (l l₁ l₂ : list α),
  split_list l l₁ l₂
  → split_list l l₂ l₁.
Proof.
intros A l l₁ l₂ H.
revert l₁ l₂ H.
induction l as [| x]; intros.
 inversion H; subst; constructor.

 inversion H; subst; constructor; apply IHl; assumption.
Qed.

Lemma split_list_length : ∀ α (l l₁ l₂ : list α),
  split_list l l₁ l₂ → length l = (length l₁ + length l₂)%nat.
Proof.
induction l as [| x]; intros; [ inversion H; reflexivity | simpl ].
inversion H; subst; simpl.
 apply eq_S, IHl; assumption.

 rewrite Nat.add_succ_r.
 apply eq_S, IHl; assumption.
Qed.

Lemma split_list_nil_l : ∀ α (l la : list α),
  split_list l [] la → la = l.
Proof.
intros A l la H.
revert la H.
induction l as [| x]; intros.
 inversion H; reflexivity.

 inversion H; subst; f_equal.
 apply IHl; assumption.
Qed.

Lemma split_sorted_cons_r : ∀ l la lb b,
  split_list l la [b … lb]
  → Sorted Nat.lt [b … l]
    → False.
Proof.
intros l la lb b Hs Hsort.
revert b lb l Hs Hsort.
induction la as [| a]; intros.
 inversion Hs; subst.
 apply Sorted_inv in Hsort.
 destruct Hsort as (_, Hrel).
 apply HdRel_inv in Hrel.
 revert Hrel; apply Nat.lt_irrefl.

 destruct l as [| c]; inversion Hs; subst.
  eapply IHla; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

  apply Sorted_inv in Hsort.
  destruct Hsort as (_, Hrel).
  apply HdRel_inv in Hrel.
  revert Hrel; apply Nat.lt_irrefl.
Qed.

Lemma split_list_sorted_cons_cons : ∀ l la lb a b,
  split_list l la [b … lb]
  → Sorted Nat.lt [a … l]
    → a ∉ lb.
Proof.
intros l la lb a b Hs Hsort Hlb.
revert la lb a b Hs Hsort Hlb.
induction l as [| c]; intros; [ inversion Hs | idtac ].
destruct (eq_nat_dec c b) as [Hcb| Hcb].
 subst c.
 inversion Hs; subst.
  eapply IHl; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

  clear Hs.
  destruct lb as [| c]; [ contradiction | idtac ].
  destruct Hlb as [Hlb| Hlb].
   subst c.
   eapply split_sorted_cons_r; [ eassumption | idtac ].
   eapply Sorted_minus_2nd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

   eapply IHl; try eassumption.
   eapply Sorted_minus_2nd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

 inversion Hs; subst.
  clear Hs.
  eapply IHl; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

  apply Hcb; reflexivity.
Qed.

Lemma split_list_sorted_cons_not_in : ∀ l la lb a,
  split_list l la lb
  → Sorted Nat.lt [a … l]
    → a ∉ lb.
Proof.
intros l la lb a Hs Hsort Hlb.
destruct lb as [| b]; intros; [ contradiction | idtac ].
destruct Hlb as [Hlb| Hlb].
 subst a.
 eapply split_sorted_cons_r; eassumption.

 eapply split_list_sorted_cons_cons; eassumption.
Qed.

Lemma xxx : ∀ l l₁ l₂ x,
  Sorted Nat.lt l
  → split_list l l₁ l₂
    → x ∈ l₁
      → x ∉ l₂.
Proof.
intros l la lb x Hsort Hs Hla Hlb.
revert l lb x Hsort Hs Hla Hlb.
induction la as [| a]; intros; [ contradiction | idtac ].
destruct Hla as [Hla| Hla].
 subst x.
 destruct l as [| x]; simpl in Hs; inversion Hs; subst.
  eapply www in Hsort; try eassumption; contradiction.
bbb.
*)

Lemma yyy : ∀ b len l₁ l₂ x,
  split_list (List.seq b len) l₁ l₂
  → x ∈ l₂
    → x ∉ l₁.
Proof.
intros s len la lb x Hs Hlb Hla.
revert s len lb x Hs Hlb Hla.
induction la as [| a]; intros; [ contradiction | idtac ].
destruct Hla as [Hla| Hla].
 subst x.
 destruct len; simpl in Hs; [ inversion Hs | idtac ].
 destruct (eq_nat_dec a s) as [Has| Has].
  subst s.
  inversion Hs; subst.
   clear Hs; rename H3 into Hs.
   revert Hlb Hs; clear; intros.
   revert a la len Hlb Hs.
   induction lb as [| b]; intros; [ contradiction | idtac ].
   destruct Hlb as [Hlb| Hlb].
    subst a.
    clear IHlb.
    revert b lb len Hs.
    induction la as [| a]; intros.
     destruct len; simpl in Hs; inversion Hs.
     revert H3; apply Nat.neq_succ_diag_l.

     destruct len; simpl in Hs; [ inversion Hs | idtac ].
     inversion Hs.
      subst.
      destruct len; simpl in H4.
       inversion H4.
bbb.
apply List.in_split in Hx.
apply List.in_split in Hy.
destruct Hx as (m1, (m2, Hm)).
destruct Hy as (n1, (n2, Hn)).
subst l₁ l₂.
revert m1 Hs.
induction n1; intros.
 simpl in Hs.
 induction m1.
  simpl in Hs.
  inversion Hs; subst.
   destruct len; [ discriminate H | idtac ].
   simpl in H.
   injection H; clear H; intros; subst x l.
   simpl in Hs.
   clear Hs.
   revert H3; clear; intros H.
   revert b m2 n2 H.
   induction len; intros.
    simpl in H.
    inversion H.

    simpl in H.
    inversion H.
     subst x n2 l₂ l.
bbb.

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

  intros Hlm.
bbb.
  assert ((Qnat l, m) ∈ pl) as Hplm.
   rewrite Hpl.
   destruct Hlm as [Hlm| Hlm].
    left; assumption.

    destruct Hlm as [Hlm| Hlm].
     right.
     apply List.in_or_app.
     right; left; assumption.

     right.
     apply List.in_or_app.
     left; assumption.

   clear Hlm.
   apply ini_oth_fin_pts_sorted in Hns.
   rewrite <- Hpl in Hns.
   subst tl.
   rewrite List.map_map in Hl₁.
   simpl in Hl₁.
bbb.
   revert Hsl Hl Hl₁ Hplm Hns; clear; intros.
   revert l₁ l₂ Hsl Hl Hl₁.
   induction pl as [| p]; intros; [ contradiction | simpl ].
   destruct Hplm as [Hplm| Hplm].
    subst p.
    simpl in Hl₁.
    subst l₁.
    rewrite nofq_Qnat in Hsl.
    apply List.in_split in Hl.
    destruct Hl as (l1, (l2, Hl)).
    subst l₂.
    revert Hsl Hns; clear; intros.
    induction l1 as [| x].
     simpl in Hsl.
     inversion Hsl; subst.
bbb.

End theorems.
