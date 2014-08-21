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

Set Implicit Arguments.

Axiom exists_or_not_forall : ∀ P : nat → Prop, (∃ n, P n) ∨ (∀ n, ¬P n).

Fixpoint nth_r α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n pol ns :=
  match n with
  | 0%nat => root_multiplicity acf (ac_root (Φq pol ns)) (Φq pol ns)
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_r n₁ pol₁ ns₁
  end.

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

Lemma lowest_i_such_that_ri_lt_r₀ : ∀ pol ns r n,
  r = nth_r 0 pol ns
  → (nth_r n pol ns < r)%nat
  → ∃ i,
    i ≤ n ∧
    (i = O ∨ r ≤ nth_r (pred i) pol ns) ∧
    (nth_r i pol ns < r)%nat.
Proof.
intros pol ns r n Hr Hrnr.
subst r.
revert pol ns Hrnr.
induction n; intros.
 exfalso; revert Hrnr; apply Nat.lt_irrefl.

 destruct (lt_dec (nth_r n pol ns) (nth_r 0 pol ns)) as [H| H].
  apply IHn in H.
  destruct H as (i, (Hin, (Hir, Hri))).
  exists i.
  split; [ fast_omega Hin | idtac ].
  split; assumption.

  apply Nat.nlt_ge in H.
  exists (S n).
  split; [ reflexivity | idtac ].
  split; [ idtac | assumption ].
  right; rewrite Nat.pred_succ; assumption.
Qed.

Lemma nth_r_n : ∀ pol ns pol₁ ns₁ c₁ n,
  pol₁ = nth_pol n pol ns
  → ns₁ = nth_ns n pol ns
  → c₁ = nth_c n pol ns
  → nth_r n pol ns = root_multiplicity acf c₁ (Φq pol₁ ns₁).
Proof.
intros pol ns pol₁ ns₁ c₁ n Hpol₁ Hns₁ Hc₁.
revert pol ns pol₁ ns₁ c₁ Hpol₁ Hns₁ Hc₁.
induction n; intros; [ subst; reflexivity | simpl ].
apply IHn; subst; reflexivity.
Qed.

(* more general than r_1_j_0_k_1 which could be simplified if this
   lemma works *)
Lemma r_n_j_0_k_1r : ∀ pol ns c₁ pol₁ ns₁ j₁ αj₁ k₁ αk₁ m r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = r
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ini_pt ns₁ = (Qnat j₁, αj₁)
  → fin_pt ns₁ = (Qnat k₁, αk₁)
  → j₁ = 0%nat ∧ (0 < k₁)%nat ∧ k₁ ≤ r ∧ αj₁ > 0 ∧ αk₁ == 0 ∧ oth_pts ns₁ = [].
Proof.
intros pol ns c₁ pol₁ ns₁ j₁ αj₁ k₁ αk₁ m r.
intros Hns Hm Hc₁ Hr Hpol₁ Hps₀ Hns₁ Hini₁ Hfin₁.
apply order_fin in Hps₀.
remember Hns as H; clear HeqH.
symmetry in Hr.
eapply f₁_orders in H; try eassumption.
destruct H as (Hnneg, (Hpos, Hz)).
assert (0 < r)%nat as H.
 destruct r.
  symmetry in Hr.
  apply root_multiplicity_0 in Hr.
   unfold degree in Hr.
   simpl in Hr.
   rewrite Nat.sub_diag in Hr.
   rewrite skipn_pad in Hr.
   simpl in Hr.
   remember Hns as H; clear HeqH.
   apply exists_ini_pt_nat in H.
   destruct H as (j, (aj, Hini)).
   remember Hns as H; clear HeqH.
   apply exists_fin_pt_nat in H.
   destruct H as (k, (ak, Hfin)).
   rewrite Hini, Hfin in Hr; simpl in Hr.
   rewrite nat_num_Qnat in Hr; simpl in Hr.
   remember
    (degree_plus_1_of_list ac_zerop
       (make_char_pol R (S j)
          (List.map (term_of_point pol) (oth_pts ns ++ [(Qnat k, ak)])))) as x.
   symmetry in Heqx.
   destruct x; [ idtac | discriminate Hr ].
   clear Hr.
   remember (oth_pts ns) as opts eqn:Hopts .
   symmetry in Hopts.
   destruct opts.
    simpl in Heqx.
    remember (nat_num (Qnat k) - S j)%nat as v; clear Heqv.
    induction v.
     simpl in Heqx.
     rewrite nat_num_Qnat in Heqx.
     destruct (ac_zerop (order_coeff (List.nth k (al pol) 0%ps))).
      exfalso.
      revert r.
      eapply ord_coeff_non_zero_in_newt_segm.
       3: eauto .

       eauto .

       rewrite Hopts; simpl.
       right; left; eauto .

      discriminate Heqx.

     simpl in Heqx.
     remember
      (degree_plus_1_of_list ac_zerop
         (list_pad v 0%K
            [order_coeff (List.nth (nat_num (Qnat k)) (al pol) 0%ps)])) as y.
     destruct y.
      apply IHv; reflexivity.

      discriminate Heqx.

    simpl in Heqx.
    remember (nat_num (fst p) - S j)%nat as v; clear Heqv.
    induction v.
     simpl in Heqx.
     remember
      (degree_plus_1_of_list ac_zerop
         (make_char_pol R (S (nat_num (fst p)))
            (List.map (term_of_point pol) (opts ++ [(Qnat k, ak)])))) as y.
     destruct y; [ idtac | discriminate Heqx ].
     destruct
      (ac_zerop (order_coeff (List.nth (nat_num (fst p)) (al pol) 0%ps))).
      exfalso.
      revert r.
      eapply ord_coeff_non_zero_in_newt_segm.
       3: eauto .

       eauto .

       rewrite Hopts.
       simpl.
       right; left.
bbb.

intros pol ns c₁ pol₁ ns₁ j₁ αj₁ k₁ αk₁ m r.
intros Hns Hm Hc₁ Hr Hpol₁ Hps₀ Hns₁ Hini₁ Hfin₁.
apply order_fin in Hps₀.
remember Hns as H; clear HeqH.
symmetry in Hr.
eapply f₁_orders in H; try eassumption.
destruct H as (Hnneg, (Hpos, Hz)).
assert (0 < 1)%nat as H by apply Nat.lt_0_1.
apply Hpos in H; clear Hpos; rename H into Hpos.
unfold newton_segments in Hns₁; simpl in Hns₁.
unfold points_of_ps_polynom in Hns₁; simpl in Hns₁.
unfold ps_poly_nth in Hnneg, Hz, Hpos.
remember (al pol₁) as la.
destruct la as [| a₀].
 unfold ps_lap_nth in Hz; simpl in Hz.
 rewrite order_0 in Hz; inversion Hz.

 unfold ps_lap_nth in Hnneg, Hz, Hpos.
 simpl in Hz, Hpos.
 unfold points_of_ps_lap in Hns₁.
 unfold points_of_ps_lap_gen in Hns₁.
 simpl in Hns₁.
 remember (order a₀) as v₀.
 symmetry in Heqv₀.
 destruct v₀ as [v₀| ].
  destruct la as [| a₁]; [ rewrite order_0 in Hz; contradiction | idtac ].
  simpl in Hz, Hns₁.
  remember (order a₁) as v₁.
  symmetry in Heqv₁.
  destruct v₁ as [v₁| ]; [ idtac | contradiction ].
  apply Qbar.qfin_inj in Hz.
  apply Qbar.qfin_lt_mono in Hpos.
  remember (pair_rec (λ pow ps, (Qnat pow, ps))) as f.
  simpl in Hns₁.
  remember (filter_finite_ord R (List.map f (power_list 2 la))) as ffo.
  remember (minimise_slope (Qnat 0, v₀) (Qnat 1, v₁) ffo) as ms.
  subst ns₁; simpl in Hini₁, Hfin₁.
  rewrite Heqms, minimised_slope_beg_pt in Hini₁.
  eapply pouet in Hfin₁; try eassumption.
  destruct Hfin₁ as (H₁, (H₂, (H₃, (H₄, (H₅, H₆))))).
  split; [ assumption | idtac ].
  split; [ omega | idtac ].
  split; [ assumption | idtac ].
  split; assumption.

  unfold ps_poly_nth in Hps₀.
  rewrite <- Heqla in Hps₀.
  unfold ps_lap_nth in Hps₀; simpl in Hps₀.
  contradiction.
Qed.

(* more general than r_1_next_ns which could be simplified if this
   lemma works *)
Lemma r_n_next_ns : ∀ pol ns c pol₁ ns₁ m r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → root_multiplicity acf c (Φq pol ns) = r
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ∃ αj αk k,
    (0 < k)%nat ∧ (k ≤ r)%nat ∧
    oth_pts ns₁ = [] ∧
    ini_pt ns₁ = (Qnat 0, αj) ∧
    fin_pt ns₁ = (Qnat 1, αk) ∧
    (0 < Qnum αj)%Z ∧
    Qnum αk = 0%Z.
Proof.
r_n_next_ns < Show Script.
intros pol ns c pol₁ ns₁ m r Hns Hm Hr Hc Hpol₁ Hns₁ Hpnz.
remember Hns₁ as H; clear HeqH.
apply exists_ini_pt_nat_fst_seg in H.
destruct H as (j₁, (αj₁, Hini₁)).
remember Hns₁ as H; clear HeqH.
apply exists_fin_pt_nat_fst_seg in H.
destruct H as (k₁, (αk₁, Hfin₁)).
remember Hns₁ as H; clear HeqH.
bbb.
eapply r_1_j_0_k_1 in H; eauto .
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁.
unfold Qlt in Hαj₁; simpl in Hαj₁.
unfold Qeq in Hαk₁; simpl in Hαk₁.
rewrite Z.mul_1_r in Hαj₁, Hαk₁.
exists αj₁, αk₁; auto.
Qed.

(* more general than r_1_nth_ns which could be simplified if this
   lemma works *)
Lemma r_n_nth_ns : ∀ pol ns c pol₁ ns₁ m r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ∀ n poln nsn,
    (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
    → poln = nth_pol n pol₁ ns₁
    → nsn = nth_ns n pol₁ ns₁
    → ∃ αj αk k,
      (0 < k)%nat ∧ (k ≤ r)%nat ∧
      oth_pts nsn = [] ∧
      ini_pt nsn = (Qnat 0, αj) ∧
      fin_pt nsn = (Qnat k, αk) ∧
      (0 < Qnum αj)%Z ∧
      Qnum αk = 0%Z.
Proof.
intros pol ns c pol₁ ns₁ m r Hns Hm Hc Hr Hpol₁ Hns₁.
intros n poln nsn Hpsi Hpoln Hnsn.
remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀ .
revert poln nsn Hpsi Hpoln Hnsn.
revert pol ns c pol₁ ns₁ m q₀ r Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁.
induction n; intros.
 pose proof (Hpsi O (Nat.le_0_l O)) as H; simpl in H.
 rename H into Hnz₁.
 simpl in Hpoln, Hnsn; subst poln nsn.
 remember Hns as H; clear HeqH.
bbb.
 eapply r_1_next_ns in H; eauto .
bbb.

Theorem zzz : ∀ pol ns c pol₁,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ∃ s, (ps_pol_apply pol₁ s = 0)%ps.
Proof.
intros pol ns c pol₁ Hns Hc Hpol₁.
remember (root_multiplicity acf c (Φq pol ns)) as r eqn:Hr .
symmetry in Hr.
revert pol ns c pol₁ Hns Hc Hpol₁ Hr.
induction r using all_lt_all; intros.
destruct r.
 exfalso; revert Hr.
 apply multiplicity_neq_0; assumption.

 rename H into IHm.
 pose proof (exists_or_not_forall (multiplicity_decreases pol ns)) as H.
 destruct H as [Hn| Hn].
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
   erewrite <- nth_r_n in Hrn; eauto ; subst rn.
   apply lowest_i_such_that_ri_lt_r₀ in Hn.
    2: subst; auto.

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
      remember (nth_pol (S i) pol ns) as polsi eqn:Hpolsi.
      remember (nth_ns (S i) pol ns) as nssi eqn:Hnssi.
      eapply IHm in Hri.
       Focus 5.
       symmetry.
       apply nth_r_n; eauto .

       Focus 3.
       erewrite nth_c_root; eauto .

       3: eauto .

       Focus 2.
       eapply List_hd_in.
        subst nssi.
        simpl.
        eapply nth_ns_n; eauto .
         rewrite Hc; reflexivity.

         subst polsi; simpl.
         symmetry.
         eapply nth_pol_n; eauto .
         rewrite Hc; reflexivity.

        simpl in Hir.
        erewrite nth_ns_succ in Hnssi; eauto .
        remember Hnssi as H; clear HeqH.
        apply exists_ini_pt_nat_fst_seg in H.
        destruct H as (jsi, (ajsi, Hinisi)).
        remember Hnssi as H; clear HeqH.
        apply exists_fin_pt_nat_fst_seg in H.
        destruct H as (ksi, (aksi, Hifinsi)).
bbb.

   remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
   remember (next_pol poln (β nsn) (γ nsn) cn) as poln₁ eqn:Hpoln₁ .
   remember (zerop_1st_n_const_coeff n pol₁ ns₁) as z eqn:Hz .
   symmetry in Hz.
   destruct z.
    Focus 2.
    eapply IHm with (ns := nsn) (c := cn) (pol₁ := poln₁) in Hn; eauto .
     erewrite nth_pol_n in Hpoln₁; eauto .
      destruct Hn as (sn₁, Hsn₁).
      remember (root_head 0 n pol₁ ns₁) as rh₁.
      remember (ps_monom 1%K (γ_sum 0 n pol₁ ns₁)) as mo₁.
      exists (rh₁ + mo₁ * sn₁)%ps; subst rh₁ mo₁.
      rewrite apply_nth_pol; auto.
      rewrite <- Hpoln₁, Hsn₁.
      rewrite rng_mul_0_r; reflexivity.

      rewrite Hcn.
      apply nth_c_root; assumption.

     eapply List_hd_in.
      rewrite Hnsn; simpl.
      eapply nth_ns_n; try reflexivity.
      erewrite nth_pol_n; try reflexivity.
      assumption.

      pose proof (exists_pol_ord R pol) as H.
      destruct H as (m, Hm).
      remember Hns as H; clear HeqH.
bbb.
waiting for a version of r_1_nth_ns with any r: r_n_nth_ns...

End theorems.
