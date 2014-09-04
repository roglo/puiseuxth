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

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Theorem multiplicity_is_pos : ∀ pol ns c r,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → (0 < r)%nat.
Proof.
intros pol ns c r Hns Hc Hr.
remember Hns as H; clear HeqH.
eapply multiplicity_neq_0 in H; auto.
apply Nat.neq_sym, neq_0_lt in H.
rewrite <- Hc, Hr in H.
assumption.
Qed.

Theorem not_zero_1st_prop : ∀ pol ns b,
  zerop_1st_n_const_coeff b (nth_pol 1 pol ns) (nth_ns 1 pol ns) = false
  → (ps_poly_nth 0 pol ≠ 0)%ps
  → (∀ i, i ≤ S b → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps).
Proof.
intros pol ns b Hpsi Hnz.
apply zerop_1st_n_const_coeff_false_iff.
rewrite zerop_1st_n_const_coeff_succ.
rewrite Hpsi, Bool.orb_false_r; simpl.
destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
contradiction.
Qed.

Theorem newton_segments_not_nil : ∀ pol ns αk r,
  ns = List.hd phony_ns (newton_segments pol)
  → fin_pt ns = (Qnat r, αk)
  → (0 < r)%nat
  → newton_segments pol ≠ [].
Proof.
intros pol ns αk r Hns Hfin Hr.
intros H; rewrite H in Hns; subst ns.
simpl in Hfin.
injection Hfin; intros H₁ H₂.
rewrite <- Nat2Z.inj_0 in H₂.
apply Nat2Z.inj in H₂.
rewrite H₂ in Hr.
revert Hr; apply Nat.lt_irrefl.
Qed.

Theorem all_same_r_next : ∀ pol ns c pol₁ ns₁ r,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i : nat, nth_r i pol ns = r)
  → (∀ i : nat, nth_r i pol₁ ns₁ = r).
Proof.
intros pol ns c pol₁ ns₁ r Hc Hpol₁ Hns₁ Hri i.
pose proof (Hri (S i)) as H; simpl in H.
rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
assumption.
Qed.

Theorem nth_pol_in_K_1_m : ∀ pol ns c αj αk poln m n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → ini_pt ns = (Qnat 0, αj)
  → fin_pt ns = (Qnat r, αk)
  → (0 < Qnum αj)%Z
  → Qnum αk = 0%Z
  → (∀ i : nat, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (∀ i : nat, i ≤ n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
  → poln = nth_pol n pol ns
  → pol_in_K_1_m poln m.
Proof.
intros pol ns c αj αk poln m n r.
intros Hns HK Hc Hini Hfin Hαj Hαk Hri H₀ Hpsi Hpoln.
eapply first_n_pol_in_K_1_m_any_r with (ns := ns) (n := n); eauto .
eapply q_eq_1_any_r with (ns := ns); eauto .
pose proof (Hri 0%nat) as H; simpl in H.
rewrite <- Hc in H; rewrite H.
assumption.
Qed.

Theorem find_coeff_step_any_r : ∀ pol ns m c pol₁ ns₁ i di p dp np r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (0 < p ≤ i)%nat
  → (di ≤ dp + 1)%nat
  → np = next_pow (p + dp) ns₁ m
  → (find_coeff i np m pol₁ ns₁ (S i - p + di) =
     find_coeff (S i - p) np m pol₁ ns₁ (S i - p + di))%K.
Proof.
(* to be cleaned up *)
intros pol ns m c pol₁ ns₁ i di p dp np r.
intros Hns HK Hq Hc Hpol₁ Hns₁ Hri H₀ (Hp, Hpi) Hdip Hnp.
remember (S i - p)%nat as id.
revert id Heqid.
revert p dp np Hp Hpi Hdip Hnp.
revert pol ns c pol₁ ns₁ di r Hns HK Hq Hc Hpol₁ Hns₁ Hri.
induction i; intros.
 destruct p; [ exfalso; revert Hp; apply Nat.lt_irrefl | idtac ].
 exfalso; revert Hpi; apply Nat.nle_succ_0.

 pose proof (Hri 0%nat) as Hr₀; simpl in Hr₀.
 rewrite <- Hc in Hr₀.
 pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hr₁.
 destruct id; [ exfalso; fast_omega Hpi Heqid | simpl ].
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁]; auto.
 unfold next_pow in Hnp; simpl in Hnp.
 remember Hns as H; clear HeqH.
 eapply r_n_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 rewrite Hini₁, Hfin₁ in Hnp; simpl in Hnp.
 rewrite Hαk₁ in Hnp; simpl in Hnp.
 assert (0 < r)%nat as Hrpos.
  destruct r; [ idtac | apply Nat.lt_0_succ ].
  exfalso; revert Hr₀; apply multiplicity_neq_0; auto.

  rewrite Qnum_inv_Qnat_sub in Hnp; auto.
  rewrite Qden_inv_Qnat_sub in Hnp; auto.
  simpl in Hnp.
  rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r, Pos.mul_1_r in Hnp.
  rewrite Z.mul_shuffle0, Pos_mul_shuffle0 in Hnp.
  do 2 rewrite Pos2Z.inj_mul in Hnp.
  rewrite Z.div_mul_cancel_r in Hnp; auto.
   remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
   eapply List_hd_in in Hns₁₁; eauto .
    remember (Nat.compare np (S (id + di))) as cmp₁ eqn:Hnpi .
    symmetry in Hnpi.
    destruct cmp₁; auto.
    remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
    remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
    remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
    remember (next_pow np ns₂ m) as nnp eqn:Hnnp .
    apply nat_compare_lt in Hnpi.
    assert (Z.of_nat r ≠ 0%Z) as Hrpos₂ by fast_omega Hrpos.
    assert (pol_in_K_1_m pol₁ m) as HK₁.
     replace m with (m * 1)%positive by apply Pos.mul_1_r.
     eapply next_pol_in_K_1_mq with (pol := pol); eauto .

     remember Hns₁₁ as H; clear HeqH.
     eapply num_m_den_is_pos with (m := m) in H; eauto .
     rename H into H₂.
     remember (p_of_m m (γ ns₁)) as p₁ eqn:Hp₁ .
     rewrite <- Nat.add_succ_r.
     assert (q_of_m m (γ ns₁) = 1%positive) as Hq₁.
      replace m with (m * 1)%positive by apply Pos.mul_1_r.
      eapply q_eq_1_any_r; eauto ; [ rewrite Pos.mul_1_r; auto | idtac ].
      rewrite Hr₁; auto.

      rewrite Nat.sub_succ_l in Heqid; auto.
      apply eq_add_S in Heqid.
      subst np; rewrite <- Nat.add_assoc in Hnnp.
      assert (0 < Z.to_nat p₁)%nat as Hp₁pos.
       erewrite αj_m_eq_p_r in Hnpi; eauto .
       rewrite Z.mul_shuffle0 in Hnpi.
       rewrite Zposnat2Znat in Hnpi; auto.
       rewrite Z.div_mul_cancel_r in Hnpi; auto.
       rewrite Z.div_mul in Hnpi; auto.
       erewrite αj_m_eq_p_r in H₂; eauto .
       rewrite Z.div_mul in H₂; auto.
       rewrite Z2Nat.inj_mul in H₂.
        rewrite Nat2Z.id in H₂.
        eapply Nat.mul_pos_cancel_r with (m := r); auto.

        rewrite Hp₁.
        unfold p_of_m; simpl.
        rewrite Hini₁, Hfin₁; simpl.
        rewrite Hαk₁; simpl.
        rewrite Qnum_inv_Qnat_sub; auto.
        rewrite Qden_inv_Qnat_sub; auto.
        rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
        apply Z.div_pos.
         apply Z.mul_nonneg_nonneg; auto.
         apply Z.mul_nonneg_nonneg; auto.
         apply Z.lt_le_incl; auto.

         pose proof
          (Z.gcd_nonneg (Qnum αj₁ * ' Qden αk₁ * ' m)
             (' (Qden αj₁ * Qden αk₁ * Pos.of_nat r))).
         assert
          (Z.gcd (Qnum αj₁ * ' Qden αk₁ * ' m)
             (' (Qden αj₁ * Qden αk₁ * Pos.of_nat r)) ≠ 0)%Z.
          2: omega.

          intros HH.
          apply Z.gcd_eq_0_r in HH.
          revert HH; apply Pos2Z_ne_0.

        destruct r.
         exfalso; revert Hr₁.
         apply multiplicity_neq_0; auto.

         apply Nat2Z.is_nonneg.

       eapply IHi with (p := p); eauto .
        intros j.
        pose proof (Hri (S j)) as H; simpl in H.
        rewrite <- Hc, <- Hpol₁, <- Hns₁ in H; eauto .

        erewrite αj_m_eq_p_r in Hnpi; eauto .
        rewrite Z.mul_shuffle0 in Hnpi.
        rewrite Zposnat2Znat in Hnpi; auto.
        rewrite Z.div_mul_cancel_r in Hnpi; auto.
        rewrite Z.div_mul in Hnpi; auto.
        omega.

        erewrite αj_m_eq_p_r; eauto .
        rewrite Z.mul_shuffle0.
        rewrite Zposnat2Znat; auto.
        rewrite Z.div_mul_cancel_r; auto.
        rewrite Z.div_mul; auto.
        omega.

    intros H.
    rewrite H in Hns₁.
    rewrite Hns₁ in Hfin₁; simpl in Hfin₁.
    injection Hfin₁; intros.
    rewrite <- Nat2Z.inj_0 in H1.
    apply Nat2Z.inj in H1.
    rewrite <- H1 in Hr₀.
    revert Hr₀.
    apply multiplicity_neq_0; auto.

   apply Pos2Z_ne_0.
Qed.

Theorem next_pow_eq_p : ∀ pol ns c αj αk m r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → ini_pt ns = (Qnat 0, αj)
  → fin_pt ns = (Qnat r, αk)
  → (0 < Qnum αj)%Z
  → Qnum αk = 0%Z
  → (0 < r)%nat
  → (1 ≠ 0)%K
  → next_pow 0 ns m = Z.to_nat (p_of_m m (γ ns)).
Proof.
intros pol ns c αj αk m r Hns Hm Hc Hr Hini Hfin Hαj Hαk Hrp H₀.
unfold next_pow; simpl.
rewrite Hini, Hfin; simpl.
rewrite Hαk; simpl.
rewrite Qnum_inv_Qnat_sub; auto.
rewrite Qden_inv_Qnat_sub; auto.
rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r, Pos.mul_1_r.
rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
rewrite Pos2Z.inj_mul.
rewrite Z.div_mul_cancel_r; auto.
erewrite αj_m_eq_p_r with (pol₁ := pol); eauto .
rewrite Pos.mul_comm.
rewrite Pos2Z.inj_mul, Zposnat2Znat; auto.
rewrite <- Z.mul_assoc.
rewrite Z.div_mul; auto.
rewrite <- Zposnat2Znat; auto.
apply Pos2Z_ne_0.
Qed.

Theorem find_coeff_enough_iter : ∀ pol ns pow m i n₁ n₂,
  (i < n₁)%nat
  → (n₁ ≤ pow)
  → (i < n₂)%nat
  → (n₂ ≤ pow)
  → (find_coeff n₁ pow m pol ns i =
     find_coeff n₂ pow m pol ns i)%K.
Proof.
intros pol ns pow m i n₁ n₂ Hn₁ Hn₁p Hn₂ Hn₂p.
revert pol ns pow m i n₂ Hn₁ Hn₂ Hn₁p Hn₂p.
induction n₁; intros.
 exfalso; revert Hn₁; apply Nat.nlt_0_r.

 destruct n₂.
  exfalso; revert Hn₂; apply Nat.nlt_0_r.

  simpl.
  destruct (ps_zerop R (ps_poly_nth 0 pol)) as [| H₁]; auto.
  remember (Nat.compare pow i) as cmp eqn:Hcmp .
  symmetry in Hcmp.
  destruct cmp; auto.
  remember (ac_root (Φq pol ns)) as c eqn:Hc .
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  destruct (eq_nat_dec i n₁) as [H₂| H₂].
   subst i.
   destruct (eq_nat_dec n₂ n₁) as [H₃| H₃].
    subst n₂; reflexivity.

    apply nat_compare_lt in Hcmp.
    exfalso; fast_omega Hn₁p Hcmp.

   destruct (eq_nat_dec i n₂) as [H₃| H₃].
    subst i.
    apply nat_compare_lt in Hcmp.
    exfalso; fast_omega Hn₂p Hcmp.

    apply IHn₁; try omega.
     apply le_trans with (m := pow); [ omega | idtac ].
     replace pow with (0 + pow)%nat by reflexivity.
     rewrite next_pow_add; simpl.
     apply Nat.le_sub_le_add_r.
     rewrite Nat.sub_diag.
     apply Nat.le_0_l.

     apply le_trans with (m := pow); [ omega | idtac ].
     replace pow with (0 + pow)%nat by reflexivity.
     rewrite next_pow_add; simpl.
     apply Nat.le_sub_le_add_r.
     rewrite Nat.sub_diag.
     apply Nat.le_0_l.
Qed.

Theorem p_is_pos : ∀ ns αj αk m r,
  ini_pt ns = (Qnat 0, αj)
  → fin_pt ns = (Qnat r, αk)
  → (0 < Qnum αj)%Z
  → Qnum αk = 0%Z
  → (0 < r)%nat
  → (0 < p_of_m m (γ ns))%Z.
Proof.
intros ns αj αk m r Hini Hfin Hαj Hαk Hr.
unfold p_of_m; simpl.
rewrite Hini, Hfin; simpl.
rewrite Hαk; simpl.
rewrite Qnum_inv_Qnat_sub; auto.
rewrite Qden_inv_Qnat_sub; auto.
rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
rewrite Z.gcd_comm.
apply Z_div_gcd_r_pos.
apply Z.mul_pos_pos; [ idtac | apply Pos2Z.is_pos ].
apply Z.mul_pos_pos; [ auto | apply Pos2Z.is_pos ].
Qed.

Theorem find_coeff_more_iter : ∀ pol ns pow m i n r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → (∀ j, nth_r j pol ns = r)
  → (∀ j, j ≤ S n → (ps_poly_nth 0 (nth_pol j pol ns) ≠ 0)%ps)
  → (1 ≠ 0)%K
  → (i < n)%nat
  → (find_coeff n pow m pol ns i =
     find_coeff (S n) pow m pol ns i)%K.
Proof.
intros pol ns pow m i n r Hns Hm Hq₀ Hri Hpsi H₀ Hin.
revert pol ns pow m n Hns Hm Hq₀ Hri Hpsi Hin.
induction i; intros.
 destruct n; [ exfalso; revert Hin; apply Nat.lt_irrefl | idtac ].
 remember (S n) as sn.
 rewrite Heqsn in |- * at 1; simpl.
 destruct (ps_zerop _ (ps_poly_nth 0 pol)) as [| H₁]; auto.
 remember (Nat.compare pow 0) as cmp₁ eqn:Hcmp₁ .
 symmetry in Hcmp₁.
 destruct cmp₁; auto.
 apply nat_compare_lt in Hcmp₁.
 exfalso; revert Hcmp₁; apply Nat.nlt_0_r.

 pose proof (Hri O) as Hr₀; simpl in Hr₀.
 assert (0 < r)%nat as Hrp.
  destruct r; [ idtac | apply Nat.lt_0_succ ].
  exfalso; revert Hr₀.
  apply multiplicity_neq_0; auto.

  destruct n; [ exfalso; revert Hin; apply Nat.nlt_0_r | idtac ].
  remember (S n) as sn.
  rewrite Heqsn in |- * at 1; simpl.
  destruct (ps_zerop _ (ps_poly_nth 0 pol)) as [| H₁]; auto.
  remember (Nat.compare pow (S i)) as cmp₁ eqn:Hcmp₁ .
  symmetry in Hcmp₁.
  destruct cmp₁; auto.
  pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
  assert (1 ≤ S sn) as H by fast_omega .
  apply Hpsi in H; simpl in H.
  rename H into Hnz₁.
  remember (ac_root (Φq pol ns)) as c eqn:Hc .
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  remember Hns as H; clear HeqH.
  eapply r_n_next_ns in H; eauto .
  destruct H as (αj₁, (αk₁, H)).
  destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
  remember Hns₁ as H; clear HeqH.
  eapply newton_segments_not_nil in H; eauto .
  rename H into Hns₁nz.
  remember Hns₁ as H; clear HeqH.
  apply List_hd_in in H; auto.
  rename H into Hns₁₁.
  remember Hpol₁ as H; clear HeqH.
  erewrite <- nth_pol_succ with (n := O) in H; simpl; eauto .
  eapply first_n_pol_in_K_1_m_any_r in H; eauto .
   rename H into HK₁.
   remember (next_pow pow ns₁ m) as pow₁ eqn:Hpow₁ .
   symmetry in Hpow₁.
   destruct pow₁.
    replace pow with (0 + pow)%nat in Hpow₁ by auto.
    rewrite next_pow_add in Hpow₁.
    apply Nat.eq_add_0 in Hpow₁.
    destruct Hpow₁ as (Hpow₁, Hpow).
    erewrite next_pow_eq_p with (pol := pol₁) in Hpow₁; eauto .
    assert (0 < p_of_m m (γ ns₁))%Z as H by (eapply p_is_pos; eauto ).
    rewrite <- Z2Nat.inj_0 in Hpow₁.
    apply Z2Nat.inj in Hpow₁; [ idtac | idtac | reflexivity ].
     rewrite Hpow₁ in H.
     exfalso; revert H; apply Z.lt_irrefl.

     apply Z.lt_le_incl; auto.

    remember (S pow₁) as x.
    rewrite <- Nat.add_1_r; subst x.
    rewrite <- Nat.add_1_r.
    do 2 rewrite find_coeff_add.
    subst sn.
    apply lt_S_n in Hin.
    apply IHi; auto.
     remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
     symmetry in Hr₁.
     eapply q_eq_1_any_r; eauto .

     intros j.
     pose proof (Hri (S j)) as H; simpl in H.
     rewrite <- Hc, <- Hpol₁, <- Hns₁ in H.
     assumption.

     intros j Hjn.
     apply le_n_S in Hjn.
     apply Hpsi in Hjn; simpl in Hjn.
     rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hjn.
     assumption.

   intros j Hj.
   apply Hpsi.
   eapply le_trans; eauto .
   apply le_n_S, Nat.le_0_l.
Qed.

Theorem xxx : ∀ pol ns pow m i n n' r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q_of_m m (γ ns) = 1%positive
  → (∀ j, nth_r j pol ns = r)
  → (∀ j, j ≤ S n → (ps_poly_nth 0 (nth_pol j pol ns) ≠ 0)%ps)
  → (1 ≠ 0)%K
  → (i < n)%nat
  → n ≤ n'
  → (find_coeff n pow m pol ns i =
     find_coeff n' pow m pol ns i)%K.
Proof.
xxx < Show Script.
intros pol ns pow m i n n' r Hns Hm Hq₀ Hri Hpsi H₀ Hin Hn'.
remember (n' - n)%nat as d eqn:Hd .
replace n' with (n + d)%nat by fast_omega Hd Hn'.
clear n' Hn' Hd.
rewrite Nat.add_comm.
revert n pow Hpsi Hin.
revert pol ns Hns Hm Hq₀ Hri.
induction d; intros; [ reflexivity | idtac ].
rewrite find_coeff_more_iter; auto; simpl.
destruct (ps_zerop R (ps_poly_nth 0 pol)) as [| H₁]; auto.
remember (Nat.compare pow i) as cmp eqn:Hcmp .
symmetry in Hcmp.
destruct cmp; auto.
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (next_pow pow ns₁ m) as pow₁.
destruct (ps_zerop _ (ps_poly_nth 0 (nth_pol (S n) pol₁ ns₁))) as [H₂| H₂].
 Focus 2.
 apply IHd; auto.
  eapply List_hd_in; eauto .
  remember Hns as H; clear HeqH.
  eapply next_has_root_0_or_newton_segments in H; eauto .
  destruct H as [H| H].
   exfalso; revert H.
   apply Hpsi, le_n_S, Nat.le_0_l.

   simpl in H.
   rewrite <- Hc, <- Hpol₁ in H; assumption.

  Focus 4.
  intros j Hj.
  destruct (eq_nat_dec j (S n)) as [| H₃]; [ subst j; auto | idtac ].
  apply le_neq_lt in Hj; auto.
  apply Hpsi in Hj; simpl in Hj.
  rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hj; assumption.
bbb.
  H₂ : (ps_poly_nth 0 (nth_pol (S n) pol₁ ns₁) = 0)%ps
  ============================
   (find_coeff n pow₁ m pol₁ ns₁ i = find_coeff (d + n) pow₁ m pol₁ ns₁ i)%K

subgoal 2 is:
 pol_in_K_1_m pol₁ m
subgoal 3 is:
 q_of_m m (γ ns₁) = 1%positive
subgoal 4 is:
 ∀ j : nat, nth_r j pol₁ ns₁ = r

(* cf root_tail_from_0 *)
Theorem root_tail_from_0₄₂ : ∀ pol ns pol₁ ns₁ c m q₀ b r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, nth_r i pol ns = r)
  → (1 ≠ 0)%K
  → (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum b 0 pol₁ ns₁) *
       root_tail (m * q₀) (b + 1) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b r Hns Hm Hq₀ Hc Hpol₁ Hns₁ Hri H₀.
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
 eapply next_pol_in_K_1_mq in HK₁; eauto .
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
 pose proof (Hri 0%nat) as Hr₀; simpl in Hr₀.
 pose proof (Hri 1%nat) as Hr₁; simpl in Hr₁.
 rewrite <- Hc in Hr₀.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hr₁.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 assert (0 < r)%nat as Hrpos by (eapply multiplicity_is_pos; eauto ).
 remember Hns₁ as H; clear HeqH.
 eapply r_n_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 assert (∀ i : nat, i ≤ b₁ → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps).
  rewrite Hb₁; apply not_zero_1st_prop; auto.

  clear Hpsi; rename H into Hpsi.
  remember Hns₁ as H; clear HeqH.
  eapply newton_segments_not_nil in H; eauto .
  rename H into Hns₁nz.
  remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
  eapply List_hd_in in Hns₁₁; eauto .
  assert (∀ i, nth_r i pol₁ ns₁ = r) as Hri₁.
   eapply all_same_r_next with (ns := ns); eauto .

   remember Hns₁₁ as H; clear HeqH.
   eapply nth_in_newton_segments_any_r with (n := b₁) in H; eauto .
   rename H into Hbns.
   remember (nth_pol b₁ pol₁ ns₁) as polb₂ eqn:Hpolb₂ .
   remember (nth_ns b₁ pol₁ ns₁) as nsb₂ eqn:Hnsb₂ .
   assert (pol_in_K_1_m polb₂ m₁) as HKb₂.
    eapply nth_pol_in_K_1_m with (ns := ns₁) (n := b₁); eauto .

    pose proof (Hri (S b₁)) as Hrb; simpl in Hrb.
    rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hrb.
    erewrite nth_r_n in Hrb; eauto .
    erewrite nth_c_root in Hrb; eauto .
    remember Hbns as H; clear HeqH.
    apply exists_ini_pt_nat in H.
    destruct H as (jb, (αjb₂, Hinib₂)).
    remember Hbns as H; clear HeqH.
    apply exists_fin_pt_nat in H.
    destruct H as (kb, (αkb₂, Hfinb₂)).
    remember (ac_root (Φq polb₂ nsb₂)) as cb₂ eqn:Hcb₂ .
    remember (nth_pol (b₁ + 1) pol₁ ns₁) as polb₃ eqn:Hpolb₃ .
    subst b₁.
    simpl in Hpolb₂, Hnsb₂, Hpolb₃.
    rewrite <- Hc₁, <- Hpol₂ in Hpolb₂, Hnsb₂, Hpolb₃.
    rewrite <- Hns₂ in Hpolb₂, Hnsb₂, Hpolb₃.
    rewrite <- Nat.add_1_r, <- Hpolb₃.
    remember Hns₁₁ as H; clear HeqH.
    eapply nth_in_newton_segments_any_r with (n := b) in H; eauto .
    remember (nth_ns b pol₁ ns₁) as nsb₁ eqn:Hnsb₁ .
    remember (nth_pol b pol₁ ns₁) as polb₁ eqn:Hpolb₁ .
    remember (ac_root (Φq polb₁ nsb₁)) as cb₁ eqn:Hcb₁ .
    pose proof (Hri (S b)) as Hrb₁; simpl in Hrb₁.
    rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hrb₁.
    erewrite nth_r_n in Hrb₁; eauto .
    erewrite nth_c_root in Hrb₁; eauto .
    rewrite <- Hcb₁ in Hrb₁.
    pose proof (Hpsi (S b) (Nat.le_refl (S b))) as Hpsb₂.
    simpl in Hpsb₂.
    rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hpsb₂.
    erewrite <- nth_pol_n with (c₁ := c₁) in Hpsb₂; eauto .
    erewrite nth_ns_n with (c := c₁) in Hnsb₂; eauto .
    assert (pol_in_K_1_m polb₁ m₁) as HKb₁.
     eapply nth_pol_in_K_1_m with (ns := ns₁) (n := b); eauto .

     erewrite nth_pol_n with (c₁ := c₁) in Hnsb₂; eauto .
     rewrite <- Hpolb₂ in Hnsb₂.
     erewrite <- nth_pol_n with (c₁ := c₁) in Hpolb₂; eauto .
     rewrite <- Hpolb₂ in Hpsb₂.
     eapply r_n_j_0_k_n with (ns₁ := nsb₂) (m := m₁) in H; eauto .
     erewrite <- nth_ns_n with (c := c₁) in Hnsb₂; eauto .
     destruct H as (Hjb, (Hkb, (Hαjb₂, Hαkb₂))).
     erewrite nth_pol_n with (c₁ := c₁) in Hpolb₂; eauto .
     subst jb kb.
     unfold Qlt in Hαjb₂; simpl in Hαjb₂.
     unfold Qeq in Hαkb₂; simpl in Hαkb₂.
     rewrite Z.mul_1_r in Hαjb₂, Hαkb₂.
     remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
     remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
     remember (List.hd phony_ns (newton_segments pol₃)) as ns₃ eqn:Hns₃ .
     pose proof (Hri 2%nat) as Hr₂.
     remember 1%nat as one; simpl in Hr₂.
     rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hr₂.
     subst one; simpl in Hr₂.
     rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hr₂.
     rewrite <- Hc₂ in Hr₂.
     destruct (ps_zerop R (ps_poly_nth 0 polb₃)) as [H₁| H₁].
      rewrite rng_mul_0_r, rng_add_0_r, Nat.add_1_r.
      unfold root_tail_from_cγ_list, ps_monom; simpl.
      rewrite Hinib₂, Hfinb₂; simpl.
      rewrite Hαkb₂; simpl.
      rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
      rewrite Qnum_inv_Qnat_sub; auto.
      rewrite Qden_inv_Qnat_sub; auto.
      rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
      rewrite <- Pos2Z.inj_mul.
      rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
      do 2 rewrite Pos2Z.inj_mul.
      rewrite Z.div_mul_cancel_r; simpl; auto.
      erewrite αj_m_eq_p_r; eauto .
      rewrite Pos2Z.inj_mul, Z.mul_shuffle0, Zposnat2Znat; auto.
      rewrite <- Z.mul_assoc.
      rewrite <- Zposnat2Znat; simpl; eauto .
      rewrite Z.div_mul; eauto .
      rewrite ps_adjust_eq with (n := O) (k := Qden (nth_γ b pol₂ ns₂)).
      symmetry.
      rewrite ps_adjust_eq with (n := O) (k := m₁).
      symmetry.
      unfold adjust_ps; simpl.
      rewrite Pos.mul_comm.
      do 2 rewrite Z.sub_0_r.
      rewrite fold_series_const.
      do 2 rewrite series_shift_0.
      rewrite series_stretch_const.
      apply mkps_morphism; auto.
       unfold series_stretch.
       constructor; intros i; simpl.
       remember (nth_γ b pol₂ ns₂) as γb eqn:Hγb .
       subst polb₃.
       rename H₁ into Hpolb₃.
       destruct (zerop (i mod Pos.to_nat (Qden γb))) as [H₁| H₁].
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
         destruct (ps_zerop R (ps_poly_nth 0 polb₂));
          [ contradiction | idtac ].
         symmetry.
         erewrite nth_c_root; eauto .

         simpl.
         rewrite <- Hcb₂.
         rewrite Nat.add_comm in Hpolb₃; simpl in Hpolb₃.
         rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in Hpolb₃.
         destruct d.
          rewrite Hd in H₁.
          exfalso; revert H₁; apply Nat.lt_irrefl.

          destruct (ps_zerop R (ps_poly_nth 0 polb₂)); auto.
          erewrite nth_pol_n with (c₁ := c₂); eauto .
          remember (nth_pol b pol₃ ns₃) as pol₄ eqn:Hpol₄ .
          remember (List.hd phony_ns (newton_segments pol₄)) as ns₄ eqn:Hns₄ .
          simpl.
          destruct (ps_zerop R (ps_poly_nth 0 pol₄)) as [H₃| H₃]; auto.
          contradiction.

        destruct (zerop i); [ subst i | reflexivity ].
        rewrite Nat.mod_0_l in H₁; auto.
        exfalso; revert H₁; apply Nat.lt_irrefl.

       erewrite nth_γ_n; eauto ; simpl.
       rewrite Hαkb₂; simpl.
       rewrite Qnum_inv_Qnat_sub; auto.
       rewrite Qden_inv_Qnat_sub; auto.
       rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
       rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
       do 2 rewrite Pos2Z.inj_mul, Z.mul_assoc.
       apply Z.mul_cancel_r; auto.
       symmetry.
       rewrite Z.mul_shuffle0.
       rewrite Zposnat2Znat; auto.
       eapply αj_m_eq_p_r; eauto .

      assert (1 ≤ S b)%nat as H by fast_omega .
      apply Hpsi in H; simpl in H.
      rewrite <- Hc₁, <- Hpol₂ in H.
      rename H into Hps₂.
      remember Hns₂ as H; clear HeqH.
      eapply r_n_next_ns with (pol := pol₁) in H; eauto .
      destruct H as (αj₂, (αk₂, H)).
      destruct H as (Hini₂, (Hfin₂, (Hαj₂, Hαk₂))).
      rewrite Nat.add_1_r; simpl.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂, <- Hc₂, <- Hpol₃, <- Hns₃.
      rewrite Nat.add_comm in Hpolb₃; simpl in Hpolb₃.
      rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in Hpolb₃.
      rewrite <- Hpolb₃.
      remember (nth_ns b pol₃ ns₃) as nsb₃ eqn:Hnsb₃ .
      remember Hns₃ as H; clear HeqH.
      eapply nth_ns_n with (c := c₂) in H; eauto .
      rewrite <- Hnsb₃ in H.
      erewrite nth_pol_n with (c₁ := c₂) in H; eauto .
      rewrite <- Hpolb₃ in H.
      rename H into Hbns₂.
      remember Hbns₂ as H; clear HeqH.
      erewrite <- nth_pol_n with (c₁ := c₂) in Hpolb₃; eauto .
      remember (ac_root (Φq polb₃ nsb₃)) as cb₃ eqn:Hcb₃ .
      remember (S b) as b₁.
      remember (S b₁) as b₂.
      pose proof (Hri (S b₂)) as Hrb₂; simpl in Hrb₂.
      rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hrb₂.
      subst b₂; simpl in Hrb₂.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hrb₂.
      subst b₁; simpl in Hrb₂.
      rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in Hrb₂.
      erewrite nth_r_n in Hrb₂; eauto .
      erewrite nth_pol_n with (c₁ := c₂) in Hpolb₃; eauto .
      rewrite <- Hpolb₃ in Hrb₂.
      erewrite nth_c_root in Hrb₂; eauto .
      rewrite <- Hcb₃ in Hrb₂.
      erewrite <- nth_pol_n with (c₁ := c₂) in Hpolb₃; eauto .
      eapply r_n_next_ns in H; eauto .
      destruct H as (αjb₃, (αkb₃, H)).
      destruct H as (Hinib₃, (Hfinb₃, (Hαjb₃, Hαkb₃))).
      remember Hbns₂ as Hnsb₃nz; clear HeqHnsb₃nz.
      eapply newton_segments_not_nil in Hnsb₃nz; eauto .
      remember Hbns₂ as Hnsb₃₁; clear HeqHnsb₃₁.
      apply List_hd_in in Hnsb₃₁; eauto .
      unfold root_tail_from_cγ_list; simpl.
      rewrite Hinib₂, Hfinb₂, Hinib₃, Hfinb₃; simpl.
      rewrite Hαkb₂, Hαkb₃; simpl.
      rewrite Qnum_inv_Qnat_sub; auto.
      rewrite Qden_inv_Qnat_sub; auto.
      rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
      rewrite Z.add_0_r, Z.mul_1_r.
      rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
      do 2 rewrite Pos2Z.inj_mul.
      rewrite Z.div_mul_cancel_r; simpl; auto.
      rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
      do 2 rewrite Pos2Z.inj_mul.
      rewrite Z.div_mul_cancel_r; auto.
      remember Hns₂ as Hns₂nz; clear HeqHns₂nz.
      eapply newton_segments_not_nil in Hns₂nz; eauto .
      remember Hns₂ as Hns₂₁; clear HeqHns₂₁.
      apply List_hd_in in Hns₂₁; eauto .
      erewrite αj_m_eq_p_r with (ns₁ := nsb₂); eauto .
      assert (pol_in_K_1_m polb₃ m₁) as HKb₃.
       erewrite nth_pol_n with (c₁ := c₁) (n := S b) in Hpolb₃; eauto .
        eapply nth_pol_in_K_1_m with (ns := ns₂); eauto .
         replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
         eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .
         symmetry.
         eapply q_eq_1_any_r with (ns := ns₁) (αk := αk₁); eauto .
         rewrite Hr₁; eauto .

         intros i.
         pose proof (Hri₁ (S i)) as H.
         simpl in H.
         rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
         assumption.

         intros i Hi.
         destruct (eq_nat_dec i (S b)) as [H₂| H₂].
          subst i; simpl.
          rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
          simpl in Hpolb₃.
          rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in Hpolb₃.
          rewrite <- Hpolb₃.
          apply order_fin.
          erewrite order_in_newton_segment; eauto ; [ idtac | left; eauto  ].
          intros H; discriminate H.

          assert (S i ≤ S b) as H by fast_omega Hi H₂.
          apply Hpsi in H; simpl in H.
          rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in H.
          assumption.

        simpl; rewrite <- Hc₁, <- Hpol₂, <- Hns₂; assumption.

        simpl; rewrite <- Hc₁, <- Hpol₂, <- Hns₂; assumption.

       erewrite αj_m_eq_p_r with (ns₁ := nsb₃) (pol₁ := polb₃); eauto .
       rewrite Z.mul_shuffle0, Zposnat2Znat; auto.
       rewrite <- Zposnat2Znat; eauto .
       rewrite <- Z.mul_assoc, Z.div_mul; simpl; auto.
       rewrite Z.mul_shuffle0.
       rewrite <- Z.mul_assoc, Z.div_mul; auto.
       unfold ps_add, ps_mul; simpl.
       unfold cm; simpl.
       rewrite fold_series_const.
       unfold ps_terms_add; simpl.
       rewrite fold_series_const.
       unfold ps_ordnum_add; simpl.
       erewrite nth_γ_n; eauto ; simpl.
       rewrite Hαkb₂; simpl.
       erewrite Qnum_inv_Qnat_sub; eauto .
       erewrite Qden_inv_Qnat_sub; eauto ; simpl.
       rewrite Nat.sub_0_r, Z.mul_1_r, Z.add_0_r.
       remember (p_of_m m₁ (γ nsb₃)) as pb₃ eqn:Hpb₃ .
       remember (Pos.of_nat r) as rq eqn:Hrq .
       remember (Qden αjb₂ * Qden αkb₂ * rq)%positive as dd.
       remember (Qnum αjb₂ * ' Qden αkb₂)%Z as nd.
       assert (0 < Z.to_nat pb₃)%nat as Hpb₃pos.
        subst pb₃.
        unfold p_of_m; simpl.
        rewrite Hinib₃, Hfinb₃; simpl.
        rewrite Hαkb₃; simpl.
        rewrite Qnum_inv_Qnat_sub; auto.
        rewrite Qden_inv_Qnat_sub; auto.
        rewrite Z.add_0_r, Z.mul_1_r, Nat.sub_0_r.
        do 2 rewrite Pos2Z.inj_mul.
        remember (Qnum αjb₃ * ' Qden αkb₃ * ' m₁)%Z as x.
        rewrite Z.mul_shuffle0 in Heqx.
        rewrite Z.mul_shuffle0; subst x.
        rewrite Z.gcd_mul_mono_r; simpl.
        rewrite Z.div_mul_cancel_r; auto.
         rewrite <- Z2Nat.inj_0.
         apply Z2Nat.inj_lt; auto; [ reflexivity | idtac | idtac ].
          apply Z.div_pos.
           apply Z.mul_nonneg_nonneg; auto.
           apply Z.lt_le_incl; auto.

           remember (Qnum αjb₃ * ' m₁)%Z as x.
           remember (Qden αjb₃ * Pos.of_nat r)%positive as y.
           pose proof (Z.gcd_nonneg x (' y)) as H.
           assert (Z.gcd x (' y) ≠ 0)%Z as HH; [ idtac | omega ].
           intros HH.
           apply Z.gcd_eq_0_r in HH.
           revert HH; apply Pos2Z_ne_0.

          rewrite Z.gcd_comm.
          apply Z_div_gcd_r_pos.
          apply Z.mul_pos_pos; auto.
          apply Pos2Z.is_pos.

         intros H.
         apply Z.gcd_eq_0_r in H.
         revert H; apply Pos2Z_ne_0.

        rewrite series_stretch_const.
        rewrite series_mul_1_l.
        do 2 rewrite Z2Nat_sub_min.
        rewrite Z.mul_add_distr_r.
        rewrite Pos2Z.inj_mul, Z.mul_assoc, Z.mul_shuffle0.
        rewrite Z.sub_add_distr, Z.sub_diag; simpl.
        rewrite Z.add_simpl_l.
        rewrite Z.min_l.
         rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
         unfold adjust_series.
         rewrite series_stretch_const.
         rewrite <- series_stretch_stretch.
         rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
         unfold adjust_ps; simpl.
         rewrite series_shift_0.
         rewrite Z.sub_0_r.
         apply mkps_morphism.
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
              erewrite nth_c_root; eauto .

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
             erewrite αj_m_eq_p_r with (pol₁ := polb₃); eauto .
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
             rewrite find_coeff_more_iter with (r := r); auto.
              symmetry.
              rewrite find_coeff_more_iter with (r := r); auto.
               symmetry.
               remember (S i) as si.
               remember (S (S id)) as ssid; simpl.
               rewrite <- Hcb₂, <- Hpolb₃.
               erewrite <- nth_ns_n with (ns := ns₂); eauto .
               rewrite <- Hnsb₃.
               destruct i;
                [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
               clear H₁.
               destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [H₁| H₁].
                contradiction.

                clear H₁.
                erewrite next_pow_eq_p; eauto .
                rewrite <- Hpb₃.
                subst si ssid.
                remember (S i) as si.
                remember (S id) as sid; simpl.
                destruct (ps_zerop R (ps_poly_nth 0 polb₃)) as [| H₁]; auto.
                clear H₁.
                subst si.
                remember (Nat.compare (Z.to_nat pb₃) (S i)) as cmp₁ eqn:Hcmp₁ .
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
                 subst sid.
                 remember (Z.to_nat pb₃) as x.
                 replace x with (0 + x)%nat by reflexivity.
                 rewrite next_pow_add.
                 replace (S i)%nat with (S i - x + x)%nat at 2
                  by fast_omega Hcmp₁.
                 rewrite find_coeff_add.
                 rewrite <- Heqid.
                 apply xxx with (r := r); auto.
bbb.
  ============================
   nsb₄ ∈ newton_segments polb₄

subgoal 2 is:
 pol_in_K_1_m polb₄ m₁
subgoal 3 is:
 q_of_m m₁ (γ nsb₄) = 1%positive
subgoal 4 is:
 ∀ j : nat, nth_r j polb₄ nsb₄ = r
subgoal 5 is:
 ∀ j : nat, j ≤ S (S i) → (ps_poly_nth 0 (nth_pol j polb₄ nsb₄) ≠ 0)%ps
subgoal 6 is:
 (S id < S i)%nat
subgoal 7 is:
 S i ≤ S (S id)
subgoal 8 is:
 (0 =
  match match id with
        | 0 => Eq
        | S _ => Lt
        end with
  | Eq => ac_root (Φq polb₃ nsb₃)
  | Lt =>
      find_coeff sid
        (next_pow 0
           (List.hd phony_ns
              (newton_segments
                 (next_pol polb₃ (β nsb₃) (γ nsb₃) (ac_root (Φq polb₃ nsb₃)))))
           m₁) m₁
        (next_pol polb₃ (β nsb₃) (γ nsb₃) (ac_root (Φq polb₃ nsb₃)))
        (List.hd phony_ns
           (newton_segments
              (next_pol polb₃ (β nsb₃) (γ nsb₃) (ac_root (Φq polb₃ nsb₃)))))
        id
  | Gt => 0
  end)%K
subgoal 9 is:
 q_of_m m₁ (γ nsb₃) = 1%positive
subgoal 10 is:
 ∀ j : nat, nth_r j polb₃ nsb₃ = r
subgoal 11 is:
 ∀ j : nat, j ≤ S (S id) → (ps_poly_nth 0 (nth_pol j polb₃ nsb₃) ≠ 0)%ps
subgoal 12 is:
 q_of_m m₁ (γ nsb₂) = 1%positive
subgoal 13 is:
 ∀ j : nat, nth_r j polb₂ nsb₂ = r
subgoal 14 is:
 ∀ j : nat, j ≤ S (S i) → (ps_poly_nth 0 (nth_pol j polb₂ nsb₂) ≠ 0)%ps
subgoal 15 is:
 (- pb₃ <= 0)%Z
subgoal 16 is:
 (p_of_m m₁ (γ nsb₂) * ' (dd * dd))%Z = (nd * ' m₁ * ' dd)%Z
subgoal 17 is:
 (m₁ * (dd * dd))%positive = (dd * (dd * m₁))%positive
subgoal 18 is:
 (nd * ' m₁ * ' dd <= nd * ' m₁ * ' dd + pb₃ * ' dd * ' dd)%Z
*)

(*
Theorem root_tail_when_r_r : ∀ pol ns pol₁ ns₁ c m q₀ b r,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = r
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ∀ n,
    (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b n pol₁ ns₁ +
       ps_monom 1%K (γ_sum b n pol₁ ns₁) *
       root_tail (m * q₀) (b + S n) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b r Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ n.
remember (m * q₀)%positive as m₁.
revert pol ns pol₁ ns₁ Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁.
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
  rewrite root_tail_from_0; eauto .
*)

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
      remember (newton_segments polsi) as nsl eqn:Hnsl .
      symmetry in Hnsl.
      destruct nsl as [| ns₂].
       Focus 2.
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

         intros H; rewrite H in Hnsl; discriminate Hnsl.

        destruct Hri as (s₁, Hs₁).
        remember (zerop_1st_n_const_coeff i pol₁ ns₁) as z eqn:Hz .
        symmetry in Hz.
        destruct z.
         Focus 2.
         remember (root_head 0 i pol₁ ns₁) as rh.
         remember (ps_monom 1%K (γ_sum 0 i pol₁ ns₁)) as mo.
         exists (rh + mo * s₁)%ps; subst rh mo.
         rewrite apply_nth_pol; auto.
         erewrite <- nth_pol_n; eauto .
         erewrite <- nth_c_root; eauto .
         rewrite Hs₁, rng_mul_0_r; reflexivity.

         apply lowest_zerop_1st_n_const_coeff in Hz.
         destruct Hz as (m, (Hmi, (Hle, Heq))).
         destruct Hle as [Hle| Hle].
          subst m.
          simpl in Heq.
          destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
           2: discriminate Heq.

           exists 0%ps.
           apply a₀_0_root_0; assumption.

          eapply root_when_fin; eauto .

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

          eapply root_when_fin; eauto .

         eapply List_hd_in; eauto .
         clear H.
         remember Hns as H; clear HeqH.
         eapply next_has_root_0_or_newton_segments in H; eauto .
         simpl in H.
         rewrite <- Hc, <- Hpol₁ in H.
         destruct H; auto.
bbb.

End theorems.
