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
Require Import Puiseux.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Lemma find_coeff_step : ∀ pol ns m c pol₁ ns₁ i di p dp np,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a : puiseux_series α, in_K_1_m a m) (al pol)
  → q_of_m m (γ ns) = 1%positive
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (0 < p ≤ i)%nat
  → (di ≤ dp + 1)%nat
  → np = next_pow (p + dp) ns₁ m
  → (find_coeff i np m pol₁ ns₁ (i + di) =
     find_coeff (S i - p) np m pol₁ ns₁ (i + di))%K.
Proof.
intros pol ns m c pol₁ ns₁ i di p dp np.
intros Hns HK Hq Hc Hr Hpol₁ Hns₁ (Hp, Hpi) Hdip Hnp.
remember (S i - p)%nat as id.
revert pol ns c pol₁ ns₁ id di p dp np Hns HK Hq Hc Hr Hpol₁
 Hns₁ Heqid Hp Hpi Hdip Hnp.
induction i; intros.
 destruct p; [ exfalso; revert Hp; apply Nat.lt_irrefl | idtac ].
 exfalso; revert Hpi; apply Nat.nle_succ_0.

 destruct id; [ exfalso; fast_omega Hpi Heqid | simpl ].
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁]; auto.
 unfold next_pow in Hnp; simpl in Hnp.
 remember Hr as H; clear HeqH.
 eapply r_1_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hoth₁, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
 rewrite Hini₁, Hfin₁ in Hnp; simpl in Hnp.
 rewrite Hαk₁ in Hnp; simpl in Hnp.
 rewrite Z.add_0_r, Z.mul_1_r in Hnp.
 do 2 rewrite Pos.mul_1_r in Hnp.
 rewrite Z.mul_shuffle0 in Hnp.
 rewrite Pos2Z.inj_mul in Hnp.
 rewrite Z.div_mul_cancel_r in Hnp; auto.
 remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
 eapply hd_newton_segments in Hns₁₁; eauto .
 remember (Nat.compare np (S (i + di))) as cmp₁ eqn:Hnpi .
 symmetry in Hnpi.
 destruct cmp₁; auto.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 remember (next_pow np ns₂ m) as nnp eqn:Hnnp .
 apply nat_compare_lt in Hnpi.
 assert (ps_lap_forall (λ a, in_K_1_m a m) (al pol₁)) as HK₁.
  replace m with (m * 1)%positive by apply Pos.mul_1_r.
  eapply next_pol_in_K_1_mq with (pol := pol); eauto .

  remember Hns₁₁ as H; clear HeqH.
  eapply num_m_den_is_pos with (m := m) in H; eauto .
  rewrite <- Nat.add_succ_r.
  assert (q_of_m m (γ ns₁) = 1%positive) as Hq₁.
   replace m with (m * 1)%positive by apply Pos.mul_1_r.
   eapply q_eq_1 with (pol := pol) (pol₁ := pol₁); eauto .
   rewrite Pos.mul_1_r; assumption.

   remember Hns as Hr₁; clear HeqHr₁.
   eapply multiplicity_1_remains in Hr₁; eauto .
   subst np; rewrite <- Nat.add_assoc in Hnnp.
   eapply IHi with (p := p); eauto.
    fast_omega H Heqid.

    fast_omega H Hnpi Hdip.

    fast_omega H Hdip.
Qed.

Lemma root_head_0 : ∀ pol ns b n,
  (ps_poly_nth 0 pol = 0)%ps
  → (root_head b n pol ns = 0)%ps.
Proof.
intros pol ns b n H.
unfold root_head.
destruct (ps_zerop R (ps_poly_nth 0 pol)); [ reflexivity | idtac ].
contradiction.
Qed.

Lemma root_head_succ : ∀ pol ns b n,
  (ps_poly_nth 0 pol ≠ 0)%ps
  → (root_head b (S n) pol ns =
     root_head b n pol ns +
     ps_monom (nth_c (b + S n) pol ns) (γ_sum b (S n) pol ns))%ps.
Proof.
intros pol ns b n Hp₀.
unfold root_head.
destruct (ps_zerop R (ps_poly_nth 0 pol)); [ contradiction | idtac ].
rewrite summation_split_last; [ reflexivity | apply Nat.le_0_l ].
Qed.

Lemma root_tail_succ : ∀ pol ns m n c pol₁ ns₁,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (root_tail m (S n) pol ns = root_tail m n pol₁ ns₁)%ps.
Proof.
intros pol ns m n c pol₁ ns₁ Hc Hpol₁ Hns₁.
unfold root_tail; simpl.
rewrite <- Hc, <- Hpol₁, <- Hns₁.
reflexivity.
Qed.

Lemma nth_c_root : ∀ pol₁ ns₁ poln nsn n,
  poln = nth_pol n pol₁ ns₁
  → nsn = nth_ns n pol₁ ns₁
  → (nth_c n pol₁ ns₁ = ac_root (Φq poln nsn))%K.
Proof.
intros pol₁ ns₁ poln nsn n Hpoln Hnsn.
revert pol₁ ns₁ poln nsn Hpoln Hnsn.
induction n; intros.
 simpl in Hpoln, Hnsn; simpl.
 subst poln nsn; reflexivity.

 simpl in Hpoln, Hnsn; simpl.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 apply IHn; assumption.
Qed.

Lemma nth_pol_n : ∀ pol₁ ns₁ c₁ pol₂ ns₂ poln nsn cn n,
  c₁ = ac_root (Φq pol₁ ns₁)
  → pol₂ = next_pol pol₁ (β ns₁) (γ ns₁) c₁
  → ns₂ = List.hd phony_ns (newton_segments pol₂)
  → poln = nth_pol n pol₁ ns₁
  → nsn = nth_ns n pol₁ ns₁
  → cn = ac_root (Φq poln nsn)
  → next_pol poln (β nsn) (γ nsn) cn = nth_pol n pol₂ ns₂.
Proof.
intros pol₁ ns₁ c₁ pol₂ ns₂ poln nsn cn n.
intros Hc₁ Hpol₂ Hns₂ Hpoln Hnsn Hcn.
revert pol₁ ns₁ c₁ pol₂ ns₂ poln nsn cn Hc₁ Hpol₂ Hns₂ Hpoln Hnsn Hcn.
induction n; intros.
 simpl in Hpoln, Hnsn; simpl.
 subst poln nsn pol₂ c₁ cn; reflexivity.

 simpl in Hpoln, Hnsn; simpl.
 remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
 remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
 remember (List.hd phony_ns (newton_segments pol₃)) as ns₃ eqn:Hns₃ .
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hpoln, Hnsn.
 eapply IHn; eauto .
Qed.

Lemma nth_ns_n : ∀ pol ns c pol₁ ns₁ poln nsn cn npoln n,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → poln = nth_pol n pol ns
  → nsn = nth_ns n pol ns
  → cn = ac_root (Φq poln nsn)
  → npoln = next_pol poln (β nsn) (γ nsn) cn
  → nth_ns n pol₁ ns₁ = List.hd phony_ns (newton_segments npoln).
Proof.
intros pol ns c pol₁ ns₁ poln nsn cn npoln n.
intros Hc Hpol₁ Hns₁ Hpoln Hnsn Hcn Hnpoln.
revert pol ns c pol₁ ns₁ poln nsn cn npoln Hc Hpol₁ Hns₁ Hpoln Hnsn Hcn
 Hnpoln.
induction n; intros.
 simpl in Hpoln, Hnsn; simpl.
 subst poln nsn npoln pol₁ ns₁ c cn.
 reflexivity.

 simpl in Hpoln, Hnsn; simpl.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hpoln, Hnsn.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂.
 rename Heqns₂ into Hns₂.
 eapply IHn with (c := c₁); eauto .
Qed.

Lemma nth_γ_n : ∀ pol ns n nsn jn αjn kn αkn,
  nsn = nth_ns n pol ns
  → ini_pt nsn = (jn, αjn)
  → fin_pt nsn = (kn, αkn)
  → nth_γ n pol ns = (αjn - αkn) / (kn - jn).
Proof.
intros pol ns n nsn jm αjn kn αkn Hnsn Hini Hfin.
revert pol ns nsn jm αjn kn αkn Hnsn Hini Hfin.
induction n; intros.
 simpl in Hnsn; simpl.
 subst nsn; unfold γ; simpl.
 rewrite Hini, Hfin; simpl.
 reflexivity.

 simpl in Hnsn; simpl.
 eapply IHn; eauto .
Qed.

Lemma root_tail_nth : ∀ pol ns m a b,
  (root_tail m (a + b) pol ns =
   root_tail m a (nth_pol b pol ns) (nth_ns b pol ns))%ps.
Proof.
intros pol ns m a b.
revert pol ns m b.
induction a; intros; simpl.
 revert pol ns m.
 induction b; intros; [ reflexivity | simpl ].
 remember (ac_root (Φq pol ns)) as c eqn:Hc .
 remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 rewrite <- IHb.
 eapply root_tail_succ; eauto .

 rewrite root_tail_succ; eauto ; symmetry.
 rewrite root_tail_succ; eauto ; symmetry.
 remember (ac_root (Φq pol ns)) as c eqn:Hc .
 remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 rewrite IHa.
 remember (nth_ns b pol ns) as nsb eqn:Hnsb .
 remember (nth_pol b pol ns) as polb eqn:Hpolb .
 remember (ac_root (Φq polb nsb)) as cb eqn:Hcb .
 remember (next_pol polb (β nsb) (γ nsb) cb) as npolb.
 rename Heqnpolb into Hnpolb.
 remember (List.hd phony_ns (newton_segments npolb)) as nnsb.
 rename Heqnnsb into Hnnsb.
 erewrite <- nth_pol_n with (c₁ := c); eauto .
 rewrite <- Hnpolb.
 erewrite nth_ns_n with (c := c); eauto .
 subst nnsb; reflexivity.
Qed.

Lemma nth_in_newton_segments : ∀ pol₁ ns₁ c₁ poln nsn n,
  ns₁ ∈ newton_segments pol₁
  → c₁ = ac_root (Φq pol₁ ns₁)
  → root_multiplicity acf c₁ (Φq pol₁ ns₁) = 1%nat
  → (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
  → poln = nth_pol n pol₁ ns₁
  → nsn = nth_ns n pol₁ ns₁
  → nsn ∈ newton_segments poln.
Proof.
intros pol₁ ns₁ c₁ poln nsn n Hns₁ Hc₁ Hr₁ Hpsi Hpoln Hnsn.
subst poln nsn.
revert pol₁ ns₁ c₁ Hns₁ Hc₁ Hr₁ Hpsi.
induction n; intros; [ assumption | simpl ].
rewrite <- Hc₁.
remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
assert (1 ≤ S n) as H₁.
 apply -> Nat.succ_le_mono.
 apply Nat.le_0_l.

 apply Hpsi in H₁; simpl in H₁.
 rewrite <- Hc₁, <- Hpol₂ in H₁.
 eapply IHn; eauto .
  remember Hns₂ as H; clear HeqH.
  apply exists_ini_pt_nat_fst_seg in H.
  destruct H as (j₂, (αj₂, Hini₂)).
  remember Hns₂ as H; clear HeqH.
  apply exists_fin_pt_nat_fst_seg in H.
  destruct H as (k₂, (αk₂, Hfin₂)).
  eapply hd_newton_segments; eauto .
  remember Hns₁ as H; clear HeqH.
  eapply r_1_j_0_k_1 in H; try eassumption.
  destruct H as (Hj₂, (Hk₂, (Hαj₂, (Hαk₂, Hoth₂)))).
  subst j₂ k₂; apply Nat.lt_0_1.

  eapply multiplicity_1_remains; eauto .

  intros i Hin.
  apply Nat.succ_le_mono in Hin.
  apply Hpsi in Hin; simpl in Hin.
  rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
  assumption.
Qed.

Lemma root_tail_split_1st : ∀ pol ns pol₁ ns₁ c m q₀,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (ps_poly_nth 0 (nth_pol 0 pol₁ ns₁) ≠ 0)%ps
  → (root_tail (m * q₀) 0 pol₁ ns₁ =
     root_head 0 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum 0 0 pol₁ ns₁) *
       root_tail (m * q₀) 1 pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ Hps₀.
remember (m * q₀)%positive as m₁.
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
unfold root_tail, root_head; simpl.
destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [| H₁].
 contradiction.

 clear H₁.
 remember Hns as HinK1m₁; clear HeqHinK1m₁.
 eapply next_pol_in_K_1_mq in HinK1m₁; eauto .
 remember Hns as H; clear HeqH.
 eapply r_1_j_0_k_1 in H; try eassumption.
 destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
 subst j₁ k₁; simpl.
 unfold Qlt in Hαj₁; simpl in Hαj₁.
 unfold Qeq in Hαk₁; simpl in Hαk₁.
 rewrite Z.mul_1_r in Hαj₁, Hαk₁.
 remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
 eapply hd_newton_segments in Hns₁₁; eauto .
 remember Hns₁₁ as HK₂; clear HeqHK₂.
 eapply next_pol_in_K_1_mq in HK₂; eauto .
 erewrite q_eq_1 with (q₀ := q₀) (ns := ns) in HK₂; eauto .
 rewrite Pos.mul_1_r, <- Heqm₁ in HK₂.
 unfold γ_sum; simpl.
 unfold summation; simpl.
 do 2 rewrite rng_add_0_r.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 remember Hns₂ as Hini₂; clear HeqHini₂.
 apply exists_ini_pt_nat_fst_seg in Hini₂.
 destruct Hini₂ as (j₂, (αj₂, Hini₂)).
 remember Hns₂ as Hfin₂; clear HeqHfin₂.
 apply exists_fin_pt_nat_fst_seg in Hfin₂.
 destruct Hfin₂ as (k₂, (αk₂, Hfin₂)).
 destruct (ps_zerop _ (ps_poly_nth 0 pol₂)) as [Hps₁| Hps₁].
  rewrite ps_mul_0_r, ps_add_0_r.
  unfold root_from_cγ_list, ps_monom; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Hαk₁; simpl.
  rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
  rewrite Z.mul_shuffle0.
  rewrite Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_r; auto.
  rewrite ps_adjust_eq with (n := O) (k := (Qden αj₁ * Qden αk₁)%positive).
  symmetry.
  rewrite ps_adjust_eq with (n := O) (k := m₁).
  unfold adjust_ps; simpl.
  rewrite fold_series_const.
  do 2 rewrite series_shift_0.
  rewrite series_stretch_const.
  do 2 rewrite Z.sub_0_r.
  symmetry.
  rewrite Z.mul_comm.
  rewrite <- Z.divide_div_mul_exact; auto.
   rewrite Pos2Z.inj_mul, <- Z.mul_assoc, Z.mul_comm, Z.mul_assoc.
   rewrite Z.div_mul; auto.
   apply mkps_morphism.
    unfold series_stretch.
    constructor; intros i; simpl.
    destruct (zerop (i mod Pos.to_nat (Qden αj₁ * Qden αk₁))) as [H₁| H₁].
     apply Nat.mod_divides in H₁; auto.
     destruct H₁ as (d, Hd).
     rewrite Nat.mul_comm in Hd.
     rewrite Hd.
     rewrite Nat.div_mul; auto.
     unfold root_series_from_cγ_list.
     rewrite <- Hd.
     destruct (zerop i) as [H₁| H₁].
      subst i.
      apply Nat.eq_mul_0_l in H₁; auto.
      subst d; simpl; rewrite <- Hc₁.
      destruct (ps_zerop R (ps_poly_nth 0 pol₁)); auto; contradiction.

      simpl.
      rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
      destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂]; auto.
      destruct d.
       rewrite Hd in H₁.
       exfalso; revert H₁; apply Nat.lt_irrefl.

       simpl.
       destruct (ps_zerop R (ps_poly_nth 0 pol₂)); auto; contradiction.

     destruct (zerop i); [ subst i | reflexivity ].
     rewrite Nat.mod_0_l in H₁; auto.
     exfalso; revert H₁; apply Nat.lt_irrefl.

    rewrite Z.mul_comm, Z.mul_assoc, Z.mul_shuffle0.
    rewrite <- Z.mul_assoc, Z.mul_comm; reflexivity.

    rewrite Pos.mul_comm; reflexivity.

   eapply den_αj_divides_num_αj_m; eauto .
   rewrite Heqm₁.
   eapply next_pol_in_K_1_mq in Hm; eauto .

  remember Hns as Hr₁; clear HeqHr₁.
  eapply multiplicity_1_remains in Hr₁; eauto .
  remember Hns₁₁ as H; clear HeqH.
  eapply r_1_j_0_k_1 in H; try eassumption.
  destruct H as (Hj₂, (Hk₂, (Hαj₂, (Hαk₂, Hoth₂)))).
  subst j₂ k₂; simpl.
  unfold Qlt in Hαj₂; simpl in Hαj₂.
  unfold Qeq in Hαk₂; simpl in Hαk₂.
  rewrite Z.mul_1_r in Hαj₂, Hαk₂.
  unfold root_from_cγ_list; simpl.
  rewrite Hini₁, Hfin₁, Hini₂, Hfin₂; simpl.
  rewrite Hαk₁, Hαk₂; simpl.
  do 2 rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
  rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_r; auto.
  rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_r; auto.
  unfold ps_add, ps_mul; simpl.
  unfold cm; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Hαk₁; simpl.
  rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
  rewrite fold_series_const.
  unfold ps_terms_add; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Hαk₁; simpl.
  unfold ps_ordnum_add; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Hαk₁; simpl.
  rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
  remember (Qden αj₁ * Qden αk₁)%positive as dd.
  rewrite fold_series_const.
  rewrite series_stretch_const.
  rewrite series_mul_1_l.
  remember (Qnum αj₁ * ' Qden αk₁)%Z as nd.
  do 2 rewrite Z2Nat_sub_min.
  rewrite Z.mul_add_distr_r.
  rewrite Pos2Z.inj_mul, Z.mul_assoc, Z.mul_shuffle0.
  rewrite Z.sub_add_distr.
  rewrite Z.sub_diag; simpl.
  rewrite Z.add_simpl_l.
  rewrite Z.min_l.
   rewrite ps_adjust_eq with (n := O) (k := (dd * dd)%positive).
   unfold adjust_ps; simpl.
   rewrite series_shift_0.
   rewrite Z.sub_0_r.
   apply mkps_morphism.
    remember Hns₂ as Hns₂₁; clear HeqHns₂₁.
    eapply hd_newton_segments in Hns₂₁; eauto .
    remember Hns₂₁ as H; clear HeqH.
    eapply den_αj_divides_num_αj_m in H; eauto .
    remember Hns₂₁ as HH; clear HeqHH.
    eapply num_m_den_is_pos in HH; eauto .
    destruct H as (d, Hd).
    rewrite Hd in HH.
    rewrite Z.div_mul in HH; auto.
    rewrite Hd.
    rewrite Z.div_mul; auto.
    destruct d as [| d| d].
     exfalso; revert HH; apply Nat.lt_irrefl.

     clear HH; simpl.
     unfold adjust_series; simpl.
     rewrite series_shift_0.
     rewrite series_stretch_const.
     rewrite <- series_stretch_stretch.
     rewrite <- Pos.mul_assoc, Pos2Nat.inj_mul.
     rewrite <- stretch_shift_series_distr.
     rewrite <- series_stretch_const with (k := (dd * dd)%positive).
     rewrite <- series_stretch_add_distr.
     apply stretch_morph; [ reflexivity | idtac ].
     unfold series_add; simpl.
     constructor; intros i; simpl.
     destruct (zerop i) as [H₁| H₁].
      subst i; simpl.
      destruct (lt_dec 0 (Pos.to_nat d)) as [H₁| H₁].
       rewrite rng_add_0_r.
       unfold root_series_from_cγ_list; simpl.
       rewrite <- Hc₁.
       destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₂| H₂]; auto.
       contradiction.

       exfalso; apply H₁; auto.

      rewrite rng_add_0_l.
      assert (next_pow 0 ns₂ m₁ = Pos.to_nat d) as Hnpow.
       unfold next_pow; simpl.
       rewrite Hini₂, Hfin₂; simpl.
       rewrite Hαk₂; simpl.
       rewrite Z.add_0_r, Z.mul_1_r.
       do 2 rewrite Pos.mul_1_r.
       rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
       rewrite Z.div_mul_cancel_r; auto.
       rewrite Hd, Z.div_mul; auto.

       remember (next_pow 0 ns₂ m₁) as p₂.
       rewrite <- Hnpow.
       destruct (lt_dec i p₂) as [H₂| H₂].
        unfold root_series_from_cγ_list; simpl.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [| H₃]; auto.
        destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
        clear H₁.
        rewrite <- Hc₁, <- Hpol₂, <- Hns₂; simpl.
        destruct (ps_zerop R (ps_poly_nth 0 pol₂)) as [| H₅]; auto.
        rewrite <- Heqp₂.
        remember (Nat.compare p₂ (S i)) as cmp; symmetry in Heqcmp.
        destruct cmp as [H₄| H₄| H₄]; auto.
         apply nat_compare_eq in Heqcmp.
         rewrite Heqcmp in H₂.
         exfalso; revert H₂; apply Nat.lt_irrefl.

         apply nat_compare_lt in Heqcmp.
         apply Nat.lt_le_incl, Nat.nlt_ge in Heqcmp.
         contradiction.

        remember (i - p₂)%nat as id.
        unfold root_series_from_cγ_list.
        remember (S id) as x; simpl; subst x.
        destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₃| H₃].
         contradiction.

         rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
         rewrite <- Heqp₂, Heqid.
         destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
         apply Nat.nlt_ge in H₂.
         symmetry.
         rewrite <- find_coeff_add with (dp := p₂).
         rewrite Nat.add_0_l, Nat.sub_add; auto.
         symmetry.
         rewrite <- Heqid; simpl.
         destruct (ps_zerop R (ps_poly_nth 0 pol₂)); try contradiction.
         clear n.
         remember (Nat.compare p₂ (S i)) as cmp eqn:Hcmp .
         symmetry in Hcmp.
         destruct cmp; auto.
         remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
         remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
         remember (List.hd phony_ns (newton_segments pol₃)) as ns₃ eqn:Hns₃ .
         remember (next_pow p₂ ns₃ m₁) as p₂₃ eqn:Hp₂₃ .
         apply nat_compare_lt in Hcmp.
         clear H₁ H₂.
         assert (q_of_m m₁ (γ ns₂) = 1%positive) as Hq₂.
          replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
          rewrite <- Heqm₁ in HinK1m₁.
          eapply q_eq_1 with (pol := pol₁) (pol₁ := pol₂); eauto .
          rewrite Pos.mul_1_r; assumption.

          remember Hns₁₁ as Hr₂; clear HeqHr₂.
          eapply multiplicity_1_remains in Hr₂; eauto .
          rewrite <- Nat.add_1_r.
          assert (0 < p₂)%nat as Hp₁ by (rewrite Hnpow; auto).
          replace p₂ with (p₂ + 0)%nat in Hp₂₃ by omega.
          apply Nat.succ_le_mono in Hcmp.
          subst id.
          eapply find_coeff_step; eauto ; reflexivity.

     simpl in HH.
     exfalso; revert HH; apply Nat.lt_irrefl.

    rewrite Pos2Z.inj_mul, Z.mul_assoc.
    apply Z.mul_cancel_r; auto.
    subst dd nd.
    rewrite Pos2Z.inj_mul, Z.mul_assoc.
    symmetry; rewrite Z.mul_shuffle0.
    apply Z.mul_cancel_r; auto.
    symmetry.
    rewrite Z.mul_comm.
    rewrite <- Z.divide_div_mul_exact; auto.
     rewrite Z.mul_comm.
     rewrite Z.div_mul; auto.

     eapply den_αj_divides_num_αj_m; eauto .
     eapply next_pol_in_K_1_mq in Hm; eauto .
     subst m₁; assumption.

    rewrite Pos.mul_comm, Pos.mul_assoc.
    reflexivity.

   apply Z.le_sub_le_add_l.
   rewrite Z.sub_diag.
   apply Z.mul_nonneg_nonneg; auto.
   apply Z.mul_nonneg_nonneg; auto.
   apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
   apply Z.mul_nonneg_nonneg; auto.
   apply Z.lt_le_incl; assumption.
Qed.

Lemma lap_forall_nth : ∀ pol ns poln m c,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → q_of_m m (γ ns) = 1%positive
  → ∀ n,
    (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
    → poln = nth_pol n pol ns
    → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
    → ps_lap_forall (λ a, in_K_1_m a m) (al poln).
Proof.
intros pol ns poln m c Hns Hc Hr Hq n Hnz Hpoln HK.
revert pol ns poln m c Hns Hc Hr Hq Hnz Hpoln HK.
induction n; intros.
 simpl in Hpoln; subst poln; assumption.

 simpl in Hpoln.
 remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 remember Hns₁ as H; clear HeqH.
 apply exists_ini_pt_nat_fst_seg in H.
 destruct H as (j₁, (αj₁, Hini₁)).
 remember Hns₁ as H; clear HeqH.
 apply exists_fin_pt_nat_fst_seg in H.
 destruct H as (k₁, (αk₁, Hfin₁)).
 remember Hns as H; clear HeqH.
 eapply r_1_j_0_k_1 in H; try eassumption.
  destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
  subst j₁ k₁; simpl.
  unfold Qlt in Hαj₁; simpl in Hαj₁.
  unfold Qeq in Hαk₁; simpl in Hαk₁.
  rewrite Z.mul_1_r in Hαj₁, Hαk₁.
  eapply IHn with (pol := pol₁) (ns := ns₁); eauto .
   eapply hd_newton_segments; eauto .

   eapply multiplicity_1_remains; eauto .
   assert (1 ≤ S n) as H by omega.
   apply Hnz in H; simpl in H.
   rewrite <- Hc, <- Hpol₁ in H.
   assumption.

   replace m with (m * 1)%positive by apply Pos.mul_1_r.
   eapply q_eq_1; eauto .
    eapply next_pol_in_K_1_mq; eauto .

    assert (1 ≤ S n) as H by omega.
    apply Hnz in H; simpl in H.
    rewrite <- Hc, <- Hpol₁ in H.
    assumption.

   intros i Hin.
   apply Nat.succ_le_mono in Hin.
   apply Hnz in Hin; simpl in Hin.
   rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hin.
   assumption.

   rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hpoln.
   assumption.

   replace m with (m * 1)%positive by apply Pos.mul_1_r.
   eapply next_pol_in_K_1_mq; eauto .

  clear H.
  assert (1 ≤ S n) as H by omega.
  apply Hnz in H; simpl in H.
  rewrite <- Hc, <- Hpol₁ in H.
  assumption.
Qed.

Lemma root_tail_from_0 : ∀ pol ns pol₁ ns₁ c m q₀ b,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (∀ i, (i ≤ b)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
  → (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum b 0 pol₁ ns₁) *
       root_tail (m * q₀) (b + 1) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ Hpsi.
remember (m * q₀)%positive as m₁.
destruct b; [ subst m₁; eapply root_tail_split_1st; eauto  | idtac ].
remember (S b) as b₁ eqn:Hb₁ .
unfold root_tail, root_head; simpl.
destruct (ps_zerop _ (ps_poly_nth 0 (nth_pol b₁ pol₁ ns₁))) as [Hpsb| Hpsb].
 pose proof (Hpsi b₁ (Nat.le_refl b₁)); contradiction.

 unfold summation; simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  pose proof (Hpsi 0%nat (Nat.le_0_l b₁)); contradiction.

  clear H₁.
  rewrite Nat.add_0_r, ps_add_0_r.
  remember Hns as HK₁; clear HeqHK₁.
  eapply next_pol_in_K_1_mq in HK₁; eauto .
  rewrite <- Heqm₁ in HK₁.
  pose proof (Hpsi O (Nat.le_0_l b₁)) as Hps₀.
  remember Hns₁ as H; clear HeqH.
  eapply r_1_next_ns in H; eauto .
  destruct H as (αj₁, (αk₁, H)).
  destruct H as (Hoth₁, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
  remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
  eapply hd_newton_segments in Hns₁₁; eauto .
  remember Hns₁₁ as HK₂; clear HeqHK₂.
  rewrite Heqm₁ in HK₁.
  eapply next_pol_in_K_1_mq in HK₂; eauto .
  erewrite q_eq_1 with (q₀ := q₀) (ns := ns) in HK₂; eauto .
  rewrite <- Heqm₁ in HK₁.
  rewrite Pos.mul_1_r, <- Heqm₁ in HK₂.
  remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
  remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
  remember Hr as Hr₁; clear HeqHr₁.
  eapply multiplicity_1_remains in Hr₁; eauto .
  remember Hns₁₁ as H; clear HeqH.
  eapply nth_in_newton_segments with (n := b₁) in H; eauto .
  remember (nth_pol b₁ pol₁ ns₁) as polb eqn:Hpolb .
  remember (nth_ns b₁ pol₁ ns₁) as nsb eqn:Hnsb .
  rename H into Hbns.
  remember Hbns as H; clear HeqH.
  apply exists_ini_pt_nat in H.
  destruct H as (jb, (αjb, Hinib)).
  remember Hbns as H; clear HeqH.
  apply exists_fin_pt_nat in H.
  destruct H as (kb, (αkb, Hfinb)).
  remember (ac_root (Φq polb nsb)) as cb eqn:Hcb .
  remember Hr as Hrb; clear HeqHrb.
  eapply multiplicity_1_remains_in_nth in Hrb; eauto .
  remember (nth_pol (b₁ + 1) pol₁ ns₁) as polb₂ eqn:Hpolb₂ .
  subst b₁.
  simpl in Hpolb, Hnsb, Hpolb₂.
  rewrite <- Hc₁, <- Hpol₂ in Hpolb, Hnsb, Hpolb₂.
  remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
  remember Hns₁₁ as H; clear HeqH.
  eapply nth_in_newton_segments with (n := b) in H; eauto .
  remember Hns as Hrb₁; clear HeqHrb₁.
  eapply multiplicity_1_remains_in_nth with (n := b) in Hrb₁; eauto .
  remember (nth_ns b pol₁ ns₁) as nsb₁ eqn:Hnsb₁ .
  remember (nth_pol b pol₁ ns₁) as polb₁ eqn:Hpolb₁ .
  remember (ac_root (Φq polb₁ nsb₁)) as cb₁ eqn:Hcb₁ .
  rewrite Hpolb in Hpsb.
  erewrite <- nth_pol_n with (c₁ := c₁) in Hpsb; eauto .
  erewrite nth_ns_n with (c := c₁) in Hnsb; eauto .
  eapply r_1_j_0_k_1 with (ns₁ := nsb) in H; eauto .
  erewrite <- nth_ns_n with (c := c₁) in Hnsb; eauto .
  erewrite nth_pol_n with (c₁ := c₁) in Hpsb; eauto .
  rewrite <- Hpolb in Hpsb.
  destruct H as (Hjb, (Hkb, (Hαjb, (Hαkb, Hothb)))).
  subst jb kb.
  unfold Qlt in Hαjb; simpl in Hαjb.
  unfold Qeq in Hαkb; simpl in Hαkb.
  rewrite Z.mul_1_r in Hαjb, Hαkb.
  destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [H₁| H₁].
   rewrite rng_mul_0_r, rng_add_0_r.
   unfold γ_sum; simpl.
   unfold summation; simpl.
   rewrite Nat.add_0_r, rng_add_0_r.
   rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
   unfold root_from_cγ_list, ps_monom; simpl.
   rewrite Hinib, Hfinb; simpl.
   rewrite Hαkb; simpl.
   rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
   rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
   rewrite Z.div_mul_cancel_r; auto.
   rewrite ps_adjust_eq with (n := O) (k := Qden (nth_γ b pol₂ ns₂)).
   symmetry.
   rewrite ps_adjust_eq with (n := O) (k := m₁).
   symmetry.
   unfold adjust_ps; simpl.
   rewrite Pos.mul_comm.
   rewrite fold_series_const.
   do 2 rewrite series_shift_0.
   rewrite series_stretch_const.
   do 2 rewrite Z.sub_0_r.
   apply mkps_morphism; auto.
    unfold series_stretch.
    constructor; intros i; simpl.
    remember (nth_γ b pol₂ ns₂) as γb eqn:Hγb .
    subst polb₂.
    rename H₁ into Hpolb₂.
    destruct (zerop (i mod Pos.to_nat (Qden γb))) as [H₁| H₁].
     apply Nat.mod_divides in H₁; auto.
     destruct H₁ as (d, Hd).
     rewrite Nat.mul_comm in Hd.
     rewrite Hd.
     rewrite Nat.div_mul; auto.
     unfold root_series_from_cγ_list.
     rewrite <- Hd.
     destruct (zerop i) as [H₁| H₁].
      subst i.
      apply Nat.eq_mul_0_l in H₁; auto.
      subst d; simpl.
      destruct (ps_zerop R (ps_poly_nth 0 polb)); [ contradiction | idtac ].
      symmetry.
      apply nth_c_root; assumption.

      simpl.
      rewrite <- Hcb.
      rewrite Nat.add_comm in Hpolb₂; simpl in Hpolb₂.
      remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
      remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
      remember (List.hd phony_ns (newton_segments pol₃)) as ns₃ eqn:Hns₃ .
      remember (next_pol polb (β nsb) (γ nsb) cb) as polb' eqn:Hpolb' .
      remember (List.hd phony_ns (newton_segments polb')) as nsb'.
      rename Heqnsb' into Hnsb'.
      destruct d.
       rewrite Hd in H₁.
       exfalso; revert H₁; apply Nat.lt_irrefl.

       destruct (ps_zerop R (ps_poly_nth 0 polb)); auto; simpl.
       erewrite nth_pol_n with (c₁ := c₂) in Hpolb'; eauto .
       rewrite <- Hpolb' in Hpolb₂.
       destruct (ps_zerop R (ps_poly_nth 0 polb')) as [H₃| H₃]; auto.
       contradiction.

     destruct (zerop i); [ subst i | reflexivity ].
     rewrite Nat.mod_0_l in H₁; auto.
     exfalso; revert H₁; apply Nat.lt_irrefl.

    erewrite nth_γ_n; eauto ; simpl.
    rewrite Hαkb; simpl.
    rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
    rewrite Pos2Z.inj_mul, Z.mul_assoc.
    symmetry.
    rewrite Z.mul_shuffle0.
    apply Z.mul_cancel_r; auto.
    rewrite Z_div_mul_swap; [ rewrite Z.div_mul; auto | idtac ].
    eapply den_αj_divides_num_αj_m; eauto .
    eapply lap_forall_nth with (ns := ns₁); eauto .
     rewrite Heqm₁.
     eapply q_eq_1 with (ns := ns); eauto .
     rewrite <- Heqm₁; assumption.

     simpl; rewrite <- Hc₁, <- Hpol₂, <- Hns₂; assumption.

   assert (1 ≤ S b)%nat as H by fast_omega .
   apply Hpsi in H; simpl in H.
   rewrite <- Hc₁, <- Hpol₂ in H.
   rename H into Hps₂.
   remember Hns₂ as H; clear HeqH.
   eapply r_1_next_ns with (pol := pol₁) in H; eauto .
   destruct H as (αj₂, (αk₂, H)).
   destruct H as (Hoth₂, (Hini₂, (Hfin₂, (Hαj₂, Hαk₂)))).
   unfold γ_sum; simpl.
   rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
   unfold summation; simpl.
   rewrite Nat.add_0_r, rng_add_0_r.
   rewrite Nat.add_comm; simpl.
   rewrite Nat.add_comm in Hpolb₂; simpl in Hpolb₂.
   remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
   remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
   remember (List.hd phony_ns (newton_segments pol₃)) as ns₃ eqn:Hns₃ .
   remember (nth_ns b pol₃ ns₃) as nsb₂ eqn:Hnsb₂ .
   remember Hns₃ as H; clear HeqH.
   eapply nth_ns_n with (c := c₂) in H; eauto .
   rewrite <- Hnsb₂ in H.
   erewrite nth_pol_n with (c₁ := c₂) in H; eauto .
   rewrite <- Hpolb₂ in H.
   rename H into Hbns₂.
   remember Hbns₂ as H; clear HeqH.
   erewrite <- nth_pol_n with (c₁ := c₂) in Hpolb₂; eauto .
   eapply r_1_next_ns in H; eauto .
   destruct H as (αjb₂, (αkb₂, H)).
   destruct H as (Hothb₂, (Hinib₂, (Hfinb₂, (Hαjb₂, Hαkb₂)))).
   unfold root_from_cγ_list; simpl.
   rewrite Hinib, Hfinb, Hinib₂, Hfinb₂; simpl.
   rewrite Hαkb, Hαkb₂; simpl.
   do 2 rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
   do 2 rewrite Pos2Z.inj_mul.
   rewrite Z.mul_shuffle0, Z.div_mul_cancel_r; auto.
   rewrite Z.mul_shuffle0, Z.div_mul_cancel_r; auto.
   unfold ps_add, ps_mul; simpl.
   unfold cm; simpl.
   rewrite fold_series_const.
   unfold ps_terms_add; simpl.
   rewrite fold_series_const.
   unfold ps_ordnum_add; simpl.
   remember (nth_γ b pol₂ ns₂) as γb₂ eqn:Hγb₂ .
   erewrite nth_γ_n in Hγb₂; eauto .
   unfold Qdiv in Hγb₂; simpl in Hγb₂.
   unfold Qmult in Hγb₂; simpl in Hγb₂.
   rewrite Hαkb in Hγb₂; simpl in Hγb₂.
   rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r in Hγb₂.
   subst γb₂; simpl.
   remember (Qden αjb * Qden αkb)%positive as dd.
   remember (Qnum αjb * ' Qden αkb)%Z as nd.
   rewrite Pos.mul_assoc.
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
    apply mkps_morphism; [ idtac | idtac | apply Pos.mul_comm ].
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
      rename H₁ into Hpsb₂.
      destruct (zerop i) as [H₁| H₁].
       subst i; simpl.
       remember (Qnum αjb₂ * ' m₁ / ' Qden αjb₂)%Z as d.
       destruct (lt_dec 0 (Z.to_nat d)) as [H₁| H₁].
        rewrite rng_add_0_r.
        unfold root_series_from_cγ_list; simpl.
        destruct (ps_zerop R (ps_poly_nth 0 polb)) as [H₃| H₃].
         contradiction.

         clear H₃; symmetry.
         apply nth_c_root; auto.

        exfalso; apply H₁.
        subst d.
        remember Hbns₂ as Hbns₂₁; clear HeqHbns₂₁.
        eapply hd_newton_segments in Hbns₂₁; eauto .
        eapply num_m_den_is_pos with (pol := polb₂); eauto .
        assert (q_of_m m₁ (γ nsb) = 1%positive) as Hqb.
         remember Hnsb as Hnsb'; clear HeqHnsb'.
         erewrite nth_ns_n with (c := c₁) in Hnsb'; eauto .
         erewrite nth_pol_n with (c₁ := c₁) in Hnsb'; eauto .
         rewrite <- Hpolb in Hnsb'.
         rewrite Heqm₁.
         eapply q_eq_1_nth with (ns := ns); eauto .
          eapply next_pol_in_K_1_mq with (pol := pol); eauto .

          simpl; rewrite <- Hc₁, <- Hpol₂, <- Hns₂; assumption.

         replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
         eapply next_pol_in_K_1_mq with (pol := polb); eauto .
         eapply lap_forall_nth with (ns := ns₁); eauto .
          replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
          eapply q_eq_1 with (ns := ns); eauto .
           rewrite Heqm₁.
           apply ps_lap_forall_forall.
            intros p₁ p₂ H₁₂ Hmq.
            rewrite <- H₁₂; assumption.

            intros a Hain.
            apply in_K_1_m_lap_mul_r_compat.
            revert a Hain.
            apply ps_lap_forall_forall; auto.
            intros p₁ p₂ H₁₂ Hmq.
            rewrite <- H₁₂; assumption.

           rewrite Pos.mul_1_r; assumption.

          simpl; rewrite <- Hc₁, <- Hpol₂, <- Hns₂; assumption.

       rewrite rng_add_0_l.
       remember (Qnum αjb₂ * ' m₁ / ' Qden αjb₂)%Z as d.
       destruct (lt_dec i (Z.to_nat d)) as [H₂| H₂].
        unfold root_series_from_cγ_list; simpl.
        rewrite <- Hcb, <- Hpolb₂, <- Hbns₂.
        destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
        clear H₁.
        destruct (ps_zerop R (ps_poly_nth 0 polb)) as [| H₁]; auto.
        simpl.
        destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [| H₃]; auto.
        unfold next_pow at 1; simpl.
        rewrite Hinib₂, Hfinb₂; simpl.
        rewrite Hαkb₂; simpl.
        rewrite Z.add_0_r, Z.mul_1_r.
        do 2 rewrite Pos.mul_1_r.
        rewrite Pos2Z.inj_mul.
        rewrite Z.mul_shuffle0, Z.div_mul_cancel_r; auto.
        rewrite <- Heqd.
        remember (Nat.compare (Z.to_nat d) (S i)) as cmp₁ eqn:Hcmp₁ .
        symmetry in Hcmp₁.
        destruct cmp₁; auto.
         apply nat_compare_eq in Hcmp₁.
         rewrite Hcmp₁ in H₂.
         exfalso; revert H₂; apply Nat.lt_irrefl.

         apply nat_compare_lt in Hcmp₁.
         exfalso; fast_omega H₂ Hcmp₁.

        apply Nat.nlt_ge in H₂.
        remember (i - Z.to_nat d)%nat as id.
        unfold root_series_from_cγ_list.
        remember (S id) as sid; simpl.
        rewrite <- Hcb, <- Hpolb₂, <- Hbns₂.
        destruct i; [ exfalso; revert H₁; apply Nat.lt_irrefl | idtac ].
        clear H₁.
        destruct (ps_zerop R (ps_poly_nth 0 polb)) as [H₁| H₁].
         contradiction.

         clear H₁.
         remember (S i) as si.
         unfold next_pow; simpl.
         rewrite Hinib₂, Hfinb₂; simpl.
         rewrite Hαkb₂; simpl.
         rewrite Z.add_0_r, Z.mul_1_r.
         do 2 rewrite Pos.mul_1_r.
         rewrite Pos2Z.inj_mul.
         rewrite Z.mul_shuffle0, Z.div_mul_cancel_r; auto.
         rewrite <- Heqd.
         subst sid si; simpl.
         destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [| H₁]; auto.
         clear H₁.
         remember (Nat.compare (Z.to_nat d) (S i)) as cmp₁ eqn:Hcmp₁ .
         symmetry in Hcmp₁.
         destruct cmp₁.
          apply nat_compare_eq in Hcmp₁.
          rewrite Hcmp₁, Nat.sub_diag in Heqid; subst id; reflexivity.

          assert (ps_lap_forall (λ a, in_K_1_m a m₁) (al polb₂)) as HKb₂.
           eapply lap_forall_nth with (ns := ns₂) (n := S b); eauto .
            eapply hd_newton_segments; eauto .

            eapply multiplicity_1_remains with (ns := ns₁); eauto .

            replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
            eapply q_eq_1 with (ns := ns₁); eauto .
            rewrite Pos.mul_1_r; assumption.

            intros j Hj.
            destruct (eq_nat_dec j (S b)) as [H₁| H₁].
             subst j; simpl.
             rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
             erewrite <- nth_pol_n with (c₁ := c₂) (poln := polb); eauto .
             rewrite <- Hpolb₂; assumption.

             apply le_neq_lt in Hj; eauto .
             apply Nat.succ_le_mono in Hj.
             apply Nat.succ_le_mono in Hj.
             apply Hpsi in Hj.
             simpl in Hj.
             rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hj.
             assumption.

            simpl.
            rewrite <- Hc₂, <- Hpol₃, <- Hns₃.
            erewrite <- nth_pol_n with (c₁ := c₂); eauto .

           apply nat_compare_lt in Hcmp₁.
           destruct id; [ exfalso; fast_omega Heqid Hcmp₁ | idtac ].
           remember (ac_root (Φq polb₂ nsb₂)) as cb₂ eqn:Hcb₂ .
           remember (next_pol polb₂ (β nsb₂) (γ nsb₂) cb₂) as polb₃.
           remember (List.hd phony_ns (newton_segments polb₃)) as nsb₃.
           rewrite <- Nat.add_1_r.
           rewrite
            find_coeff_step
             with (ns := nsb₂) (pol := polb₂) (p := Z.to_nat d) (dp := O);
            eauto .
            rewrite <- Heqid; symmetry.
            rewrite <- find_coeff_add with (dp := Z.to_nat d).
            rewrite Heqid.
            rewrite Nat.sub_add; auto.
            rewrite Nat.add_comm, Nat.add_1_r.
            unfold next_pow.
            rewrite Nat.add_0_l; reflexivity.

            eapply hd_newton_segments; eauto .

            replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
            eapply q_eq_1 with (ns := nsb); eauto .
             eapply lap_forall_nth with (ns := ns₁); eauto .
              rewrite Heqm₁.
              eapply q_eq_1 with (ns := ns); eauto .
              rewrite <- Heqm₁; assumption.

              simpl.
              rewrite <- Hc₁, <- Hpol₂, <- Hns₂; assumption.

             rewrite Pos.mul_1_r; assumption.

            eapply multiplicity_1_remains with (ns := nsb); eauto .

            split; [ idtac | fast_omega Hcmp₁ ].
            rewrite Heqd.
            eapply num_m_den_is_pos with (ns := nsb₂) (pol := polb₂); eauto .
            eapply hd_newton_segments; eauto .

            rewrite Nat.add_0_r; reflexivity.

          apply nat_compare_gt in Hcmp₁.
          apply Nat.nle_gt in Hcmp₁.
          contradiction.

      apply Z.opp_nonpos_nonneg.
      apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
      apply Z.mul_nonneg_nonneg; auto.
      apply Z.lt_le_incl; assumption.

     rewrite Pos2Z.inj_mul, Z.mul_assoc.
     apply Z.mul_cancel_r; auto.
     subst dd nd.
     rewrite Pos2Z.inj_mul, Z.mul_assoc.
     symmetry; rewrite Z.mul_shuffle0.
     apply Z.mul_cancel_r; auto.
     symmetry.
     rewrite Z.mul_comm.
     rewrite <- Z.divide_div_mul_exact; auto.
      rewrite Z.mul_comm.
      rewrite Z.div_mul; auto.

      eapply den_αj_divides_num_αj_m; eauto .
      remember Hm as H; clear HeqH.
      eapply next_pol_in_K_1_mq in H; eauto .
      rewrite <- Heqm₁ in H.
      eapply lap_forall_nth with (ns := ns₁); eauto .
       rewrite Heqm₁.
       eapply q_eq_1 with (ns := ns); eauto .
       rewrite <- Heqm₁; assumption.

       simpl; rewrite <- Hc₁, <- Hpol₂, <- Hns₂; assumption.

    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
    apply Z.mul_nonneg_nonneg; auto.
    apply Z.lt_le_incl; assumption.
Qed.

Lemma fold_γ_sum : ∀ b n pol ns,
  let qr := Q_ring in
  Σ (i = 0, n), nth_γ (b + i) pol ns = γ_sum b n pol ns.
Proof. reflexivity. Qed.

Lemma r_1_nth_ns : ∀ pol ns c pol₁ ns₁,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ∀ n poln nsn,
    (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
    → poln = nth_pol n pol₁ ns₁
    → nsn = nth_ns n pol₁ ns₁
    → ∃ αj αk,
      oth_pts nsn = [] ∧
      ini_pt nsn = (Qnat 0, αj) ∧
      fin_pt nsn = (Qnat 1, αk) ∧
      (0 < Qnum αj)%Z ∧
      Qnum αk = 0%Z.
Proof.
intros pol ns c pol₁ ns₁ Hns Hc Hr Hpol₁ Hns₁.
intros n poln nsn Hpsi Hpoln Hnsn.
revert poln nsn Hpsi Hpoln Hnsn.
revert pol ns c pol₁ ns₁ Hns Hc Hr Hpol₁ Hns₁.
induction n; intros.
 pose proof (Hpsi O (Nat.le_0_l O)) as H; simpl in H.
 rename H into Hnz₁.
 simpl in Hpoln, Hnsn; subst poln nsn.
 remember Hns as H; clear HeqH.
 eapply r_1_next_ns in H; eauto .

 pose proof (Hpsi O (Nat.le_0_l (S n))) as H; simpl in H.
 rename H into Hnz₁.
 remember Hns as H; clear HeqH.
 eapply r_1_next_ns with (ns₁ := ns₁) in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (_, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
 remember Hns₁ as H; clear HeqH.
 eapply hd_newton_segments in H; eauto .
 rename H into Hns₁i.
 remember Hr as H; clear HeqH.
 eapply multiplicity_1_remains in H; eauto .
 rename H into Hr₁.
 simpl in Hpoln, Hnsn.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 eapply IHn with (ns := ns₁); eauto .
 intros i Hin.
 apply Nat.succ_le_mono in Hin.
 apply Hpsi in Hin; simpl in Hin.
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
 assumption.
Qed.

Lemma rrr : ∀ pol ns pol₁ ns₁ c m q₀ n,
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
intros pol ns pol₁ ns₁ c m q₀ n Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ Hpsi.
remember (m * q₀)%positive as m₁.
unfold root_tail, ps_monom; simpl.
rewrite fold_series_const.
rewrite fold_series_const.
remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
remember (nth_pol n pol₁ ns₁) as poln₁ eqn:Hpoln₁ .
remember (nth_pol n pol₂ ns₂) as poln₂ eqn:Hpoln₂ .
destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₁| H₁].
 pose proof (Hpsi n (Nat.le_refl n)) as H; simpl in H.
 subst poln₁; contradiction.

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
 destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
  rewrite ps_mul_0_r, ps_add_0_r.
  unfold root_from_cγ_list; simpl.
  remember (nth_ns n pol₁ ns₁) as nsn₁ eqn:Hnsn₁ .
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
      unfold root_series_from_cγ_list; simpl.
      destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₃| H₃].
       contradiction.

       symmetry.
       apply nth_c_root; auto.

      unfold root_series_from_cγ_list; simpl.
      destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [| H₄]; auto.
      clear H₄.
      destruct d.
       exfalso; subst i; revert H₃; apply Nat.lt_irrefl.

       remember (ac_root (Φq poln₁ nsn₁)) as cn₁ eqn:Hcn₁ .
       remember (next_pol poln₁ (β nsn₁) (γ nsn₁) cn₁) as poln₁s eqn:Hpoln₁s .
       erewrite nth_pol_n with (ns₁ := ns₁) in Hpoln₁s; eauto .
       rewrite <- Hpoln₂ in Hpoln₁s; subst poln₁s.
       remember (List.hd phony_ns (newton_segments poln₂)) as nsn₂ eqn:Hnsn₂ .
       simpl.
       destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₄| H₄]; auto.
       contradiction.

     destruct (zerop i) as [H₄| H₄]; auto.
     subst i; rewrite Nat.mod_0_l in H₃; auto.
     exfalso; revert H₃; apply Nat.lt_irrefl.

    apply Pos.mul_comm; reflexivity.
bbb.

Lemma sss : ∀ pol ns pol₁ ns₁ c m q₀ b,
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
remember (m * q₀)%positive as m₁.
revert pol ns pol₁ ns₁ Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ Hpsi.
revert b c m q₀ m₁ Heqm₁.
induction n; intros.
 rewrite Nat.add_0_r in Hpsi; subst m₁.
 eapply root_tail_from_0; eauto .

 rewrite IHn; eauto ; [ idtac | intros i H; apply Hpsi; fast_omega H ].
 unfold root_head.
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
  rewrite <- ps_mul_assoc.
  rewrite <- ps_mul_add_distr_l.
  apply ps_mul_compat_l.
  symmetry.
  do 3 rewrite Nat.add_succ_r.
  remember (S (b + n)) as bn.
  rewrite ps_mul_comm.
  rewrite <- ps_monom_split_mul.
  remember (nth_c bn pol₁ ns₁) as cbn eqn:Hcbn .
  remember (nth_γ bn pol₁ ns₁) as γbn eqn:Hγbn .
bbb.

(* mmm... faut voir... *)
Lemma uuu₂ : ∀ pol ns n,
  ns ∈ newton_segments pol
  → (root_head n pol ns +
       ps_monom 1%K (γ_sum n pol ns) * root_tail n pol ns =
     root_head (S n) pol ns +
       ps_monom 1%K (γ_sum (S n) pol ns) * root_tail (S n) pol ns)%ps.
Proof.
intros pol ns n Hns.
revert pol ns Hns.
induction n; intros.
 unfold root_head, root_tail; simpl.
 unfold summation; simpl.
 do 2 rewrite ps_add_0_r.
 remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
 remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 rewrite <- rng_add_assoc; simpl.
 apply rng_add_compat_l.
 unfold γ_sum; simpl.
 unfold summation; simpl.
 rewrite rng_add_0_r.
 rewrite rng_add_0_r.
 rewrite <- Hc₁, <- Hpol₁, <- Hns₁.
 remember (ac_root (Φq pol₁ ns₁)) as c₂ eqn:Hc₂ .
 apply ttt with (n := 0%nat) in Hns.
 simpl in Hns.
 rewrite <- Hc₁, <- Hpol₁, <- Hns₁ in Hns.
 rewrite <- Hc₂ in Hns.
 unfold root_tail in Hns.
 simpl in Hns.
 rewrite <- Hc₁, <- Hpol₁, <- Hns₁ in Hns.
bbb.

Lemma uuu : ∀ pol ns n,
  let qr := Q_ring in
  (root_head (S n) pol ns =
   root_head n pol ns +
   ps_monom (nth_c n pol ns) (Σ (i = 0, n), nth_γ i pol ns))%ps.
Proof.
intros pol ns n qr.
revert pol ns.
induction n; intros.
 simpl.
 unfold summation; simpl.
 rewrite ps_mul_0_r, ps_add_0_r, ps_add_0_l, rng_add_0_r.
 reflexivity.

 remember (S n) as n₁; simpl; subst n₁.
 remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
 remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
bbb.

Lemma vvv : ∀ pol ns n,
  (root_when_r_1 pol ns =
   root_head n pol ns +
   root_when_r_1 (nth_pol n pol ns) (nth_ns n pol ns))%ps.
Proof.
intros pol ns n.
revert pol ns.
induction n; intros; [ rewrite ps_add_0_l; reflexivity | idtac ].
bbb.
destruct n.
 simpl.
 remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
 remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 rewrite ps_mul_0_r, ps_add_0_r.
bbb.

intros pol ns n.
revert pol ns.
induction n; intros; [ rewrite ps_add_0_l; reflexivity | idtac ].
remember (root_head (S n)) as x; simpl; subst x.
remember (next_pol pol (β ns) (γ ns) (ac_root (Φq pol ns))) as pol₁.
rename Heqpol₁ into Hpol₁.
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
bbb.

(*
Fixpoint ps_poly_root m pol ns :=
  match m with
  | 0%nat => None
  | S m₁ =>
      let c := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c in
      if ps_zerop R (List.hd ps_zero (al pol₁)) then
        Some (ps_monom c (γ ns))
      else
        let ns₁ := List.hd phony_ns (newton_segments pol₁) in
        let r := root_multiplicity acf c (Φq pol ns) in
        if eq_nat_dec r 1 then Some (root_when_r_1 pol ns)
        else if infinite_with_same_r r pol₁ ns₁ then ...
        else
          match ps_poly_root m₁ pol₁ ns₁ with
          | None => None
          | Some y => Some (ps_monom c (γ ns) + ps_monom 1%K (γ ns) * y)%ps
          end
  end.
*)

(*
Lemma yyy₁ : ∀ pol ns m ps,
  ns = List.hd phony_ns (newton_segments pol)
  → ps_poly_root m pol ns = Some ps
  → (ps_pol_apply pol ps = 0)%ps.
Proof.
intros pol ns m ps Hns Hps.
revert pol ns ps Hns Hps.
induction m; intros; [ discriminate Hps | simpl in Hps ].
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (ps_poly_root m pol₁ ns₁) as pso eqn:Hpso .
symmetry in Hpso.
unfold next_pol in Hpol₁.
remember (next_lap (al pol) (β ns) (γ ns) c) as la₁ eqn:Hla₁ .
destruct (ps_zerop R (List.hd 0%ps la₁)) as [Hz| Hnz].
 injection Hps; clear Hps; intros Hps.
 rewrite <- Hps; simpl.
 eapply f₁_root_f_root with (y₁ := 0%ps).
  unfold next_pol.
  rewrite Hla₁ in Hpol₁.
  eassumption.

  rewrite ps_mul_0_r, ps_add_0_r; reflexivity.

  unfold ps_pol_apply; simpl.
  unfold apply_poly; simpl.
  rewrite Hpol₁; simpl.
  destruct la₁ as [| a]; [ reflexivity | simpl ].
  simpl in Hz.
  rewrite Hz, ps_mul_0_r, ps_add_0_r; reflexivity.

 destruct pso as [ps₁| ]; [ idtac | discriminate Hps ].
 injection Hps; clear Hps; intros Hps.
 apply IHm in Hpso; [ idtac | assumption ].
 symmetry in Hps.
 subst la₁.
 eapply f₁_root_f_root; try eassumption.
 rewrite Hps; reflexivity.
Qed.
*)

(*
Lemma yyy : ∀ pol ns m ps,
  degree (ps_zerop R) pol ≥ 1
  → ns ∈ newton_segments pol
  → ps_poly_root m pol ns = Some ps
  → (ps_pol_apply pol ps = 0)%ps.
Proof.
intros pol ns m ps Hdeg Hns Hps.
revert pol ns ps Hdeg Hns Hps.
induction m; intros; [ discriminate Hps | simpl in Hps ].
remember (ac_root (Φq pol ns)) as c eqn:Hc .
remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
remember (ps_poly_root m pol₁ ns₁) as pso eqn:Hpso .
symmetry in Hpso.
unfold next_pol in Hpol₁.
remember (next_lap (al pol) (β ns) (γ ns) c) as la₁ eqn:Hla₁ .
destruct (ps_zerop R (List.hd 0%ps la₁)) as [Hz| Hnz].
 injection Hps; clear Hps; intros Hps.
 rewrite <- Hps; simpl.
 eapply f₁_root_f_root with (y₁ := 0%ps).
  unfold next_pol.
  rewrite Hla₁ in Hpol₁.
  eassumption.

  rewrite ps_mul_0_r, ps_add_0_r; reflexivity.

  unfold ps_pol_apply; simpl.
  unfold apply_poly; simpl.
  rewrite Hpol₁; simpl.
  destruct la₁ as [| a]; [ reflexivity | simpl ].
  simpl in Hz.
  rewrite Hz, ps_mul_0_r, ps_add_0_r; reflexivity.

 destruct pso as [ps₁| ]; [ idtac | discriminate Hps ].
 injection Hps; clear Hps; intros Hps.
 apply IHm in Hpso.
  symmetry in Hps.
  subst la₁.
  eapply f₁_root_f_root; try eassumption.
  rewrite Hps; reflexivity.
bbb.
*)

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
