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
Require Import PosOrder.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Lemma lap_nth_add : ∀ n la lb,
  (lap_nth n (la + lb) = lap_nth n la + lap_nth n lb)%ps.
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

Lemma lap_nth_x_pow_mul : ∀ la n,
  (lap_nth n ([0; 1 … []] ^ n * la) = lap_nth 0 la)%ps.
Proof.
intros la n.
induction n.
 progress unfold ps_lap_pow; simpl.
 progress unfold ps_lap_mul.
 rewrite lap_mul_1_l.
 reflexivity.

 rewrite <- Nat.add_1_l.
 unfold ps_lap_pow.
 rewrite lap_power_add.
 rewrite lap_power_1.
 progress unfold ps_lap_mul.
 rewrite <- lap_mul_assoc.
 unfold lap_nth.
 rewrite nth_mul_deg_1.
 rewrite rng_mul_0_l.
 rewrite rng_add_0_l.
 assumption.
Qed.

Lemma lap_nth_0_cons_pow : ∀ a la n, (lap_nth 0 ([a … la] ^ n) = a ^ n)%ps.
Proof.
intros a la n.
induction n; simpl.
 progress unfold ps_lap_pow; simpl.
 reflexivity.

 unfold ps_lap_pow; simpl.
 unfold lap_nth.
 rewrite list_nth_lap_mul; simpl.
 unfold summation; simpl.
 rewrite IHn.
 rewrite ps_add_0_r; reflexivity.
Qed.

Lemma eq_1_0_all_0 : (1 = 0)%K → ∀ a, (a = 0)%K.
Proof.
intros H a.
rewrite <- rng_mul_1_l.
rewrite H, rng_mul_0_l.
reflexivity.
Qed.

Lemma order_pow : ∀ a n,
  (a ≠ 0)%ps
  → (order (a ^ n) = qfin (Qnat n) * order a)%Qbar.
Proof.
intros a n Ha.
induction n; simpl.
 remember (order a) as v eqn:Hv .
 symmetry in Hv.
 destruct v as [v| ].
  unfold Qnat; simpl.
  rewrite Qmult_0_l.
  unfold ps_one.
  rewrite ps_monom_order; [ reflexivity | idtac ].
  intros H; apply Ha.
  rewrite <- ps_mul_1_l.
  unfold ps_one.
  rewrite H, ps_zero_monom_eq.
  rewrite ps_mul_0_l.
  reflexivity.

  exfalso; apply Ha.
  apply order_inf; assumption.

 rewrite order_mul; [ idtac | assumption ].
 rewrite IHn.
 remember (order a) as v eqn:Hv .
 symmetry in Hv.
 destruct v as [v| ]; [ simpl | reflexivity ].
 rewrite <- Nat.add_1_l.
 unfold Qnat.
 rewrite Nat2Z.inj_add, QZ_plus.
 rewrite Qmult_plus_distr_l; simpl.
 rewrite Qmult_1_l; reflexivity.
Qed.

Lemma lap_nth_0_apply_0 : ∀ la,
  (lap_nth 0 la = @apply_lap _ (ps_ring R) la 0)%ps.
Proof.
intros la.
induction la as [| a]; [ reflexivity | simpl ].
rewrite ps_mul_0_r, ps_add_0_l.
reflexivity.
Qed.

Lemma apply_lap_inject_K_in_Kx_monom : ∀ P c,
  (@apply_lap _ (ps_ring R) (lap_inject_K_in_Kx P) (ps_monom c 0) =
   ps_monom (apply_lap P c) 0)%ps.
Proof.
intros P c.
unfold apply_lap; simpl.
unfold lap_inject_K_in_Kx.
rename c into d.
rewrite list_fold_right_map.
induction P as [| a]; simpl.
 rewrite ps_zero_monom_eq; reflexivity.

 rewrite IHP.
 rewrite ps_monom_add_l, ps_monom_mul_l.
 reflexivity.
Qed.

Lemma ps_monom_0_coeff_0 : ∀ c, (ps_monom c 0 = 0)%ps → (c = 0)%K.
Proof.
intros c Hc.
apply ps_null_coeff_range_length_inf_iff in Hc.
apply null_coeff_range_length_iff in Hc.
unfold null_coeff_range_length_prop in Hc.
simpl in Hc.
pose proof (Hc O); assumption.
Qed.

Lemma in_power_list_lt : ∀ A la h (hv : puiseux_series A) pow,
  (h, hv) ∈ qpower_list pow la
  → (nofq h < pow + length la)%nat.
Proof.
intros A la h hv pow Hh.
unfold qpower_list in Hh.
unfold pair_rec in Hh; simpl in Hh.
revert pow Hh.
induction la as [| a]; intros; [ contradiction | simpl ].
simpl in Hh.
destruct Hh as [Hh| Hh].
 injection Hh; clear Hh; intros; subst h hv.
 rewrite nofq_Qnat.
 apply Nat.lt_sub_lt_add_l.
 rewrite Nat.sub_diag.
 apply Nat.lt_0_succ.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 apply IHla; assumption.
Qed.

Lemma in_points_of_ps_lap_gen_lt : ∀ la pow pt,
  pt ∈ points_of_ps_lap_gen R pow la
  → (nofq (fst pt) < pow + length la)%nat.
Proof.
intros la pow pt Hpt.
unfold points_of_ps_lap_gen in Hpt.
destruct pt as (h, hv); simpl.
eapply in_pts_in_ppl with (def := 0%ps) in Hpt; try reflexivity.
destruct Hpt as (Hpt, Hord).
eapply in_power_list_lt; eassumption.
Qed.

Lemma in_points_of_ps_lap_lt : ∀ la pt,
  pt ∈ points_of_ps_lap R la
  → (nofq (fst pt) < length la)%nat.
Proof.
intros la pt Hpt.
apply in_points_of_ps_lap_gen_lt in Hpt.
assumption.
Qed.

(* [Walker, p 101] « O(br) = 0 » *)
Theorem order_bbar_r_is_0 : ∀ pol ns c₁ r f₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
    → r = root_multiplicity acf c₁ (Φq pol ns)
      → f₁ = pol₁ pol (β ns) (γ ns) c₁
        → (order (poly_nth r f₁) = 0)%Qbar.
Proof.
intros pol ns c₁ r f₁ Hns (Hc₁, Hc₁nz) Hr Hf₁.
subst f₁.
remember (g_lap_of_ns pol ns) as gg.
remember Heqgg as H; clear HeqH.
unfold g_lap_of_ns in H; subst gg.
rewrite <- Hc₁ in H.
remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl eqn:Hpl .
remember (List.map (term_of_point R pol) pl) as tl eqn:Htl .
remember (List.map (λ t : term α nat, power t) tl) as l₁ eqn:Hl₁ .
remember (list_seq_except 0 (length (al pol)) l₁) as l₂ eqn:Hl₂ .
remember (quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r) as Ψ eqn:HΨ .
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
 assert (order (lap_nth r (g_lap_of_ns pol ns)) > 0)%Qbar as Hog.
  destruct (lt_dec r (length (g_lap_of_ns pol ns))) as [Hlt| Hge].
   eapply each_power_of_y₁_in_g_has_coeff_pos_ord; try eassumption.
    reflexivity.

    unfold g_of_ns; simpl.
    unfold lap_nth.
    apply list_nth_in; assumption.

   apply Nat.nlt_ge in Hge.
   unfold lap_nth.
   rewrite List.nth_overflow; [ idtac | assumption ].
   rewrite order_0; constructor.

  rewrite fold_ps_lap_comp.
  do 2 rewrite fold_ps_lap_mul.
  do 2 rewrite fold_ps_lap_pow.
  remember ([0%ps; 1%ps … []] ^ r)%pslap as yr.
  remember ([ps_monom c₁ 0; 1%ps … []] ^ j)%pslap as ycj.
  remember (lap_inject_K_in_Kx (al Ψ)) as psy.
  remember [ps_monom c₁ 0; 1%ps … []] as yc.
  assert (order (lap_nth r (yr * ycj * psy ∘ yc)) = 0)%Qbar as Hor.
   subst yr ycj psy yc.
   progress unfold ps_lap_mul.
   rewrite <- lap_mul_assoc.
   do 2 rewrite fold_ps_lap_mul.
   erewrite lap_nth_x_pow_mul.
   progress unfold ps_lap_mul.
   progress unfold lap_mul.
   progress unfold lap_nth; simpl.
   rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
   unfold summation; simpl.
   rewrite ps_add_0_r.
   rewrite order_mul; [ idtac | assumption ].
   rewrite fold_lap_nth.
   rewrite lap_nth_0_cons_pow.
   rewrite order_pow.
    rewrite ps_monom_order; [ idtac | assumption ].
    rewrite Qbar.mul_0_r; [ idtac | intros H; discriminate H ].
    rewrite Qbar.add_0_l.
    rewrite fold_lap_nth.
    rewrite lap_nth_0_apply_0.
    unfold ps_lap_comp.
    rewrite apply_lap_compose.
    unfold apply_lap at 2; simpl.
    rewrite ps_mul_0_l, ps_add_0_l.
    rewrite ps_mul_0_r, ps_add_0_l.
    rewrite apply_lap_inject_K_in_Kx_monom.
    rewrite ps_monom_order; [ reflexivity | idtac ].
    eapply psy_c₁_ne_0 in HΨ; eassumption.

    intros H; apply Hc₁nz.
    apply ps_monom_0_coeff_0; assumption.

   rewrite order_neq_min.
    rewrite Hor.
    rewrite Qbar.min_l; [ reflexivity | idtac ].
    apply Qbar.lt_le_incl.
    remember (g_of_ns pol ns) as g eqn:Hg .
    destruct (lt_dec r (length (g_lap_of_ns pol ns))) as [Hlt| Hge].
     eapply each_power_of_y₁_in_g_has_coeff_pos_ord; try eassumption.
     rewrite Hg.
     unfold g_of_ns; simpl.
     unfold lap_nth.
     apply list_nth_in; assumption.

     apply Nat.nlt_ge in Hge.
     unfold lap_nth.
     rewrite List.nth_overflow; [ idtac | assumption ].
     rewrite order_0; constructor.

    rewrite Hor.
    apply Qbar.lt_neq.
    remember (g_of_ns pol ns) as g eqn:Hg .
    destruct (lt_dec r (length (g_lap_of_ns pol ns))) as [Hlt| Hge].
     eapply each_power_of_y₁_in_g_has_coeff_pos_ord; try eassumption.
     rewrite Hg.
     unfold g_of_ns; simpl.
     unfold lap_nth.
     apply list_nth_in; assumption.

     apply Nat.nlt_ge in Hge.
     unfold lap_nth.
     rewrite List.nth_overflow; [ idtac | assumption ].
     rewrite order_0; constructor.

 apply except_split_seq; [ idtac | idtac | assumption ].
  rewrite Hl₁, Htl, Hpl.
  do 2 apply Sorted_map; simpl.
  apply Sorted_fst_lt_nofq_fst.
   intros a Ha.
   remember (points_of_ps_polynom R pol) as pts.
   symmetry in Heqpts.
   eapply pt_absc_is_nat; [ eassumption | idtac ].
   eapply ns_in_init_pts; [ idtac | eassumption ].
   rewrite <- Heqpts; assumption.

   eapply ini_oth_fin_pts_sorted; eassumption.

  simpl.
  rewrite Hl₁.
  apply List.Forall_forall; intros i Hi.
  split; [ apply Nat.le_0_l | idtac ].
  apply List.in_map_iff in Hi.
  destruct Hi as (x, (Hxi, Hx)).
  subst i.
  rewrite Htl in Hx.
  apply List.in_map_iff in Hx.
  destruct Hx as (y, (Hi, Hy)).
  subst x; simpl.
  rename y into pt.
  rewrite Hpl in Hy.
  eapply ns_in_init_pts in Hy; [ idtac | eassumption ].
  unfold points_of_ps_polynom in Hy.
  apply in_points_of_ps_lap_lt; assumption.
Qed.

(* [Walker, p 101] « O(bi) ≥ 0,  i = 0,..., n » *)
Theorem yyy : ∀ pol ns c₁ r f₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
    → r = root_multiplicity acf c₁ (Φq pol ns)
      → f₁ = pol₁ pol (β ns) (γ ns) c₁
        → ∀ i, (order (poly_nth i f₁) ≥ 0)%Qbar.
Proof.
intros pol ns c₁ r f₁ Hns (Hc₁, Hc₁nz) Hr Hf₁ i.
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
  ns ∈ newton_segments pol
  → ini_pt ns = (Qnat j, αj)
    → fin_pt ns = (Qnat k, αk)
      → c₁ = ac_root (Φq pol ns)
        → r = root_multiplicity acf c₁ (Φq pol ns)
          → Ψ = quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r
            → f₁ = pol₁ pol (β ns) (γ ns) c₁
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
  → c₁ = ac_root (Φq pol ns)
    → f₁ = pol₁ pol (β ns) (γ ns) c₁
      → ∀ i, (order (poly_nth i f₁) ≥ 0)%Qbar.
Proof.
intros pol ns c₁ f₁ Hns Hc₁ Hf₁ i.
bbb.

End theorems.
