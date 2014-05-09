(* puiseux.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.
Require Import Sorted.

Require Import Misc.
Require Import Qbar.
Require Import SplitList.
Require Import Field.
Require Import Fpolynomial.
Require Import Fsummation.
Require Import Newton.
Require Import ConvexHullMisc.
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

Lemma lap_nth_x_le_pow_mul : ∀ la m n,
  (n ≤ m)%nat
  → (lap_nth m ([0; 1 … []] ^ n * la) = lap_nth (m - n) la)%ps.
Proof.
intros la m n Hnm.
revert m Hnm.
induction n; intros.
 progress unfold ps_lap_pow; simpl.
 progress unfold ps_lap_mul.
 rewrite lap_mul_1_l.
 rewrite Nat.sub_0_r.
 reflexivity.

 rewrite <- Nat.add_1_l.
 unfold ps_lap_pow.
 rewrite lap_power_add.
 rewrite lap_power_1.
 progress unfold ps_lap_mul.
 rewrite <- lap_mul_assoc.
 rewrite lap_mul_cons_l.
 rewrite lap_eq_0, lap_mul_nil_l, lap_add_nil_l, lap_mul_1_l.
 destruct m; [ exfalso; revert Hnm; apply Nat.nlt_0_r | simpl ].
 apply le_S_n in Hnm.
 apply IHn; assumption.
Qed.

Lemma lap_nth_x_gt_pow_mul : ∀ la m n,
  (m < n)%nat
  → (lap_nth m ([0; 1 … []] ^ n * la) = 0)%ps.
Proof.
intros la m n Hmn.
revert m Hmn.
induction n; intros.
 exfalso; revert Hmn; apply Nat.nlt_0_r.

 unfold ps_lap_mul, ps_lap_pow; simpl.
 rewrite <- lap_mul_assoc.
 rewrite lap_mul_cons_l.
 rewrite lap_eq_0, lap_mul_nil_l, lap_add_nil_l, lap_mul_1_l.
 destruct m; [ reflexivity | idtac ].
 apply lt_S_n in Hmn.
 unfold lap_nth; simpl.
 apply IHn; assumption.
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

Lemma f₁_eq_term_with_Ψ_plus_g : ∀ pol ns j αj c₁ r f₁ Ψ,
  ns ∈ newton_segments pol
  → ini_pt ns = (Qnat j, αj)
    → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
      → r = root_multiplicity acf c₁ (Φq pol ns)
        → Ψ = quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r
          → f₁ = pol₁ pol (β ns) (γ ns) c₁
            → (f₁ =
               POL [0%ps; 1%ps … []] ^ r *
               POL [ps_monom c₁ 0; 1%ps … []] ^ j *
               POL (lap_inject_K_in_Kx (al Ψ)) ∘
               POL [ps_monom c₁ 0; 1%ps … []] +
               g_of_ns pol ns)%pspol.
Proof.
intros pol ns j αj c₁ r f₁ Ψ Hns Hini (Hc₁, Hc₁nz) Hr HΨ Hf₁.
subst f₁.
remember (g_lap_of_ns pol ns) as gg.
remember Heqgg as H; clear HeqH.
unfold g_lap_of_ns in H; subst gg.
rewrite <- Hc₁ in H.
remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl eqn:Hpl .
remember (List.map (term_of_point R pol) pl) as tl eqn:Htl .
remember (List.map (λ t : term α nat, power t) tl) as l₁ eqn:Hl₁ .
remember (list_seq_except 0 (length (al pol)) l₁) as l₂ eqn:Hl₂ .
symmetry in Hc₁.
rewrite f₁_eq_term_with_Ψ_plus_sum with (l₂ := l₂); try eassumption.
 rewrite ps_poly_lap_summ; [ idtac | intros i; simpl; apply lap_eq_refl ].
 rewrite ps_poly_lap_summ; [ simpl | intros i; simpl; apply lap_eq_refl ].
 unfold ps_pol_add, poly_add; simpl.
 unfold ps_lap_add in H; simpl in H.
 unfold ps_lap_mul in H; simpl in H.
 progress unfold ps_lap_pow in H.
 simpl in H; rewrite <- H; clear H.
 reflexivity.

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

Lemma nth_g_order_pos : ∀ pol ns h,
  ns ∈ newton_segments pol
  → (order (lap_nth h (g_lap_of_ns pol ns)) > 0)%Qbar.
Proof.
intros pol ns h Hns.
destruct (lt_dec h (length (g_lap_of_ns pol ns))) as [Hlt| Hge].
 eapply each_power_of_y₁_in_g_has_coeff_pos_ord; try eassumption.
  reflexivity.

  unfold g_of_ns; simpl.
  unfold lap_nth.
  apply list_nth_in; assumption.

 apply Nat.nlt_ge in Hge.
 unfold lap_nth.
 rewrite List.nth_overflow; [ idtac | assumption ].
 rewrite order_0; constructor.
Qed.

Lemma xxx : ∀ pol ns j αj c₁ r Ψ yr ycj psy yc,
  ns ∈ newton_segments pol
  → ini_pt ns = (Qnat j, αj)
    → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
      → r = root_multiplicity acf c₁ (Φq pol ns)
        → Ψ = quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r
          → yr = ([0%ps; 1%ps … []] ^ r)%pslap
            → ycj = ([ps_monom c₁ 0; 1%ps … []] ^ j)%pslap
              → psy = lap_inject_K_in_Kx (al Ψ)
                → yc = [ps_monom c₁ 0; 1%ps … []]
                  → ∀ i, (i < r)%nat
                    → (order (lap_nth i (yr * ycj * psy ∘ yc)) > 0)%Qbar.
Proof.
intros pol ns j αj c₁ r Ψ yr ycj psy yc.
intros Hns Hini Hc₁ Hr HΨ Hyr Hycj Hpsy Hyc i Hir.
subst yr ycj psy yc.
progress unfold ps_lap_mul.
rewrite <- lap_mul_assoc.
do 2 rewrite fold_ps_lap_mul.
rewrite lap_nth_x_gt_pow_mul; [ idtac | assumption ].
rewrite order_0; constructor.
Qed.

Lemma order_nth_inject_K : ∀ la i,
  (0 ≤ order (lap_nth i (lap_inject_K_in_Kx la)))%Qbar.
Proof.
intros la i.
revert i.
induction la as [| a]; intros; simpl.
 unfold lap_nth.
 rewrite list_nth_nil.
 rewrite order_0; constructor.

 destruct i; [ idtac | apply IHla ].
 unfold lap_nth; simpl.
 apply ps_monom_order_ge.
Qed.

Lemma monom_y_plus_c_is_inject_K : ∀ c,
  ([ps_monom c 0; 1%ps … []] = lap_inject_K_in_Kx [c; 1%K … []])%pslap.
Proof.
intros c.
unfold ps_lap_eq.
reflexivity.
Qed.

Lemma ps_monom_add : ∀ a b n,
  (ps_monom a n + ps_monom b n = ps_monom (a + b)%K n)%ps.
Proof.
intros a b n.
symmetry.
unfold ps_add; simpl.
unfold cm; simpl.
unfold ps_ordnum_add; simpl.
unfold ps_terms_add; simpl.
rewrite ps_adjust_eq with (n := O) (k := Qden n).
unfold adjust_ps; simpl.
rewrite Z.sub_0_r.
rewrite Z.min_id.
apply mkps_morphism; try reflexivity.
rewrite series_shift_0.
rewrite Z.sub_diag; simpl.
unfold adjust_series; simpl.
do 2 rewrite series_shift_0.
constructor; intros i; simpl.
destruct (zerop (i mod Pos.to_nat (Qden n))) as [H₁| H₁].
 apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
 destruct H₁ as (c, Hc).
 rewrite Nat.mul_comm in Hc; rewrite Hc.
 rewrite Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
 destruct c; [ reflexivity | simpl ].
 rewrite rng_add_0_l; reflexivity.

 rewrite rng_add_0_l; reflexivity.
Qed.

Lemma ps_monom_mul : ∀ a b m n,
  (ps_monom a m * ps_monom b n = ps_monom (a * b)%K (m + n))%ps.
Proof.
intros a b m n.
progress unfold ps_mul; simpl.
unfold cm; simpl.
unfold ps_monom; simpl.
apply mkps_morphism; try reflexivity.
constructor; intros i; simpl.
unfold convol_mul; simpl.
destruct i; simpl.
 unfold summation; simpl.
 rewrite Nat.mod_0_l; [ idtac | apply Pos2Nat_ne_0 ].
 rewrite Nat.mod_0_l; [ simpl | apply Pos2Nat_ne_0 ].
 rewrite Nat.div_0_l; [ idtac | apply Pos2Nat_ne_0 ].
 rewrite Nat.div_0_l; [ idtac | apply Pos2Nat_ne_0 ].
 rewrite rng_add_0_r; reflexivity.

 rewrite all_0_summation_0; [ reflexivity | idtac ].
 intros j (_, Hj).
 rewrite fold_sub_succ_l.
bbb.

Lemma lap_add_cons : ∀ α (R : ring α) a b la lb,
  ([a … la] + [b … lb] = [(a + b)%K … la + lb])%lap.
Proof. reflexivity. Qed.

Lemma lap_inject_add : ∀ la lb,
  (lap_inject_K_in_Kx la + lap_inject_K_in_Kx lb =
   lap_inject_K_in_Kx (la + lb)%lap)%pslap.
Proof.
intros la lb.
unfold lap_inject_K_in_Kx.
revert lb.
induction la as [| a]; intros; simpl.
 progress unfold ps_lap_add.
 rewrite lap_add_nil_l; reflexivity.

 destruct lb as [| b]; simpl.
  progress unfold ps_lap_add.
  rewrite lap_add_nil_r; reflexivity.

  progress unfold ps_lap_add.
  rewrite lap_add_cons.
  constructor; [ idtac | apply IHla ].
  rewrite ps_monom_add; reflexivity.
Qed.

Lemma ttt : ∀ la lb,
  (lap_inject_K_in_Kx la * lap_inject_K_in_Kx lb =
   lap_inject_K_in_Kx (la * lb)%lap)%pslap.
Proof.
intros la lb.
unfold lap_inject_K_in_Kx.
revert lb.
induction la as [| a]; intros; simpl.
 progress unfold ps_lap_mul.
 do 2 rewrite lap_mul_nil_l; reflexivity.

 destruct lb as [| b]; simpl.
  progress unfold ps_lap_mul.
  do 2 rewrite lap_mul_nil_r; reflexivity.

  progress unfold ps_lap_mul.
  do 2 rewrite lap_mul_cons; simpl.
  constructor; [ simpl; apply ps_monom_mul_pow_0 | idtac ].
bbb.

Lemma uuu : ∀ la lb,
  (lap_inject_K_in_Kx la ∘ lap_inject_K_in_Kx lb =
   lap_inject_K_in_Kx (lap_compose la lb))%pslap.
Proof.
intros la lb.
progress unfold lap_inject_K_in_Kx; simpl.
progress unfold ps_lap_comp.
progress unfold lap_compose.
revert lb.
induction la as [| a]; intros; [ reflexivity | simpl ].
rewrite IHla.
remember ttt as ttt.
clear Heqttt.
unfold lap_inject_K_in_Kx in ttt.
progress unfold ps_lap_mul in ttt.
rewrite ttt.
(* lap_inject_add *)
remember sss as sss.
clear Heqsss.
progress unfold lap_inject_K_in_Kx in sss.
progress unfold ps_lap_add in sss.
rewrite <- sss.
reflexivity.
qed.

(* [Walker, p 101] « O(bi) ≥ 0,  i = 0,...,n » *)
Theorem vvv : ∀ pol ns c₁ r f₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
    → r = root_multiplicity acf c₁ (Φq pol ns)
      → f₁ = pol₁ pol (β ns) (γ ns) c₁
        → ∀ i, (order (poly_nth i f₁) ≥ 0)%Qbar.
Proof.
intros pol ns c₁ r f₁ Hns Hc₁ Hr Hf₁ i.
remember (quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r) as Ψ eqn:HΨ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
rewrite f₁_eq_term_with_Ψ_plus_g; try eassumption.
destruct Hc₁ as (Hc₁, Hc₁nz).
unfold poly_nth; simpl.
rewrite fold_ps_lap_add.
rewrite lap_nth_add.
rewrite fold_ps_lap_comp.
eapply Qbar.le_trans; [ idtac | apply order_add ].
apply Qbar.min_glb.
 Focus 2.
 apply Qbar.lt_le_incl.
 apply nth_g_order_pos; assumption.

 rewrite <- lap_mul_assoc.
 rewrite fold_ps_lap_mul, fold_ps_lap_pow.
 destruct (le_dec r i) as [Hle| Hgt].
  Focus 2.
  apply Nat.nle_gt in Hgt.
  rewrite lap_nth_x_gt_pow_mul; [ idtac | assumption ].
  rewrite order_0; constructor.

  rewrite lap_nth_x_le_pow_mul; [ idtac | assumption ].
  progress unfold ps_lap_comp.
  rewrite monom_y_plus_c_is_inject_K.
  rewrite fold_ps_lap_pow.
  rewrite lap_power_map_ps.
  rewrite fold_ps_lap_comp.
  rewrite uuu.
bbb.
Check order_nth_inject_K.

(* [Walker, p 101] « O(bi) > 0,  i = 0,...,r-1 » *)
Theorem yyy : ∀ pol ns c₁ r f₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
    → r = root_multiplicity acf c₁ (Φq pol ns)
      → f₁ = pol₁ pol (β ns) (γ ns) c₁
        → ∀ i, (i < r)%nat
          → (order (poly_nth i f₁) > 0)%Qbar.
Proof.
intros pol ns c₁ r f₁ Hns Hc₁ Hr Hf₁ i Hir.
remember (quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r) as Ψ eqn:HΨ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
rewrite f₁_eq_term_with_Ψ_plus_g; try eassumption.
destruct Hc₁ as (Hc₁, Hc₁nz).
unfold poly_nth; simpl.
rewrite fold_ps_lap_add.
rewrite lap_nth_add.
rewrite fold_ps_lap_comp.
rewrite order_neq_min.
bbb.
*)

(* [Walker, p 101] « O(br) = 0 » *)
Theorem order_bbar_r_is_0 : ∀ pol ns c₁ r f₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
    → r = root_multiplicity acf c₁ (Φq pol ns)
      → f₁ = pol₁ pol (β ns) (γ ns) c₁
        → (order (poly_nth r f₁) = 0)%Qbar.
Proof.
intros pol ns c₁ r f₁ Hns Hc₁ Hr Hf₁.
remember (quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r) as Ψ eqn:HΨ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
rewrite f₁_eq_term_with_Ψ_plus_g; try eassumption.
destruct Hc₁ as (Hc₁, Hc₁nz).
unfold poly_nth; simpl.
remember ([0%ps; 1%ps … []] ^ r)%pslap as yr.
remember ([ps_monom c₁ 0; 1%ps … []] ^ j)%pslap as ycj.
remember (lap_inject_K_in_Kx (al Ψ)) as psy.
remember [ps_monom c₁ 0; 1%ps … []] as yc.
assert (order (lap_nth r (yr * ycj * psy ∘ yc)) = 0)%Qbar as Hor.
 subst yr ycj psy yc.
 progress unfold ps_lap_mul.
 rewrite <- lap_mul_assoc.
 do 2 rewrite fold_ps_lap_mul.
 erewrite lap_nth_x_le_pow_mul; [ idtac | reflexivity ].
 rewrite Nat.sub_diag.
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
  rewrite Qbar.mul_0_r; [ idtac | intros HH; discriminate HH ].
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

  intros HH; apply Hc₁nz.
  apply ps_monom_0_coeff_0; assumption.

 subst yr ycj psy yc.
 rewrite fold_ps_lap_add.
 rewrite lap_nth_add.
 rewrite fold_ps_lap_comp.
 rewrite order_neq_min; rewrite Hor.
 rewrite Qbar.min_l; [ reflexivity | idtac ].
  apply Qbar.lt_le_incl.
  apply nth_g_order_pos; assumption.

  apply Qbar.lt_neq.
  apply nth_g_order_pos; assumption.
Qed.

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

End theorems.
