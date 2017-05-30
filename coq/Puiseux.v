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
Require Import RootHeadTail.
Require Import RootAnyR.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Definition multiplicity_decreases f L n :=
  let c := ac_root (Φq f L) in
  let r := root_multiplicity acf c (Φq f L) in
  let fn := nth_pol n f L in
  let Ln := nth_ns n f L in
  let cn := nth_c n f L in
  let rn := root_multiplicity acf cn (Φq fn Ln) in
  lt_dec rn r.

Theorem order_root_tail_nonneg_any_r_aux : ∀ f L c f₁ L₁ m q₀ n r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q₀ = q_of_m m (γ L)
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (∀ i, i ≤ S n → (ps_poly_nth 0 (nth_pol i f L) ≠ 0)%ps)
  → (∀ i, i ≤ S n → nth_r i f L = r)
  → (0 ≤ order (root_tail (m * q₀) n f₁ L₁))%Qbar.
Proof.
intros f L c f₁ L₁ m q₀ n r HL Hm Hq₀ Hc Hf₁ HL₁ Hpsi Hri.
unfold root_tail.
remember (zerop_1st_n_const_coeff n f₁ L₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁; [ rewrite order_0; constructor | idtac ].
revert m q₀ c f L f₁ L₁ HL Hc Hm Hq₀ Hf₁ HL₁ Hz₁ Hpsi Hri.
induction n; intros.
 simpl.
 unfold order; simpl.
 pose proof (Hpsi 1%nat (Nat.le_refl 1)) as H; simpl in H.
 rewrite <- Hc, <- Hf₁ in H.
 rename H into Hnz₁; move Hnz₁ before HL₁.
 pose proof (Hri 0%nat Nat.le_0_1) as H.
 simpl in H; rewrite <- Hc in H.
 rename H into Hr₀; move Hr₀ before Hc.
 pose proof (Hri 1%nat (Nat.le_refl 1)) as H.
 simpl in H.
 rewrite <- Hc, <- Hf₁, <- HL₁ in H.
 remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
 move Hc₁ before HL₁.
 move c₁ before L₁.
 rename H into Hr₁; move Hr₁ before Hc₁.
 remember Hc as H; clear HeqH.
 eapply multiplicity_is_pos in H; try eassumption .
 rename H into Hrpos; move Hrpos before Hnz₁.
 remember HL₁ as H; clear HeqH.
 eapply r_n_next_ns in H; try eassumption .
 move H before Hnz₁.
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 remember HL₁ as H; clear HeqH.
 eapply hd_newton_segments in H; try eassumption .
 rename H into HL₁i; move HL₁i before HL₁.
 remember HL as H; clear HeqH.
 eapply next_pol_in_K_1_mq in H; try eassumption .
 remember (m * q₀)%positive as m₁ eqn:Hm₁.
 rename H into HK₁; move HK₁ before Hnz₁.
 move Hm₁ before Hq₀.
 rewrite Hini₁, Hfin₁; simpl.
 rewrite Hαk₁; simpl.
 rewrite Qnum_inv_Qnat_sub; [ | apply Hrpos ].
 rewrite Qden_inv_Qnat_sub; [ | apply Hrpos ].
 rewrite Z.add_0_r, Z.mul_1_r.
 remember (root_tail_series_from_cγ_list m₁ f₁ L₁) as t.
 remember (series_order {| terms := t |} 0) as v eqn:Hv .
 symmetry in Hv.
 destruct v; [ idtac | constructor ].
 apply Qbar.qfin_le_mono.
 rewrite Nat.sub_0_r.
 rewrite Z.mul_shuffle0, Pos_mul_shuffle0.
 rewrite Pos2Z.inj_mul.
 rewrite Z.div_mul_cancel_r; [ | apply Pos2Z_ne_0 | apply Pos2Z_ne_0 ].
 erewrite αj_m_eq_p_r with (L₁ := L₁); try eassumption; [ | reflexivity ].
 rewrite Z.mul_shuffle0.
 rewrite <- Zposnat2Znat; [ | assumption ].
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
 rewrite Z.div_mul; [ | apply Pos2Z_ne_0 ].
 unfold Qle; simpl.
 rewrite Z.mul_1_r.
 apply Z.add_nonneg_nonneg; [ idtac | apply Nat2Z.is_nonneg ].
 apply Z.lt_le_incl.
 eapply p_is_pos; eassumption .

 simpl in Hz₁; simpl.
 remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
 remember (next_pol f₁ (β L₁) (γ L₁) c₁) as f₂ eqn:Hpol₂ .
 remember (option_get phony_ns (newton_segments f₂)) as L₂ eqn:HL₂ .
 destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₁| H₁].
  discriminate Hz₁.

  remember (m * q₀)%positive as m₁ eqn:Hm₁ .
  replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
  pose proof (Hri 0%nat (Nat.le_0_l (S (S n)))) as H.
  simpl in H; rewrite <- Hc in H.
  rename H into Hr₀; move Hr₀ before Hc.
  assert (1 ≤ S (S n)) as H by apply le_n_S, Nat.le_0_l.
  apply Hri in H; simpl in H.
  rewrite <- Hc, <- Hf₁, <- HL₁, <- Hc₁ in H.
  rename H into Hr₁; move Hr₁ before Hc₁.
  remember Hc as H; clear HeqH.
  eapply multiplicity_is_pos in H; try eassumption .
  rename H into Hrpos; move Hrpos before HL₁.
  remember HL₁ as H; clear HeqH.
  eapply r_n_next_ns in H; try eassumption .
  destruct H as (αj₁, (αk₁, H)).
  destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
  remember HL₁ as H; clear HeqH.
  eapply hd_newton_segments in H; try eassumption .
  rename H into HL₁i; move HL₁i before HL₁.
  remember HL as H; clear HeqH.
  eapply next_pol_in_K_1_mq in H; try eassumption .
  rewrite <- Hm₁ in H.
  rename H into HK₁; move HK₁ before HL₁i.
  eapply IHn with (L := L₁) (f := f₁); try eassumption .
   symmetry in Hr₁; symmetry.
   eapply q_eq_1_any_r with (f := f₁); try eassumption; reflexivity.

   intros i Hin.
   apply Nat.succ_le_mono in Hin.
   apply Hpsi in Hin; simpl in Hin.
   rewrite <- Hc, <- Hf₁, <- HL₁ in Hin.
   assumption.

   intros i Hin.
   apply Nat.succ_le_mono in Hin.
   apply Hri in Hin; simpl in Hin.
   rewrite <- Hc, <- Hf₁, <- HL₁ in Hin.
   assumption.
Qed.

(* todo: group order_root_tail_nonneg_any_r_aux and this theorem together *)
Theorem order_root_tail_nonneg_any_r : ∀ f L c f₁ L₁ m q₀ n r,
  newton_segments f = Some L
  → m = ps_pol_com_polydo f
  → q₀ = q_of_m m (γ L)
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → zerop_1st_n_const_coeff n f L = false
  → root_multiplicity acf c (Φq f L) = r
  → (∀ i, r ≤ nth_r i f L)
  → (0 ≤ order (root_tail (m * q₀) n f₁ L₁))%Qbar.
Proof.
intros f L c f₁ L₁ m q₀ n r.
intros HL HK Hq₀ Hc Hf₁ HL₁ Hz Hr Hrle.
rewrite zerop_1st_n_const_coeff_false_iff in Hz.
pose proof (Hz O (Nat.le_0_l n)) as H; simpl in H.
rename H into Hnz; move Hnz before Hc.
apply zerop_1st_n_const_coeff_false_iff in Hz.
remember (zerop_1st_n_const_coeff n f₁ L₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁.
 unfold root_tail.
 rewrite Hz₁.
 rewrite order_0; constructor.

 eapply order_root_tail_nonneg_any_r_aux with (r := r); try eassumption.
  pose proof (exists_pol_ord K f) as H.
  destruct H as (m', (Hm', Hp)).
  rewrite <- HK in Hm'; subst m'.
  apply Hp.

  apply not_zero_1st_prop; [ simpl | assumption ].
  rewrite <- Hc, <- Hf₁, <- HL₁; assumption.

  apply non_decr_imp_eq; try assumption.
   rewrite zerop_1st_n_const_coeff_succ; simpl.
   rewrite <- Hc, <- Hf₁, <- HL₁; rewrite Hz₁.
   remember (ps_poly_nth 0 f) as x.
   destruct (ps_zerop K x); [ contradiction | reflexivity ].

   simpl; rewrite <- Hc; assumption.
Qed.

Theorem zerop_1st_n_const_coeff_false_before : ∀ f L m,
  zerop_1st_n_const_coeff m f L = false
  → ∀ i, i ≤ m →
    zerop_1st_n_const_coeff i f L = false.
Proof.
intros f L m H i Hi.
rewrite zerop_1st_n_const_coeff_false_iff in H.
apply zerop_1st_n_const_coeff_false_iff.
intros j Hj; apply H.
transitivity i; assumption.
Qed.

Theorem multiplicity_not_decreasing : ∀ f L r,
  (∀ i : nat, if multiplicity_decreases f L i then False else True)
  → root_multiplicity acf (ac_root (Φq f L)) (Φq f L) = r
  → ∀ j, r ≤ nth_r j f L.
Proof.
intros f L r Hn Hr j.
pose proof Hn j as H.
remember (multiplicity_decreases f L j) as p eqn:Hp .
destruct p as [| p]; [ contradiction  |  ].
unfold multiplicity_decreases in Hp; simpl in Hp.
destruct
  (lt_dec
     (root_multiplicity acf (nth_c j f L)
                        (Φq (nth_pol j f L) (nth_ns j f L)))
     (root_multiplicity acf (ac_root (Φq f L)) (Φq f L)))
 as [| H₁].
contradiction .

 clear Hp.
 apply Nat.nlt_ge in H₁.
 rewrite Hr in H₁.
 erewrite <- nth_r_n in H₁; try eassumption; reflexivity.
Qed.

Theorem in_newton_segment_when_r_constant : ∀ f L f₁ L₁ c r,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → root_multiplicity acf c (Φq f L) = S r
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (ps_poly_nth 0 f ≠ 0)%ps
  → (∀ n : nat, S r ≤ nth_r n f L)
  → ∀ n fn Ln,
    zerop_1st_n_const_coeff n f₁ L₁ = false
    → fn = nth_pol n f₁ L₁
    → Ln = nth_ns n f₁ L₁
    → newton_segments fn = Some Ln.
Proof.
intros f L f₁ L₁ c r.
intros HL Hc Hr Hf₁ HL₁ Hnz₀ Hrle N polN LN Hz HpolN HLN.
rewrite zerop_1st_n_const_coeff_false_iff in Hz.
eapply nth_in_newton_segments_any_r with (L₁ := L₁); try eassumption;
 [ | apply eq_refl ].
generalize HL₁; intros H.
pose proof (Hz O (Nat.le_0_l N)) as H₁.
rewrite <- Hc in Hf₁.
eapply r_n_next_ns in H; try eassumption; try apply eq_refl.
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (Hini₁, (Hfin₁, (Hαj₁, Hαk₁))).
 eapply hd_newton_segments; try eassumption.
 apply Nat.lt_0_succ.

 rewrite <- nth_r_n with (n := 1%nat) (f := f) (L := L).
  symmetry.
  apply r_le_eq_incl with (n := 1%nat); try assumption.
   simpl; rewrite <- Hc; assumption.

   intros i Hi.
   destruct i; [ assumption | simpl ].
   rewrite <- Hc, <- Hf₁, <- HL₁.
   apply Hz.
   apply Nat.succ_le_mono in Hi.
   apply Nat.le_0_r in Hi; subst i.
   apply Nat.le_0_l.

   intros; apply Hrle; assumption.

   apply Nat.le_refl.

  simpl; rewrite <- Hc; assumption.

  simpl; rewrite <- Hc, <- Hf₁; assumption.

  symmetry.
  apply nth_c_n.
   simpl; rewrite <- Hc; assumption.

   simpl; rewrite <- Hc, <- Hf₁; assumption.
Qed.

Theorem upper_bound_zerop_1st_when_r_constant : ∀ f L c f₁ L₁ m q₀ r ofs,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (ps_poly_nth 0 f ≠ 0)%ps
  → m = ps_pol_com_polydo f
  → q₀ = q_of_m m (γ L)
  → root_multiplicity acf c (Φq f L) = S r
  → (∀ i : nat, if multiplicity_decreases f L i then False else True)
  → (order (ps_pol_apply f₁ (root_tail (m * q₀) 0 f₁ L₁)) =
     qfin ofs)%Qbar
  → ∀ N,
    N = Z.to_nat (2 * ' m * ' q₀ * Qnum ofs)
    → zerop_1st_n_const_coeff N f₁ L₁ = true.
Proof.
intros f L c f₁ L₁ m q₀ r ofs.
intros HL Hc Hf₁ HL₁ Hnz₀ Hm Hq₀ Hr Hn Hofs N HN.
apply not_false_iff_true; intros Hz.
assert (Hrle : ∀ n : nat, S r ≤ nth_r n f L).
 rewrite Hc in Hr.
 apply multiplicity_not_decreasing; assumption.

 remember (1 # 2 * m * q₀) as η eqn:Hη .
 assert (Hηβ : ∀ i, i ≤ N → η < β (nth_ns i f₁ L₁)).
  intros i Hi.
  clear HN.
  revert HL Hc Hf₁ HL₁ Hnz₀ Hm Hq₀ Hr Hrle Hη N Hi Hz; clear; intros.
  subst c q₀.
  eapply β_lower_bound_r_const with (n := i) (r := S r); try eassumption.
   pose proof (exists_pol_ord K f) as H.
   destruct H as (m', (Hm', Hp)).
   rewrite <- Hm in Hm'; subst m'.
   apply Hp.

   apply Nat.lt_0_succ.

   eapply zerop_1st_n_const_coeff_false_before; eassumption.

   apply non_decr_imp_eq; try assumption.
   apply zerop_1st_n_const_coeff_false_succ; [ assumption | simpl ].
   rewrite <- Hf₁, <- HL₁.
   eapply zerop_1st_n_const_coeff_false_before; eassumption.

   apply eq_refl.

  remember (@summation _ Q_ring O N (λ i, β (nth_ns i f₁ L₁))) as u eqn:Hu .
  assert (Huo : u <= ofs).
   rewrite Hc in Hf₁.
   revert HL Hc Hf₁ HL₁ Hnz₀ Hm Hq₀ Hr Hofs Hz Hrle Hu; clear; intros.
   rewrite root_tail_when_r_r with (n := N) (r := (S r)) in Hofs;
    try eassumption.
    rewrite apply_nth_pol in Hofs; [  | assumption ].
    rewrite <- Hu in Hofs.
    destruct (fld_zerop 1%K) as [H₀| H₀].
     rewrite H₀ in Hofs.
     rewrite ps_zero_monom_eq in Hofs.
     rewrite ps_mul_0_l in Hofs.
     rewrite order_0 in Hofs.
     symmetry in Hofs.
     apply eq_Qbar_qinf in Hofs.
     discriminate Hofs.

     rewrite order_mul in Hofs.
     rewrite ps_monom_order in Hofs; [  | assumption ].
     apply Qbar.qfin_le_mono.
     rewrite <- Hofs.
     apply Qbar.le_sub_le_add_l.
     rewrite Qbar.sub_diag.
     apply order_pol_apply_nonneg.
      intros a Ha.
      remember (nth_pol N f₁ L₁) as polN eqn:HpolN .
      remember (nth_ns N f₁ L₁) as LN eqn:HLN .
      assert (H : newton_segments polN = Some LN).
       eapply in_newton_segment_when_r_constant; eassumption.

       eapply f₁_orders in H; try eassumption; try apply eq_refl.
       erewrite <- nth_pol_succ in H; try eassumption.
        destruct H as (H, _).
        apply List_In_nth with (d := 0%ps) in Ha.
        destruct Ha as (n, Hn₁).
        rewrite Hn₁.
        apply H.

        symmetry.
        apply nth_c_n; try eassumption.

      rewrite Nat.add_0_l.
      rewrite <- Hc in Hf₁.
      eapply order_root_tail_nonneg_any_r; try eassumption.
      rewrite zerop_1st_n_const_coeff_succ; simpl.
      rewrite <- Hc, <- Hf₁, <- HL₁, Hz.
      remember (ps_poly_nth 0 f) as x.
      destruct (ps_zerop K x); [ contradiction  | reflexivity ].

    pose proof (exists_pol_ord K f) as H.
    destruct H as (m', (Hm', Hp)).
    rewrite <- Hm in Hm'; subst m'.
    apply Hp.

    apply non_decr_imp_eq; auto.
     apply zerop_1st_n_const_coeff_false_iff.
     intros j Hj.
     destruct j; [ assumption |  ].
     apply le_S_n in Hj.
     apply Nat.le_0_r in Hj; subst j; simpl.
     rewrite <- Hf₁.
     rewrite zerop_1st_n_const_coeff_false_iff in Hz.
     pose proof (Hz O (Nat.le_0_l N)) as H₁.
     assumption.

     simpl; rewrite <- Hc; assumption.

    rewrite zerop_1st_n_const_coeff_succ; simpl.
    rewrite <- Hf₁, <- HL₁, Hz.
    remember (ps_poly_nth 0 f) as x.
    destruct (ps_zerop K x); [ contradiction  | reflexivity ].

   assert (Hou : ofs < u).
    clear Hofs Hn.
    subst u.
    apply summation_all_lt in Hηβ.
    eapply Qle_lt_trans; try eassumption.
    rewrite Hη, HN.
    rewrite <- Pos2Z.inj_mul.
    rewrite <- Pos2Z.inj_mul.
    remember (2 * m * q₀)%positive as mq eqn:Hmq .
    rewrite Z.mul_comm.
    rewrite Z2Nat_inj_mul_pos_r.
    unfold Qle; simpl.
    rewrite Pos.mul_1_r.
    rewrite Pos2Z.inj_mul.
    rewrite Zpos_P_of_succ_nat.
    rewrite Nat2Z.inj_mul.
    remember (Qnum ofs) as nofs eqn:Hnofs .
    symmetry in Hnofs.
    destruct nofs as [| nofs| nofs]; simpl; auto.
     rewrite positive_nat_Z.
     rewrite Z.mul_succ_l.
     rewrite positive_nat_Z.
     rewrite <- Pos2Z.inj_mul.
     rewrite <- Z.mul_1_r at 1.
     eapply Z.le_trans.
      apply Z.mul_le_mono_nonneg_l with (m := (' Qden ofs)%Z); auto.

      rewrite Z.one_succ.
      apply Zlt_le_succ.
      apply Pos2Z.is_pos.

      apply Z.le_sub_le_add_l.
      rewrite Z.sub_diag; apply Pos2Z.is_nonneg.

     apply Zle_neg_pos.

    apply Qlt_not_le in Hou; contradiction .
Qed.

Definition f₁_root_when_r_constant f L :=
  if fld_zerop 1%K then 0%ps
  else
    let m := ps_pol_com_polydo f in
    let q₀ := q_of_m m (γ L) in
    let f₁ := next_pol f (β L) (γ L) (ac_root (Φq f L)) in
    let L₁ := option_get phony_ns (newton_segments f₁) in
    let s := root_tail (m * q₀) 0 f₁ L₁ in
    match order (ps_pol_apply f₁ s) with
    | qfin ofs =>
        let N := Z.to_nat (2 * ' m * ' q₀ * Qnum ofs) in
        if zerop_1st_n_const_coeff N f₁ L₁ then
          match lowest_with_zero_1st_const_coeff acf N f₁ L₁ with
          | O => 0%ps
          | S i' => root_head 0 i' f₁ L₁
          end
        else 0%ps
    | ∞%Qbar => s
    end.

Theorem root_for_f₁_when_r_constant : ∀ f L f₁,
  newton_segments f = Some L
  → (ps_poly_nth 0 f ≠ 0)%ps
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → (∀ i, if multiplicity_decreases f L i then False else True)
  → (ps_pol_apply f₁ (f₁_root_when_r_constant f L) = 0)%ps.
Proof.
intros f L f₁ HL Hnz₀ Hf₁ Hn.
unfold f₁_root_when_r_constant.
rewrite <- Hf₁.
remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁.
remember (ac_root (Φq f L)) as c eqn:Hc in Hf₁.
remember (ps_pol_com_polydo f) as m eqn:Hm.
remember (q_of_m m (γ L)) as q₀ eqn:Hq₀ .
remember (root_tail (m * q₀) 0 f₁ L₁) as s eqn:Hs .
destruct (fld_zerop 1%K) as [H₀| H₀].
 unfold ps_pol_apply, apply_poly, apply_lap; simpl.
 destruct (al f₁) as [| a]; [ reflexivity | simpl ].
 rewrite rng_mul_0_r, rng_add_0_l.
 apply eq_1_0_ps_0; assumption.

 remember (order (ps_pol_apply f₁ s)) as ofs eqn:Hofs .
 destruct ofs as [ofs| ].
  remember (Z.to_nat (2 * ' m * ' q₀ * Qnum ofs)) as N eqn:HN .
  remember (zerop_1st_n_const_coeff N f₁ L₁) as z eqn:Hz .
  symmetry in Hz.
  destruct z.
   apply lowest_zerop_1st_n_const_coeff in Hz.
   destruct Hz as (i, (Hi, (Hin, (Hji, Hz)))).
   symmetry in Hi.
   rewrite Hi.
   destruct Hji as [Hi2| Hpi].
    move Hi2 at top; subst i.
    simpl in Hz.
    destruct (ps_zerop K (ps_poly_nth 0 f₁)); [ | discriminate Hz ].
    apply a₀_0_root_0; assumption.

    destruct i.
     simpl in Hpi, Hz; rewrite Hpi in Hz; discriminate Hz.

     apply root_when_fin in Hpi; [ apply Hpi | assumption ].

   exfalso.
   remember (root_multiplicity acf c (Φq f L)) as r eqn:Hr .
   symmetry in Hr.
   pose proof (multiplicity_neq_0 acf f HL Hc) as H.
   destruct r; [ contradiction | ].
   revert Hz; apply not_false_iff_true.
   eapply upper_bound_zerop_1st_when_r_constant; try eassumption.
   rewrite Hofs, Hs; reflexivity.

  symmetry in Hofs.
  apply order_inf; assumption.
Qed.

Theorem degree_pos_imp_L_not_empty : ∀ f,
  degree (ps_zerop K) f ≥ 1
  → (ps_poly_nth 0 f ≠ 0)%ps
  → newton_segments f ≠ None.
Proof.
intros f Hdeg Hnz.
unfold degree in Hdeg.
unfold ps_poly_nth in Hnz.
unfold ps_lap_nth in Hnz.
unfold newton_segments, points_of_ps_polynom.
unfold points_of_ps_lap, points_of_ps_lap_gen; simpl.
intros HLl.
remember (al f) as la eqn:Hla .
clear f Hla.
destruct la as [| a]; [ apply Hnz; reflexivity | idtac ].
simpl in Hdeg, Hnz, HLl.
remember (degree_plus_1_of_list (ps_zerop K) la) as d eqn:Hd .
symmetry in Hd.
destruct d.
 destruct (ps_zerop K a) as [H₁| H₁].
  apply Nat.nlt_ge in Hdeg; apply Hdeg, Nat.lt_0_1.

  apply Nat.nlt_ge in Hdeg; apply Hdeg, Nat.lt_0_1.

 clear Hdeg.
 apply order_fin in Hnz.
 remember (order a) as va eqn:Hva .
 symmetry in Hva.
 destruct va as [va| ]; [ clear Hnz | apply Hnz; reflexivity ].
 remember 1%nat as pow in HLl; clear Heqpow.
 revert a d va pow Hd Hva HLl.
 induction la as [| b]; intros; [ discriminate Hd | idtac ].
 simpl in Hd.
 remember (degree_plus_1_of_list (ps_zerop K) la) as e eqn:He  in Hd.
 symmetry in He.
 destruct e.
  destruct (ps_zerop K b) as [H₁| H₁]; [ discriminate Hd | idtac ].
  clear d Hd.
  simpl in HLl.
  apply order_fin in H₁.
  remember (order b) as vb eqn:Hvb .
  symmetry in Hvb.
  destruct vb as [vb| ]; [ discriminate HLl | apply H₁; reflexivity ].

  clear d Hd.
  simpl in HLl.
  remember (order b) as vb eqn:Hvb .
  symmetry in Hvb.
  destruct vb as [vb| ]; [ discriminate HLl | idtac ].
  eapply IHla; eauto .
Qed.

Theorem degree_pos_imp_has_ns : ∀ f,
  degree (ps_zerop K) f ≥ 1
  → (ps_poly_nth 0 f ≠ 0)%ps
  → ∃ L, newton_segments f = Some L.
Proof.
intros * Hdeg Hnz.
specialize (degree_pos_imp_L_not_empty f Hdeg Hnz) as H.
remember (newton_segments f) as Ll eqn:HLl .
symmetry in HLl.
destruct Ll as [L| ]; [ | now exfalso; apply H ].
now exists L.
Qed.

Theorem f₁_has_root : ∀ f L f₁,
  newton_segments f = Some L
  → (ps_poly_nth 0 f ≠ 0)%ps
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → ∃ s₁, (ps_pol_apply f₁ s₁ = 0)%ps.
Proof.
intros f L f₁ HL Hnz₀ Hf₁.
remember (ac_root (Φq f L)) as c eqn:Hc.
remember (root_multiplicity acf c (Φq f L)) as r eqn:Hr .
symmetry in Hr.
revert f L c f₁ HL Hnz₀ Hc Hf₁ Hr.
induction r as (r, IHr) using lt_wf_rec; intros.
set (v := fun i => if multiplicity_decreases f L i then S O else O).
destruct (LPO v) as [Hn| Hn].
 subst c.
 exists (f₁_root_when_r_constant f L).
 eapply root_for_f₁_when_r_constant; try eassumption.
 intros i.
 specialize (Hn i); unfold v in Hn.
 now destruct (multiplicity_decreases f L i).

 destruct Hn as (n, Hn).
 unfold v in Hn; clear v.
 unfold multiplicity_decreases in Hn.
 rewrite <- Hc, Hr in Hn.
 remember (nth_pol n f L) as fn eqn:Hfn .
 remember (nth_ns n f L) as Ln eqn:HLn .
 remember (nth_c n f L) as cn eqn:Hcn .
 remember (root_multiplicity acf cn (Φq fn Ln)) as rn eqn:Hrn .
 symmetry in Hrn.
 destruct (lt_dec rn r) as [Hrnr| Hrnr]; [ | now exfalso ].
 destruct n.
  exfalso.
  simpl in Hfn, HLn, Hcn.
  subst fn Ln cn.
  rewrite <- Hc in Hrn.
  rewrite <- Hrn, Hr in Hrnr.
  now apply lt_irrefl in Hrnr.

  clear Hn; rename Hrnr into Hn.
  remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
  erewrite <- nth_r_n in Hrn; try eassumption; subst rn.
  apply lowest_i_such_that_ri_lt_r₀ in Hn; [  | subst; auto ].
  destruct Hn as (i, (Hin, (Hir, Hri))).
  destruct Hir as [Hir| Hir].
   rewrite Hir, <- Hr, Hc in Hri.
   now apply Nat.lt_irrefl in Hri.

   destruct i.
    rewrite <- Hr, Hc in Hri.
    now apply Nat.lt_irrefl in Hri.

    remember (nth_pol i f L) as fi eqn:Hfi .
    remember (nth_ns i f L) as Li eqn:HLi .
    remember (nth_pol (S i) f L) as fsi eqn:Hfsi .
    remember (nth_ns (S i) f L) as Lsi eqn:HLsi .
    remember (newton_segments fsi) as Lo eqn:HLo .
    remember (nth_c (S i) f L) as cssi eqn:Hcssi.
    remember (next_pol fsi (β Lsi) (γ Lsi) cssi) as fssi eqn:Hfssi.
    symmetry in HLo.
    destruct Lo as [L₂| ].
     remember (zerop_1st_n_const_coeff i f₁ L₁) as z eqn:Hz .
     symmetry in Hz.
     destruct z.
      apply lowest_zerop_1st_n_const_coeff in Hz.
      destruct Hz as (m, (Hm, (Hmi, (Hle, Heq)))).
      destruct Hle as [Hle| Hle].
       move Hle at top; subst m.
       simpl in Heq.
       destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₂| H₂].
        exists 0%ps.
        apply a₀_0_root_0; assumption.

        discriminate Heq.

       exists (root_head 0 (pred m) f₁ L₁).
       apply root_when_fin; assumption.

      eapply IHr with (f := fsi) (L := Lsi) (f₁ := fssi) in Hri.
       destruct Hri as (s₁, Hs₁).
       remember (root_head 0 i f₁ L₁) as rh.
       remember (ps_monom 1%K (γ_sum 0 i f₁ L₁)) as mo.
       exists (rh + mo * s₁)%ps; subst rh mo.
       rewrite apply_nth_pol; auto.
       erewrite nth_pol_n; try eassumption; eauto  .
       erewrite <- nth_c_n; try eassumption.
       rewrite <- Hcssi, <- Hfssi.
       rewrite Hs₁, rng_mul_0_r; reflexivity.

       subst Lsi.
       erewrite nth_ns_succ; [ | eassumption ].
       now rewrite HLo.

       rewrite zerop_1st_n_const_coeff_false_iff in Hz.
       pose proof (Hz i (Nat.le_refl i)) as H.
       rewrite Hfsi; simpl.
       rewrite <- Hc, <- Hf₁, <- HL₁; auto.

       reflexivity.

       erewrite nth_c_n in Hcssi; try eassumption.
       rewrite <- Hcssi; assumption.

       symmetry.
       apply nth_r_n; try eassumption.
       erewrite nth_c_n; try eassumption; reflexivity.

     destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₁| H₁].
      apply a₀_0_root_0 in H₁.
      exists 0%ps; assumption.

      generalize HLo; intros H.
      rewrite Hfsi in H.
      simpl in H.
      rewrite <- Hc, <- Hf₁, <- HL₁ in H.
      apply nth_newton_segments_nil in H; auto.
       destruct H as (j, (Hjn, (Hjz, Hjnz))).
       destruct Hjz as [Hjz| Hjz].
        subst j.
        simpl in Hjnz.
        destruct (ps_zerop K (ps_poly_nth 0 f₁)); [ contradiction | ].
        discriminate Hjnz.

        exists (root_head 0 (pred j) f₁ L₁).
        apply root_when_fin; assumption.

       clear H.
       remember HL as H; clear HeqH.
       eapply next_has_root_0_or_newton_segments in H; auto.
       simpl in H.
       rewrite <- Hc, <- Hf₁ in H.
       destruct H; [ contradiction | ].
       rewrite HL₁.
       now destruct (newton_segments f₁).
Qed.

Theorem puiseux_series_algeb_closed : ∀ (f : polynomial (puiseux_series α)),
  degree (ps_zerop K) f ≥ 1
  → ∃ s, (ps_pol_apply f s = 0)%ps.
Proof.
intros f Hdeg.
destruct (ps_zerop _ (ps_poly_nth 0 f)) as [Hz| Hnz].
 exists 0%ps.
 unfold ps_pol_apply, apply_poly, apply_lap; simpl.
 unfold ps_poly_nth, ps_lap_nth in Hz; simpl in Hz.
 remember (al f) as la eqn:Hla .
 symmetry in Hla.
 destruct la as [| a]; [ reflexivity | simpl in Hz; simpl ].
 rewrite rng_mul_0_r, rng_add_0_l; assumption.

 specialize (degree_pos_imp_has_ns f Hdeg Hnz) as (L, HL).
 remember (ac_root (Φq f L)) as c eqn:Hc .
 remember (next_pol f (β L) (γ L) c) as f₁ eqn:Hf₁ .
 rewrite Hc in Hf₁.
 specialize (f₁_has_root HL Hnz Hf₁) as (s₁, Hs₁).
 exists (ps_monom c (γ L) + ps_monom 1%K (γ L) * s₁)%ps.
 eapply f₁_root_f_root; eauto .
 rewrite <- Hc.
 reflexivity.
Qed.

End theorems.

Check puiseux_series_algeb_closed.

(*
Print Assumptions puiseux_series_algeb_closed.
*)
