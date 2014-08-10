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

Set Implicit Arguments.

Definition phony_ns :=
  {| ini_pt := (0, 0); fin_pt := (0, 0); oth_pts := [] |}.

Fixpoint nth_pol α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n pol ns :=
  match n with
  | 0%nat => pol
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_pol n₁ pol₁ ns₁
  end.

Fixpoint nth_ns α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n pol ns :=
  match n with
  | 0%nat => ns
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_ns n₁ pol₁ ns₁
  end.

Fixpoint nth_c α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n pol ns :=
  match n with
  | 0%nat => ac_root (Φq pol ns)
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_c n₁ pol₁ ns₁
  end.

Fixpoint nth_γ α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n pol ns :=
  match n with
  | 0%nat => γ ns
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_γ n₁ pol₁ ns₁
  end.

Definition same_r α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  pol ns :=
  let c₁ := ac_root (Φq pol ns) in
  let r₁ := root_multiplicity acf c₁ (Φq pol ns) in
  let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
  let ns₁ := List.hd phony_ns (newton_segments pol₁) in
  let c₂ := ac_root (Φq pol₁ ns₁) in
  let r₁ := root_multiplicity acf c₁ (Φq pol ns) in
  let r₂ := root_multiplicity acf c₂ (Φq pol₁ ns₁) in
  r₁ = r₂.

Fixpoint polydromy_if_r_reaches_one α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} m pol {struct m} :=
  match m with
  | 0%nat => 0%nat
  | S m₁ =>
      let ns := List.hd phony_ns (newton_segments pol) in
      let c₁ := ac_root (Φq pol ns) in
      let r₁ := root_multiplicity acf c₁ (Φq pol ns) in
      if eq_nat_dec r₁ 1 then 1%nat
      else
        let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
        let v := polydromy_if_r_reaches_one m₁ pol₁ in
        (v * Pos.to_nat (Qden (γ ns)))%nat
  end.

Definition next_pow pow ns₁ m :=
  let n := (γ ns₁ * inject_Z ('m)) in
  (pow + Z.to_nat (Qnum n / ' Qden n))%nat.

Fixpoint find_coeff α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} max_iter npow m pol ns i :=
  match max_iter with
  | 0%nat => 0%K
  | S mx =>
      if ps_zerop _ (ps_poly_nth 0 pol) then 0%K
      else
        match Nat.compare npow i with
        | Eq => ac_root (Φq pol ns)
        | Lt =>
            let c₁ := ac_root (Φq pol ns) in
            let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
            let ns₁ := List.hd phony_ns (newton_segments pol₁) in
            let npow₁ := next_pow npow ns₁ m in
            find_coeff mx npow₁ m pol₁ ns₁ i
        | Gt => 0%K
        end
  end.

Definition root_tail_series_from_cγ_list α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} m pol ns i :=
  find_coeff (S i) 0%nat m pol ns i.

Definition root_tail_from_cγ_list α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} m pol ns :=
  {| ps_terms := {| terms := root_tail_series_from_cγ_list m pol ns |};
     ps_ordnum := Qnum (γ ns) * ' m / ' Qden (γ ns);
     ps_polord := m |}.

Definition γ_sum α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} b n pol ns :=
  let qr := Q_ring in
  Σ (i = 0, n), nth_γ (b + i) pol ns.

Fixpoint root_head_from_cγ_list α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} pol ns b n i :=
  (ps_monom (nth_c (b + i) pol ns) (γ_sum b i pol ns) +
   match n with
   | O => 0%ps
   | S n₁ =>
       if ps_zerop R (ps_poly_nth 0 (nth_pol (b + S i) pol ns)) then 0%ps
       else root_head_from_cγ_list pol ns b n₁ (S i)
   end)%ps.

Fixpoint zerop_1st_n_const_coeff α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} n pol ns :=
  if ps_zerop _ (ps_poly_nth 0 pol) then true
  else
    match n with
    | O => false
    | S n₁ =>
        let c₁ := ac_root (Φq pol ns) in
        let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
        let ns₁ := List.hd phony_ns (newton_segments pol₁) in
        zerop_1st_n_const_coeff n₁ pol₁ ns₁
    end.

(* Σ _(i=0,n).c_{b+i} x^Σ_(j=0,i) γ_{b+j} *)
Definition root_head α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  b n pol ns :=
  if zerop_1st_n_const_coeff b pol ns then 0%ps
  else root_head_from_cγ_list pol ns b n 0.

(* Σ _(i=n+1,∞).c_i x^Σ_(j=n+1,∞) γ_j *)
Definition root_tail α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  m n pol ns :=
  if zerop_1st_n_const_coeff n pol ns then 0%ps
  else root_tail_from_cγ_list m (nth_pol n pol ns) (nth_ns n pol ns).

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Lemma fold_γ_sum : ∀ b n pol ns,
  let qr := Q_ring in
  Σ (i = 0, n), nth_γ (b + i) pol ns = γ_sum b n pol ns.
Proof. reflexivity. Qed.

(* to be moved in the good file *)
Theorem ps_inv_monom : ∀ c pow,
  (c ≠ 0)%K
  → (¹/(ps_monom c pow) = ps_monom ¹/c%K (- pow))%ps.
Proof.
intros c pow Hc.
unfold ps_inv.
unfold ps_monom; simpl.
do 2 rewrite fold_series_const.
remember (null_coeff_range_length R (series_const c) 0) as v eqn:Hv .
symmetry in Hv.
apply null_coeff_range_length_iff in Hv.
unfold null_coeff_range_length_prop in Hv.
simpl in Hv.
destruct v as [v| ].
 destruct Hv as (Hiv, Hv).
 symmetry.
 rewrite ps_adjust_eq with (n := v) (k := xH).
 unfold adjust_ps; simpl.
 rewrite series_stretch_1, Z.mul_1_r, Pos.mul_1_r.
 apply mkps_morphism; try reflexivity.
 unfold series_inv; simpl.
 unfold series_shift, series_left_shift; simpl.
 constructor; intros i; simpl.
 rewrite Nat.add_0_r.
 destruct (zerop v) as [H₁| H₁].
  subst v; simpl.
  rewrite Nat.sub_0_r.
  destruct (zerop i) as [H₁| H₁]; [ reflexivity | idtac ].
  rewrite fold_series_const.
  rewrite summation_split_first; auto; simpl.
  rewrite rng_mul_0_l, rng_add_0_l.
  rewrite all_0_summation_0.
   rewrite rng_mul_0_r; reflexivity.

   intros j (Hj, Hji).
   destruct (zerop j) as [H₂| H₂].
    subst j.
    apply Nat.nlt_ge in Hj.
    exfalso; apply Hj, Nat.lt_0_succ.

    rewrite rng_mul_0_l; reflexivity.

  exfalso; apply Hv; reflexivity.

 pose proof (Hv O) as H; simpl in H.
 contradiction.
Qed.

Theorem null_coeff_range_length_const : ∀ c,
  (c ≠ 0)%K
  → null_coeff_range_length R (series_const c) 0 = 0%Nbar.
Proof.
intros c Hc.
apply null_coeff_range_length_iff.
unfold null_coeff_range_length_prop; simpl.
split; [ idtac | assumption ].
intros i Hi.
exfalso; revert Hi; apply Nat.nlt_0_r.
Qed.

Lemma normalise_ps_monom : ∀ c q,
  (c ≠ 0)%K
  → normalise_ps (ps_monom c q) ≐ ps_monom c (Qred q).
Proof.
intros c q Hc.
unfold normalise_ps; simpl.
rewrite fold_series_const.
rewrite null_coeff_range_length_const; auto; simpl.
rewrite Z.add_0_r.
erewrite greatest_series_x_power_series_const; [ idtac | reflexivity ].
unfold gcd_ps; simpl.
rewrite Z.add_0_r; simpl.
rewrite Z.gcd_0_r; simpl.
unfold Qred; simpl.
destruct q as (q₁, q₂).
pose proof (Z.ggcd_correct_divisors q₁ (' q₂)) as H.
remember (Z.ggcd q₁ (' q₂)) as g.
destruct g as (g, (aa, bb)).
destruct H as (Hq₁, Hq₂); simpl.
rewrite Hq₁, Hq₂; simpl.
pose proof (Z.ggcd_gcd q₁ (' q₂)) as Hg.
rewrite <- Heqg in Hg; simpl in Hg.
assert (0 <= g)%Z as Hgnn by (subst g; apply Z.gcd_nonneg).
assert (g ≠ 0)%Z as Hgnz.
 subst g; intros H.
 apply Z.gcd_eq_0_r in H.
 revert H; apply Pos2Z_ne_0.

 rewrite Z.gcd_mul_mono_l_nonneg; auto.
 assert (Z.gcd aa bb = 1)%Z as Hg1.
  apply Z.mul_reg_l with (p := g); auto.
  rewrite Z.mul_1_r.
  rewrite <- Z.gcd_mul_mono_l_nonneg; auto.
  rewrite <- Hq₁, <- Hq₂.
  symmetry; assumption.

  rewrite Z.abs_eq.
   rewrite Z.div_mul_cancel_l; auto.
    rewrite Hg1, Z.div_1_r, Z.mul_1_r.
    rewrite Z.mul_comm.
    rewrite Z.div_mul; auto.
    unfold normalise_series.
    rewrite series_left_shift_0.
    unfold ps_monom; simpl.
    rewrite fold_series_const.
    constructor; auto; simpl.
    apply series_shrink_const.

    rewrite Hg1; intros H; discriminate H.

   apply Z.mul_nonneg_nonneg; auto.
   rewrite Hg1; apply Z.le_0_1.
Qed.

(* *)

(* f₁(x,y₁) = 0 => f(x,c₁.x^γ+x^γ.y₁) = 0 *)
Lemma f₁_root_f_root : ∀ f f₁ β γ c₁ y y₁,
  f₁ = next_pol f β γ c₁
  → (y = ps_monom c₁ γ + ps_monom 1%K γ * y₁)%ps
  → (ps_pol_apply f₁ y₁ = 0)%ps
  → (ps_pol_apply f y = 0)%ps.
Proof.
intros f f₁ β γ c₁ y y₁ Hpol₁ Hy Happ.
destruct (ps_zerop R 1%ps) as [Hzo| Hnzo].
 apply eq_1_0_all_0; assumption.

 subst f₁.
 unfold next_pol in Happ.
 unfold ps_pol_apply, apply_poly in Happ; simpl in Happ.
 unfold next_lap in Happ; simpl in Happ.
 unfold ps_pol_apply, apply_poly.
 rewrite apply_lap_mul in Happ.
 rewrite apply_lap_compose in Happ.
 simpl in Happ.
 rewrite ps_mul_0_l in Happ.
 do 2 rewrite ps_add_0_l in Happ.
 rewrite ps_add_comm, <- Hy in Happ.
 apply fld_eq_mul_0_r in Happ; [ assumption | apply ps_field | idtac ].
 simpl; intros H.
 apply ps_monom_0_coeff_0 in H.
 apply Hnzo.
 unfold ps_one; rewrite H.
 apply ps_zero_monom_eq.
Qed.

Lemma minimise_slope_end_2nd_pt : ∀ pt₁ pt₂ pts ms,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → snd pt₂ < snd pt₁
    → (∀ pt₃, pt₃ ∈ pts → snd pt₂ <= snd pt₃)
      → ms = minimise_slope pt₁ pt₂ pts
        → end_pt ms = pt₂.
Proof.
intros pt₁ pt₂ pts ms Hsort Hpt₁ Hpt Hms.
revert ms pt₂ Hsort Hpt Hpt₁ Hms.
induction pts as [| pt]; intros.
 simpl in Hms; subst ms; reflexivity.

 simpl in Hms.
 remember (minimise_slope pt₁ pt pts) as ms₁ eqn:Hms₁ .
 remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c eqn:Hc .
 symmetry in Hc.
 remember Hms₁ as Hsl₁; clear HeqHsl₁.
 symmetry in Hsl₁.
 eapply minimised_slope in Hsl₁; [ idtac | reflexivity ].
 rewrite Hsl₁ in Hc.
 remember Hms₁ as Hsnde; clear HeqHsnde.
 symmetry in Hsnde.
 apply end_pt_in in Hsnde.
 remember (end_pt ms₁) as pte eqn:Hpte .
 remember Hsnde as Hein; clear HeqHein.
 apply Hpt in Hsnde.
 apply Qminus_le_compat_r with (z := snd pt₂) in Hsnde.
 rewrite Qminus_diag in Hsnde.
 apply Qminus_lt_compat_r with (z := snd pt₁) in Hpt₁.
 rewrite Qminus_diag in Hpt₁.
 apply Q_div_lt_mono with (c := fst pt₂ - fst pt₁) in Hpt₁.
  unfold Qdiv at 2 in Hpt₁.
  rewrite Qmult_0_l in Hpt₁.
  apply Q_div_le_mono with (c := fst pte - fst pt₂) in Hsnde.
   unfold Qdiv at 1 in Hsnde.
   rewrite Qmult_0_l in Hsnde.
   destruct c; subst ms; [ simpl | reflexivity | simpl ].
    apply Qlt_not_le in Hpt₁.
    apply Qeq_alt in Hc.
    eapply slope_expr_eq in Hc; try eassumption.
    unfold slope_expr in Hc.
    rewrite Hc in Hpt₁; contradiction.

    apply Qgt_alt in Hc.
    remember Hc as Hd; clear HeqHd.
    apply slope_lt_1312_2313 in Hc.
     eapply Qlt_trans in Hd; [ idtac | eassumption ].
     eapply Qlt_trans in Hpt₁; [ idtac | eassumption ].
     apply Qlt_not_le in Hpt₁.
     contradiction.

     split.
      apply Sorted_inv in Hsort.
      destruct Hsort as (_, Hrel).
      apply HdRel_inv in Hrel.
      assumption.

      apply Sorted_inv_1 in Hsort.
      eapply Sorted_hd; eassumption.

   apply Qlt_minus.
   apply Sorted_inv_1 in Hsort.
   eapply Sorted_hd; eassumption.

  apply Qlt_minus.
  apply Sorted_inv in Hsort.
  destruct Hsort as (_, Hrel).
  apply HdRel_inv in Hrel.
  assumption.
Qed.

Lemma minimise_slope_2_pts : ∀ ms pt₁ pt₂ pts,
  ms = minimise_slope pt₁ pt₂ pts
  → pt₂ ∉ pts
  → end_pt ms = pt₂
  → seg ms = [].
Proof.
intros ms pt₁ pt₂ pts Hms Hnin Hend.
revert ms pt₂ Hms Hnin Hend.
induction pts as [| pt]; intros; [ subst ms; reflexivity | idtac ].
simpl in Hms.
remember (minimise_slope pt₁ pt pts) as ms₁.
remember (slope_expr pt₁ pt₂ ?= slope ms₁) as c.
symmetry in Heqc.
destruct c.
 subst ms; simpl in Hend; simpl.
 symmetry in Heqms₁.
 apply end_pt_in in Heqms₁.
 rewrite Hend in Heqms₁; contradiction.

 subst ms; reflexivity.

 subst ms; simpl in Hend; simpl.
 symmetry in Heqms₁.
 apply end_pt_in in Heqms₁.
 rewrite Hend in Heqms₁; contradiction.
Qed.

Lemma pouet : ∀ f ffo ms a₀ a₁ la v₀ v₁ j k αj αk,
  f = pair_rec (λ pow ps, (Qnat pow, ps))
  → ffo = filter_finite_ord R (List.map f (power_list 2 la))
  → ms = minimise_slope (Qnat 0, v₀) (Qnat 1, v₁) ffo
  → (∀ i : nat, (order (List.nth i [a₀; a₁ … la] 0%ps) ≥ 0)%Qbar)
  → v₁ == 0
  → 0 < v₀
  → (Qnat 0, v₀) = (Qnat j, αj)
  → end_pt ms = (Qnat k, αk)
  → (j = 0)%nat ∧ (j < k)%nat ∧ (k ≤ 1)%nat ∧ 0 < αj ∧ αk == 0 ∧ seg ms = [].
Proof.
intros f ffo ms a₀ a₁ la v₀ v₁ j k αj αk.
intros Heqf Heqffo Heqms Hnneg Hz Hpos Hini Hfin.
remember Heqms as Hms; clear HeqHms.
apply minimise_slope_end_2nd_pt in Heqms.
 rewrite Heqms in Hfin.
 injection Hini; clear Hini; intros; subst αj.
 injection Hfin; clear Hfin; intros; subst αk.
 apply Z2Nat.inj_iff in H0; [ idtac | reflexivity | apply Nat2Z.is_nonneg ].
 apply Z2Nat.inj_iff in H1; [ idtac | idtac | apply Nat2Z.is_nonneg ].
  rewrite Nat2Z.id in H0, H1.
  simpl in H0, H1.
  rewrite Pos2Nat.inj_1 in H1.
  subst j k.
  split; [ reflexivity | idtac ].
  split; [ apply Nat.lt_0_1 | idtac ].
  split; [ reflexivity | idtac ].
  split; [ assumption | idtac ].
  split; [ assumption | idtac ].
  eapply minimise_slope_2_pts; try eassumption.
  subst ffo; revert Heqf; clear; intros.
  remember 2%nat as pow.
  assert (2 <= pow)%nat as Hpow by (subst pow; reflexivity).
  clear Heqpow.
  revert pow Hpow.
  induction la as [| a]; intros; [ intros H; assumption | simpl ].
  rewrite Heqf; simpl; rewrite <- Heqf.
  destruct (order a) as [v| ].
   intros H; simpl in H.
   destruct H as [H| H].
    injection H; clear H; intros; subst v.
    apply Z2Nat.inj_iff in H0.
     rewrite Nat2Z.id in H0; simpl in H0.
     unfold Pos.to_nat in H0; simpl in H0.
     rewrite H0 in Hpow.
     apply Nat.nlt_ge in Hpow.
     apply Hpow, Nat.lt_1_2.

     apply Nat2Z.is_nonneg.

     apply Z.le_0_1.

    revert H; apply IHla.
    apply Nat.le_le_succ_r; assumption.

   apply IHla.
   apply Nat.le_le_succ_r; assumption.

  apply Z.le_0_1.

 subst ffo; revert Heqf; clear; intros.
 constructor.
  remember 2%nat as pow.
  assert (1 < pow)%nat as Hpow by (subst pow; apply Nat.lt_1_2).
  clear Heqpow.
  remember 1%nat as n.
  clear Heqn.
  revert n v₁ pow Hpow.
  induction la as [| a]; intros.
   constructor; [ constructor; constructor | constructor ].

   unfold fst_lt; simpl.
   rewrite Heqf; simpl; rewrite <- Heqf.
   destruct (order a) as [v| ].
    constructor.
     apply IHla, Nat.lt_succ_r; reflexivity.

     constructor.
     unfold fst_lt; simpl.
     apply Qnat_lt; assumption.

    apply IHla, Nat.lt_lt_succ_r; assumption.

  constructor.
  unfold fst_lt; simpl.
  apply Qnat_lt, Nat.lt_0_1.

 simpl.
 rewrite Hz; assumption.

 intros pt Hpt; simpl; rewrite Hz.
 rewrite Heqffo in Hpt.
 revert Heqf Hnneg Hpt; clear; intros.
 remember 2%nat as pow; clear Heqpow.
 revert pow Hpt.
 induction la as [| a]; intros; [ contradiction | idtac ].
 simpl in Hpt.
 rewrite Heqf in Hpt; simpl in Hpt; rewrite <- Heqf in Hpt.
 remember (order a) as v.
 symmetry in Heqv.
 destruct v as [v| ].
  simpl in Hpt.
  destruct Hpt as [Hpt| Hpt].
   subst pt; simpl.
   pose proof (Hnneg 2%nat) as H; simpl in H.
   rewrite Heqv in H.
   apply Qbar.qfin_le_mono; assumption.

   eapply IHla; [ intros i | eassumption ].
   revert Hnneg; clear; intros.
   revert la Hnneg.
   induction i; intros; simpl.
    pose proof (Hnneg 0%nat); assumption.

    destruct i; [ pose proof (Hnneg 1%nat); assumption | idtac ].
    pose proof (Hnneg (3 + i)%nat) as H; assumption.

  eapply IHla; [ intros i | eassumption ].
  revert Hnneg; clear; intros.
  revert la Hnneg.
  induction i; intros; simpl.
   pose proof (Hnneg 0%nat); assumption.

   destruct i; [ pose proof (Hnneg 1%nat); assumption | idtac ].
   pose proof (Hnneg (3 + i)%nat) as H; assumption.
Qed.

Lemma r_1_j_0_k_1 : ∀ pol ns c₁ pol₁ ns₁ j₁ αj₁ k₁ αk₁ m,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ini_pt ns₁ = (Qnat j₁, αj₁)
  → fin_pt ns₁ = (Qnat k₁, αk₁)
  → j₁ = 0%nat ∧ k₁ = 1%nat ∧ αj₁ > 0 ∧ αk₁ == 0 ∧ oth_pts ns₁ = [].
Proof.
intros pol ns c₁ pol₁ ns₁ j₁ αj₁ k₁ αk₁ m.
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

Lemma minimise_slope_seg_cons : ∀ pt₁ pt₂ pt₃ pts,
  slope_expr pt₁ pt₂ < slope (minimise_slope pt₁ pt₃ pts)
  → seg (minimise_slope pt₁ pt₂ [pt₃ … pts]) = [].
Proof.
intros pt₁ pt₂ pt₃ pts H.
apply -> Qlt_alt in H.
simpl; rewrite H; reflexivity.
Qed.

Lemma no_pts_order_inf : ∀ la,
  points_of_ps_lap la = []
  → order (List.nth 0 la 0%ps) = ∞%Qbar.
Proof.
intros la H.
destruct la as [| a]; [ apply order_0 | idtac ].
unfold points_of_ps_lap in H.
unfold points_of_ps_lap_gen in H.
simpl in H; simpl.
remember (order a) as oa eqn:Hoa .
symmetry in Hoa.
destruct oa; [ discriminate H | reflexivity ].
Qed.

Lemma one_pt_order_inf : ∀ la pt,
  points_of_ps_lap la = [pt]
  → (order (List.nth 1 la 0%ps) = 0)%Qbar
  → order (List.nth 0 la 0%ps) = ∞%Qbar.
Proof.
intros la pt Hpts Hz.
destruct la as [| a₀]; [ apply order_0 | simpl ].
unfold points_of_ps_lap in Hpts.
unfold points_of_ps_lap_gen in Hpts.
simpl in Hpts, Hz.
remember (order a₀) as oa₀ eqn:Hoa₀ .
destruct oa₀ as [oa₀| ]; [ idtac | reflexivity ].
destruct la as [| a₁]; simpl in Hz.
 rewrite order_0 in Hz; inversion Hz.

 simpl in Hpts.
 remember (order a₁) as oa₁ eqn:Hoa₁ .
 destruct oa₁ as [oa₁| ]; [ idtac | inversion Hz ].
 discriminate Hpts.
Qed.

Lemma pow_ord_of_point : ∀ la pt pow,
  pt ∈ points_of_ps_lap_gen pow la
  → ∃ n,
    fst pt = Qnat (pow + n)
    ∧ qfin (snd pt) = order (ps_lap_nth n la).
Proof.
intros la pt pow Hpt.
revert pow Hpt.
induction la as [| a]; intros; [ contradiction | idtac ].
unfold points_of_ps_lap_gen in Hpt.
simpl in Hpt.
remember (order a) as oa eqn:Hoa .
symmetry in Hoa.
rewrite fold_qpower_list in Hpt.
rewrite fold_points_of_ps_lap_gen in Hpt.
destruct oa as [oa| ].
 destruct Hpt as [Hpt| Hpt].
  subst pt; simpl.
  unfold ps_lap_nth.
  symmetry in Hoa.
  exists 0%nat; split; [ rewrite Nat.add_comm; reflexivity | assumption ].

  apply IHla in Hpt.
  destruct Hpt as (m, (Hpow, Hord)).
  rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hpow.
  unfold ps_lap_nth in Hord.
  unfold ps_lap_nth.
  exists (S m); split; assumption.

 apply IHla in Hpt.
 destruct Hpt as (m, (Hpow, Hord)).
 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hpow.
 unfold ps_lap_nth in Hord.
 unfold ps_lap_nth.
 exists (S m); split; assumption.
Qed.

Lemma exists_ini_pt_nat_fst_seg : ∀ pol ns,
  ns = List.hd phony_ns (newton_segments pol)
  → ∃ i αi, ini_pt ns = (Qnat i, αi).
Proof.
intros pol ns Hns.
remember (newton_segments pol) as nsl eqn:Hnsl .
symmetry in Hnsl.
destruct nsl as [| ns₁].
 subst ns; simpl.
 exists 0%nat, 0; reflexivity.

 simpl in Hns; subst ns₁.
 eapply exists_ini_pt_nat with (pol := pol).
 rewrite Hnsl; left; reflexivity.
Qed.

Lemma exists_fin_pt_nat_fst_seg : ∀ pol ns,
  ns = List.hd phony_ns (newton_segments pol)
  → ∃ i αi, fin_pt ns = (Qnat i, αi).
Proof.
intros pol ns Hns.
remember (newton_segments pol) as nsl eqn:Hnsl .
symmetry in Hnsl.
destruct nsl as [| ns₁].
 subst ns; simpl.
 exists 0%nat, 0; reflexivity.

 simpl in Hns; subst ns₁.
 eapply exists_fin_pt_nat with (pol := pol).
 rewrite Hnsl; left; reflexivity.
Qed.

Lemma multiplicity_1_remains : ∀ pol ns c₁ c₂ pol₁ ns₁ m,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → c₂ = ac_root (Φq pol₁ ns₁)
  → root_multiplicity acf c₂ (Φq pol₁ ns₁) = 1%nat.
Proof.
intros pol ns c₁ c₂ pol₁ ns₁ m.
intros Hns Hm Hc₁ Hr Hpol₁ Hps₀ Hns₁ Hc₂.
apply order_fin in Hps₀.
remember Hns as H; clear HeqH.
symmetry in Hr.
eapply f₁_orders in H; try eassumption.
destruct H as (Hnneg, (Hpos, Hz)).
symmetry in Hr.
unfold root_multiplicity; simpl.
rewrite Nat.sub_diag; simpl.
rewrite skipn_pad; simpl.
remember (al pol₁) as la eqn:Hla .
unfold term_of_point; rewrite <- Hla.
unfold next_pol in Hpol₁.
remember Hla as H; clear HeqH.
rewrite Hpol₁ in H; simpl in H.
clear Hpol₁; rename H into Hpol₁.
unfold ps_poly_nth in Hps₀; rewrite <- Hla in Hps₀.
unfold newton_segments, points_of_ps_polynom in Hns₁; rewrite <- Hla in Hns₁.
unfold Φq, summation_ah_xh_pol, characteristic_polynomial in Hc₂.
unfold term_of_point in Hc₂; rewrite <- Hla in Hc₂.
unfold ps_poly_nth in Hnneg; rewrite <- Hla in Hnneg.
unfold ps_poly_nth in Hpos; rewrite <- Hla in Hpos.
unfold ps_poly_nth in Hz; rewrite <- Hla in Hz.
unfold ps_lap_nth in Hnneg, Hpos, Hz, Hps₀.
assert (0 < 1)%nat as Hp by apply Nat.lt_0_1.
apply Hpos in Hp; simpl in Hp.
clear Hpos; rename Hp into Hpos.
remember (points_of_ps_lap la) as pts eqn:Hpts .
unfold points_of_ps_lap in Hpts.
unfold points_of_ps_lap_gen in Hpts.
clear pol₁ Hla; simpl in Hc₂.
unfold poly_left_shift in Hc₂; simpl in Hc₂.
rewrite skipn_pad, Nat.sub_diag, list_pad_0 in Hc₂.
assert (nat_num (fst (ini_pt ns₁)) = 0)%nat as Hini.
 destruct pts as [| pt₁]; [ subst ns₁; reflexivity | idtac ].
 destruct pts as [| pt₂]; [ subst ns₁; reflexivity | idtac ].
 unfold lower_convex_hull_points in Hns₁.
 rewrite Hns₁; simpl.
 rewrite minimised_slope_beg_pt.
 destruct la as [| a₁]; [ discriminate Hpts | idtac ].
 simpl in Hpts.
 unfold ps_lap_nth in Hps₀; simpl in Hps₀.
 remember (order a₁) as o₁ eqn:Ho₁ .
 symmetry in Ho₁.
 destruct o₁ as [o₁| ]; [ idtac | exfalso; apply Hps₀; reflexivity ].
 injection Hpts; clear Hpts; intros Hpts Hpt₁.
 subst pt₁; reflexivity.

 rewrite Hini in Hc₂; rewrite Hini.
 assert (oth_pts ns₁ = []) as Hoth.
  symmetry in Hpts.
  destruct pts as [| pt₁].
   exfalso; apply Hps₀, no_pts_order_inf; assumption.

   destruct pts as [| pt₂].
    apply one_pt_order_inf in Hpts; [ contradiction | assumption ].

    unfold lower_convex_hull_points in Hns₁.
    rewrite Hns₁; simpl.
    destruct la as [| a₁]; [ discriminate Hpts | simpl in Hpts ].
    unfold ps_lap_nth in Hps₀; simpl in Hps₀.
    simpl in Hpos.
    remember (order a₁) as o₁ eqn:Ho₁ .
    symmetry in Ho₁.
    destruct o₁ as [o₁| ]; [ idtac | exfalso; apply Hps₀; reflexivity ].
    apply Qbar.qfin_lt_mono in Hpos.
    injection Hpts; clear Hpts; intros Hpts Hpt₁; simpl in Hz.
    destruct la as [| a₂]; [ discriminate Hpts | idtac ].
    simpl in Hpts, Hz.
    remember (order a₂) as o₂ eqn:Ho₂ .
    symmetry in Ho₂.
    destruct o₂ as [o₂| ]; [ apply Qbar.qfin_inj in Hz | inversion Hz ].
    injection Hpts; clear Hpts; intros Hpts Hpt₂.
    subst pt₁ pt₂.
revert Hnneg Hpos Hz Hpts; clear; intros.
    destruct pts as [| pt₁]; [ reflexivity | idtac ].
    rewrite minimise_slope_seg_cons; [ reflexivity | idtac ].
    unfold slope; simpl.
    rewrite minimised_slope_beg_pt.
    unfold Qnat; simpl.
    unfold slope_expr; simpl.
    rewrite Hz.
    rewrite Q_sub_0_l, Q_sub_0_r, Q_sub_0_r, Q_div_1_r.
    remember (minimise_slope (0, o₁) pt₁ pts) as ms eqn:Hms .
    remember (end_pt ms) as pt eqn:Hend .
    symmetry in Hend.
    destruct pt as (pow, ord); simpl.
    assert (pow >= Qnat 2) as Hp2.
     revert Hpts Hms Hend; clear; intros.
     remember 2 as n.
     assert (2 ≤ n)%nat as Hn by (subst n; reflexivity).
     clear Heqn.
     revert o₁ pt₁ pts ms pow ord n Hpts Hms Hend Hn.
     induction la as [| a]; intros; [ discriminate Hpts | idtac ].
     destruct n.
      exfalso; apply Nat.nle_gt in Hn; apply Hn, Nat.le_0_1.

      simpl in Hpts.
      remember (order a) as oa eqn:Hoa .
      symmetry in Hoa.
      destruct oa as [oa| ].
       injection Hpts; clear Hpts; intros Hpts Hpt₁; subst pt₁.
       destruct pts as [| pt₁].
        simpl in Hms.
        subst ms; simpl in Hend.
        injection Hend; clear Hend; intros; subst pow; apply Qle_refl.

        simpl in Hms.
        remember (minimise_slope (0, o₁) pt₁ pts) as ms₁ eqn:Hms₁ .
        remember (slope_expr (0, o₁) (Qnat (S n), oa) ?= slope ms₁) as c
         eqn:Hc .
        symmetry in Hc.
        destruct c.
         rewrite Hms in Hend; simpl in Hend.
         eapply IHla in Hpts; try eassumption.
          eapply Qle_trans; [ idtac | eassumption ].
          apply Qnat_le, le_n_S, Nat.le_succ_diag_r.

          apply Nat.le_le_succ_r; assumption.

         rewrite Hms in Hend; simpl in Hend.
         injection Hend; clear Hend; intros; subst pow; apply Qle_refl.

         move Hms at top; subst ms₁.
         eapply IHla in Hpts; try eassumption.
          eapply Qle_trans; [ idtac | eassumption ].
          apply Qnat_le, le_n_S, Nat.le_succ_diag_r.

          apply Nat.le_le_succ_r; assumption.

       eapply IHla in Hpts; try eassumption.
        eapply Qle_trans; [ idtac | eassumption ].
        apply Qnat_le, le_n_S, Nat.le_succ_diag_r.

        apply Nat.le_le_succ_r; assumption.

     assert (ord >= 0) as Hop.
      revert Hnneg Hpts Hms Hend; clear; intros.
      remember 2 as n.
      assert (2 ≤ n)%nat as Hn by (subst n; reflexivity).
      clear Heqn.
      revert o₁ pt₁ pts ms pow ord n Hpts Hms Hend Hn.
      induction la as [| a]; intros; [ discriminate Hpts | idtac ].
      destruct n.
       exfalso; apply Nat.nle_gt in Hn; apply Hn, Nat.le_0_1.

       simpl in Hpts.
       remember (order a) as oa eqn:Hoa .
       symmetry in Hoa.
       destruct oa as [oa| ].
        injection Hpts; clear Hpts; intros Hpts Hpt₁; subst pt₁.
        destruct pts as [| pt₁].
         simpl in Hms.
         subst ms; simpl in Hend.
         injection Hend; clear Hend; intros; subst pow oa.
         pose proof (Hnneg 2) as H.
         simpl in H.
         rewrite Hoa in H.
         apply Qbar.qfin_le_mono; assumption.

         simpl in Hms.
         remember (minimise_slope (0, o₁) pt₁ pts) as ms₁ eqn:Hms₁ .
         remember (slope_expr (0, o₁) (Qnat (S n), oa) ?= slope ms₁) as c
          eqn:Hc .
         symmetry in Hc.
         destruct c.
          rewrite Hms in Hend; simpl in Hend.
          eapply IHla in Hpts; try eassumption.
           intros i.
           destruct i; simpl.
            pose proof (Hnneg 0%nat); assumption.

            destruct i.
             pose proof (Hnneg 1%nat); assumption.

             pose proof (Hnneg (3 + i)%nat) as H; assumption.

           apply Nat.le_le_succ_r; assumption.

          rewrite Hms in Hend; simpl in Hend.
          injection Hend; clear Hend; intros; subst pow.
          subst oa.
          pose proof (Hnneg 2) as H; simpl in H.
          rewrite Hoa in H.
          apply Qbar.qfin_le_mono; assumption.

          move Hms at top; subst ms₁.
          eapply IHla in Hpts; try eassumption.
           intros i.
           destruct i; simpl.
            pose proof (Hnneg 0%nat); assumption.

            destruct i.
             pose proof (Hnneg 1%nat); assumption.

             pose proof (Hnneg (3 + i)%nat) as H; assumption.

           apply Nat.le_le_succ_r; assumption.

        eapply IHla in Hpts; try eassumption.
         intros i.
         destruct i; simpl.
          pose proof (Hnneg 0%nat); assumption.

          destruct i.
           pose proof (Hnneg 1%nat); assumption.

           pose proof (Hnneg (3 + i)%nat) as H; assumption.

         apply Nat.le_le_succ_r; assumption.

      revert Hpos Hp2 Hop; clear; intros.
      rewrite <- Qopp_minus, <- Q_div_opp_opp, Q_div_opp_r.
      apply Qopp_lt_compat.
      rewrite Qopp_opp.
      apply Qle_lt_trans with (y := o₁ / pow).
       apply Q_div_le_mono.
        eapply Qlt_le_trans; [ idtac | eassumption ].
        replace 0 with (Qnat 0) by reflexivity.
        apply Qnat_lt, Nat.lt_0_succ.

        apply Qle_sub_le_add_l.
        assert (0 + o₁ == o₁) as H by apply Qplus_0_l.
        rewrite <- H in |- * at 1.
        apply Qplus_le_l; assumption.

       apply Qlt_shift_div_r.
        eapply Qlt_le_trans; [ idtac | eassumption ].
        replace 0 with (Qnat 0) by reflexivity.
        apply Qnat_lt, Nat.lt_0_succ.

        rewrite <- Qmult_1_r in |- * at 1.
        apply Qmult_lt_l; [ assumption | idtac ].
        eapply Qlt_le_trans; [ idtac | eassumption ].
        replace 1 with (Qnat 1) by reflexivity.
        apply Qnat_lt, Nat.lt_succ_r; reflexivity.

  rewrite Hoth; simpl.
  assert (nat_num (fst (fin_pt ns₁)) = 1)%nat as Hfin.
   symmetry in Hpts.
   destruct pts as [| pt₁].
    exfalso; apply Hps₀, no_pts_order_inf; assumption.

    destruct pts as [| pt₂].
     apply one_pt_order_inf in Hpts; [ contradiction | assumption ].

     unfold lower_convex_hull_points in Hns₁.
     rewrite Hns₁; simpl.
     destruct la as [| a₁]; [ discriminate Hpts | simpl in Hpts ].
     unfold ps_lap_nth in Hps₀; simpl in Hps₀.
     simpl in Hpos.
     remember (order a₁) as o₁ eqn:Ho₁ .
     symmetry in Ho₁.
     destruct o₁ as [o₁| ]; [ idtac | exfalso; apply Hps₀; reflexivity ].
     apply Qbar.qfin_lt_mono in Hpos.
     injection Hpts; clear Hpts; intros Hpts Hpt₁; simpl in Hz.
     destruct la as [| a₂]; [ discriminate Hpts | idtac ].
     simpl in Hpts, Hz.
     remember (order a₂) as o₂ eqn:Ho₂ .
     symmetry in Ho₂.
     destruct o₂ as [o₂| ]; [ apply Qbar.qfin_inj in Hz | inversion Hz ].
     injection Hpts; clear Hpts; intros Hpts Hpt₂.
     subst pt₁ pt₂.
     remember (minimise_slope (Qnat 0, o₁) (Qnat 1, o₂) pts) as ms eqn:Hms .
     destruct pts as [| pt₁]; [ subst ms; reflexivity | idtac ].
     simpl in Hpts, Hms.
     remember (minimise_slope (Qnat 0, o₁) pt₁ pts) as ms₁ eqn:Hms₁ .
     unfold slope_expr in Hms; simpl in Hms.
     unfold Qnat in Hms; simpl in Hms.
     rewrite Q_sub_0_r, Q_div_1_r in Hms.
     rewrite Hz, Q_sub_0_l in Hms.
     unfold slope in Hms.
     rewrite Hms₁ in Hms at 1.
     rewrite minimised_slope_beg_pt in Hms.
     unfold slope_expr, Qnat in Hms; simpl in Hms.
     rewrite Q_sub_0_r in Hms.
     remember (end_pt ms₁) as p eqn:Hp .
     symmetry in Hp.
     destruct p as (pow, ord); simpl in Hms.
     remember (- o₁ ?= (ord - o₁) / pow) as c eqn:Hc .
     symmetry in Hc.
     destruct c.
      subst ms; simpl.
      apply Qeq_alt in Hc.
      symmetry in Hc.
      apply Qeq_shift_mult_l in Hc.
       apply Qminus_eq_eq_plus_r in Hc.
       setoid_replace (- o₁ * pow + o₁) with (- o₁ * (pow - 1)) in Hc by
        ring.
       remember Hms₁ as Hend; clear HeqHend.
       symmetry in Hend.
       apply end_pt_in in Hend.
       rewrite fold_qpower_list in Hpts.
       rewrite fold_points_of_ps_lap_gen in Hpts.
       rewrite <- Hpts in Hend.
       apply pow_ord_of_point in Hend.
       destruct Hend as (n, (Hpow, Hord)).
       rewrite Hp in Hpow; simpl in Hpow.
       rewrite Hp in Hord; simpl in Hord.
       assert (qfin ord ≥ 0)%Qbar as Hop.
        rewrite Hord.
        pose proof (Hnneg (2 + n)%nat) as H; assumption.

        rewrite Hc in Hop.
        apply Qbar.qfin_le_mono in Hop.
        rewrite Qmult_opp_l in Hop.
        apply Qopp_le_compat in Hop.
        rewrite Qopp_opp in Hop.
        apply Qle_not_lt in Hop.
        exfalso; apply Hop.
        unfold Qopp at 1; simpl.
        rewrite Hpow; simpl.
        rewrite <- Qnat_1.
        rewrite <- Qnat_inj_sub; [ simpl | apply le_n_S, Nat.le_0_l ].
        apply Q_mul_pos_pos; [ assumption | idtac ].
        rewrite <- Qnat_0.
        apply Qnat_lt, Nat.lt_0_succ.

       remember Hms₁ as Hend; clear HeqHend.
       symmetry in Hend.
       apply end_pt_in in Hend.
       rewrite fold_qpower_list in Hpts.
       rewrite fold_points_of_ps_lap_gen in Hpts.
       rewrite <- Hpts in Hend.
       apply pow_ord_of_point in Hend.
       destruct Hend as (n, (Hpow, Hord)).
       rewrite Hp in Hpow; simpl in Hpow.
       rewrite Hp in Hord; simpl in Hord.
       rewrite Hpow.
       rewrite <- Qnat_0.
       unfold Qnat, Qeq; simpl.
       apply Pos2Z_ne_0.

      subst ms; reflexivity.

      move Hms at top; subst ms₁.
      rewrite Hp; simpl.
      apply Qgt_alt in Hc.
      remember Hms₁ as Hend; clear HeqHend.
      symmetry in Hend.
      apply end_pt_in in Hend.
      rewrite fold_qpower_list in Hpts.
      rewrite fold_points_of_ps_lap_gen in Hpts.
      rewrite <- Hpts in Hend.
      apply pow_ord_of_point in Hend.
      destruct Hend as (n, (Hpow, Hord)).
      rewrite Hp in Hpow; simpl in Hpow.
      rewrite Hp in Hord; simpl in Hord.
      apply Qlt_shift_mult_l in Hc.
       apply Qminus_lt_lt_plus_r in Hc.
       setoid_replace (- o₁ * pow + o₁) with (o₁ * (1 - pow)) in Hc by ring.
       eapply Qlt_trans with (z := 0) in Hc.
        pose proof (Hnneg (2 + n)%nat) as H; simpl in H.
        rewrite fold_ps_lap_nth in H.
        rewrite <- Hord in H.
        apply Qbar.qfin_le_mono in H.
        apply Qlt_not_le in Hc; contradiction.

        rewrite <- Qopp_opp.
        setoid_replace 0 with (- 0) by reflexivity.
        apply Qopp_lt_compat.
        rewrite <- Qmult_opp_r.
        rewrite Qopp_minus, Hpow, <- Qnat_1.
        rewrite <- Qnat_inj_sub; [ simpl | apply le_n_S, Nat.le_0_l ].
        apply Q_mul_pos_pos; [ assumption | idtac ].
        rewrite <- Qnat_0.
        apply Qnat_lt, Nat.lt_0_succ.

       rewrite Hpow.
       rewrite <- Qnat_0.
       apply Qnat_lt, Nat.lt_0_succ.

   rewrite Hfin; simpl.
   rewrite Hoth in Hc₂; simpl in Hc₂.
   rewrite Hfin in Hc₂; simpl in Hc₂.
   remember
    [order_coeff (List.nth 0 la 0%ps); order_coeff (List.nth 1 la 0%ps) … []]%pol as la₂.
   remember POL la₂%pol as pol₂ eqn:Hpol₂ .
   assert (order_coeff (List.nth 1 la 0%ps) ≠ 0)%K as Hnz.
    intros Hoc₁.
    move Hz at bottom.
    unfold order_coeff in Hoc₁.
    unfold order in Hz.
    remember (ps_terms (List.nth 1 la 0%ps)) as s.
    remember (null_coeff_range_length R s 0) as v eqn:Hv .
    destruct v as [v| ].
     apply Qbar.qfin_inj in Hz.
     symmetry in Hv.
     apply null_coeff_range_length_iff in Hv.
     unfold null_coeff_range_length_prop in Hv.
     simpl in Hv.
     destruct Hv as (Hvi, Hv).
     rewrite Hoc₁ in Hv.
     apply Hv; reflexivity.

     inversion Hz.

    assert (degree ac_zerop pol₂ ≥ 1)%nat as Hpol.
     subst pol₂ la₂.
     unfold degree; simpl.
     remember (order_coeff (List.nth 1 la 0%ps)) as oc₁ eqn:Hoc₁ .
     symmetry in Hoc₁.
     destruct (ac_zerop oc₁) as [| Hne]; [ contradiction | idtac ].
     apply Nat.le_refl.

     apply ac_prop_root in Hpol.
     rewrite <- Hc₂, Hpol₂ in Hpol.
     unfold apply_poly in Hpol; simpl in Hpol.
     destruct (ac_zerop (lap_mod_deg_1 la₂ c₂)) as [Heq| Hne].
      apply eq_S.
      destruct (ac_zerop (lap_mod_deg_1 (lap_div_deg_1 la₂ c₂) c₂))
       as [Heq₁| ]; [ idtac | reflexivity ].
      apply lap_mod_deg_1_apply in Heq₁.
      rewrite Heqla₂ in Heq₁; simpl in Heq₁.
      rewrite rng_mul_0_l in Heq₁.
      do 2 rewrite rng_add_0_l in Heq₁.
      contradiction.

      apply apply_lap_mod_deg_1 in Hpol.
      contradiction.
Qed.

Lemma r_1_next_ns : ∀ pol ns c pol₁ ns₁ m,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → ∃ αj αk,
    oth_pts ns₁ = [] ∧
    ini_pt ns₁ = (Qnat 0, αj) ∧
    fin_pt ns₁ = (Qnat 1, αk) ∧
    (0 < Qnum αj)%Z ∧
    Qnum αk = 0%Z.
Proof.
intros pol ns c pol₁ ns₁ m Hns Hm Hr Hc Hpol₁ Hns₁ Hpnz.
remember Hns₁ as H; clear HeqH.
apply exists_ini_pt_nat_fst_seg in H.
destruct H as (j₁, (αj₁, Hini₁)).
remember Hns₁ as H; clear HeqH.
apply exists_fin_pt_nat_fst_seg in H.
destruct H as (k₁, (αk₁, Hfin₁)).
remember Hns₁ as H; clear HeqH.
eapply r_1_j_0_k_1 in H; eauto .
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁.
unfold Qlt in Hαj₁; simpl in Hαj₁.
unfold Qeq in Hαk₁; simpl in Hαk₁.
rewrite Z.mul_1_r in Hαj₁, Hαk₁.
exists αj₁, αk₁; auto.
Qed.

Lemma hd_newton_segments : ∀ pol ns j k αj αk,
  ns = List.hd phony_ns (newton_segments pol)
 → ini_pt ns = (Qnat j, αj)
  → fin_pt ns = (Qnat k, αk)
  → (j < k)%nat
  → ns ∈ newton_segments pol.
Proof.
intros pol ns j k αj αk Hns Hini Hfin Hjk.
remember (newton_segments pol) as nsl.
symmetry in Heqnsl.
destruct nsl as [| ns₁]; simpl in Hns.
 subst ns; simpl in Hini, Hfin.
 injection Hini; intros; subst.
 injection Hfin; intros; subst.
 rewrite <- Nat2Z.inj_0 in H0.
 rewrite <- Nat2Z.inj_0 in H1.
 apply Nat2Z.inj in H0.
 apply Nat2Z.inj in H1.
 subst j k; exfalso; revert Hjk; apply Nat.lt_irrefl.

 subst ns; left; reflexivity.
Qed.

Lemma q_eq_1 : ∀ pol ns pol₁ ns₁ c₁ m q₀,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → ps_lap_forall (λ a, in_K_1_m a (m * q₀)) (al pol₁)
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → q_of_m (m * q₀) (γ ns₁) = 1%positive.
Proof.
intros pol ns pol₁ ns₁ c₁ m q₀ Hns Hm Hq₀ Hc₁ Hr Hpol₁ Hns₁ Hps₀.
remember Hns₁ as Hini₁; clear HeqHini₁.
apply exists_ini_pt_nat_fst_seg in Hini₁.
destruct Hini₁ as (j₁, (αj₁, Hini₁)).
remember Hns₁ as Hfin₁; clear HeqHfin₁.
apply exists_fin_pt_nat_fst_seg in Hfin₁.
destruct Hfin₁ as (k₁, (αk₁, Hfin₁)).
remember Hns as H; clear HeqH.
eapply r_1_j_0_k_1 in H; try eassumption.
destruct H as (Hj₁, (Hk₁, (Hαj₁, (Hαk₁, Hoth₁)))).
subst j₁ k₁; simpl.
unfold Qlt in Hαj₁; simpl in Hαj₁.
unfold Qeq in Hαk₁; simpl in Hαk₁.
rewrite Z.mul_1_r in Hαj₁, Hαk₁.
eapply hd_newton_segments in Hns₁; eauto .
remember Hns₁ as Hqhj; clear HeqHqhj.
remember (Pos.to_nat (q_of_m (m * q₀) (γ ns₁))) as q.
eapply q_is_factor_of_h_minus_j in Hqhj; eauto .
 2: apply List.in_or_app; right; left; symmetry; eauto .

 simpl in Hqhj.
 destruct Hqhj as (c, Hc).
 symmetry in Hc.
 apply Nat.eq_mul_1 in Hc.
 move Hc at top; destruct Hc; subst c q.
 symmetry in Heqq.
 rewrite <- Pos2Nat.inj_1 in Heqq.
 apply Pos2Nat.inj in Heqq.
 assumption.
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

Lemma r_1_nth_ns : ∀ pol ns c pol₁ ns₁ m,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
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
intros pol ns c pol₁ ns₁ m Hns Hm Hc Hr Hpol₁ Hns₁.
intros n poln nsn Hpsi Hpoln Hnsn.
remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀.
revert poln nsn Hpsi Hpoln Hnsn.
revert pol ns c pol₁ ns₁ m q₀ Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁.
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
 eapply IHn with (ns := ns₁) (m := (m * q₀)%positive); eauto .
  eapply next_pol_in_K_1_mq with (ns := ns); eauto .

  intros i Hin.
  apply Nat.succ_le_mono in Hin.
  apply Hpsi in Hin; simpl in Hin.
  rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
  assumption.
Qed.

Lemma multiplicity_1_remains_in_nth : ∀ pol ns c₁ pol₁ ns₁ m,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ∀ n poln nsn cn,
  (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
  → poln = nth_pol n pol₁ ns₁
  → nsn = nth_ns n pol₁ ns₁
  → cn = ac_root (Φq poln nsn)
  → root_multiplicity acf cn (Φq poln nsn) = 1%nat.
Proof.
intros pol ns c pol₁ ns₁ m Hns Hm Hc Hr Hpol₁ Hns₁.
intros n poln nsn cn Hpsi Hpoln Hnsn Hcn.
revert poln nsn cn Hpsi Hpoln Hnsn Hcn.
revert pol ns c pol₁ ns₁ m Hns Hm Hc Hr Hpol₁ Hns₁.
induction n; intros.
 simpl in Hpoln, Hnsn; subst poln nsn; simpl.
 eapply multiplicity_1_remains; eauto .
 pose proof (Hpsi O (le_refl O)) as H; assumption.

 simpl in Hpoln, Hnsn; subst poln nsn; simpl.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 remember (nth_pol n pol₂ ns₂) as poln₂ eqn:Hpoln₂ .
 remember Hr as Hr₁; clear HeqHr₁.
 eapply multiplicity_1_remains with (ns₁ := ns₁) in Hr₁; try eassumption.
  remember Hns₁ as H; clear HeqH.
  eapply r_1_next_ns with (ns := ns) in H; try eassumption.
   destruct H as (αj₁, (αk₁, H)).
   destruct H as (Hoth₁, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
   remember (q_of_m m (γ ns)) as q₀ eqn:Hq₀.
   eapply IHn with (ns := ns₁) (pol := pol₁) (m := (m * q₀)%positive); eauto .
    eapply hd_newton_segments; eauto .

    eapply next_pol_in_K_1_mq; eauto .

    intros i Hin.
    apply Nat.succ_le_mono in Hin.
    apply Hpsi in Hin; simpl in Hin.
    rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
    assumption.

   clear H.
   assert (0 ≤ S n)%nat as H by apply Nat.le_0_l.
   apply Hpsi in H; assumption.

  assert (0 ≤ S n)%nat as H by apply Nat.le_0_l.
  apply Hpsi in H; assumption.
Qed.

(* *)

Lemma nth_pol_succ : ∀ n pol ns pol₁ ns₁ c₁,
  pol₁ = nth_pol n pol ns
  → ns₁ = nth_ns n pol ns
  → c₁ = nth_c n pol ns
  → nth_pol (S n) pol ns = next_pol pol₁ (β ns₁) (γ ns₁) c₁.
Proof.
intros n pol ns pol₁ ns₁ c₁ Hpol₁ Hns₁ Hc₁; subst.
revert pol ns.
induction n; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
apply IHn.
Qed.

Lemma nth_ns_succ : ∀ n pol ns pol₁,
  pol₁ = nth_pol (S n) pol ns
  → nth_ns (S n) pol ns = List.hd phony_ns (newton_segments pol₁).
Proof.
intros n pol ns pol₁ Hpol₁; subst.
revert pol ns.
induction n; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
apply IHn.
Qed.

Lemma exists_ini_pt_nat_n : ∀ pol ns n nsn,
  ns ∈ newton_segments pol
  → nsn = nth_ns n pol ns
  → ∃ i αi, ini_pt nsn = (Qnat i, αi).
Proof.
intros pol ns n nsn Hns Hnsn.
destruct n.
 subst nsn; simpl.
 eapply exists_ini_pt_nat; eassumption.

 simpl in Hnsn.
 remember (ac_root (Φq pol ns)) as c.
 remember (next_pol pol (β ns) (γ ns) c) as polp.
 remember (List.hd phony_ns (newton_segments polp)) as nsp.
 clear Heqpolp.
 revert polp nsp nsn Heqnsp Hnsn.
 induction n; intros.
  subst nsn; simpl.
  eapply exists_ini_pt_nat_fst_seg; eassumption.

  simpl in Hnsn.
  remember (ac_root (Φq pol ns)) as c₁.
  remember (next_pol pol (β ns) (γ ns) c) as pol₁.
  remember (List.hd phony_ns (newton_segments polp)) as ns₁.
  eapply IHn; [ idtac | eassumption ].
  reflexivity.
Qed.

Lemma exists_fin_pt_nat_n : ∀ pol ns n nsn,
  ns ∈ newton_segments pol
  → nsn = nth_ns n pol ns
  → ∃ i αi, fin_pt nsn = (Qnat i, αi).
Proof.
intros pol ns n nsn Hns Hnsn.
destruct n.
 subst nsn; simpl.
 eapply exists_fin_pt_nat; eassumption.

 simpl in Hnsn.
 remember (ac_root (Φq pol ns)) as c.
 remember (next_pol pol (β ns) (γ ns) c) as polp.
 remember (List.hd phony_ns (newton_segments polp)) as nsp.
 clear Heqpolp.
 revert polp nsp nsn Heqnsp Hnsn.
 induction n; intros.
  subst nsn; simpl.
  eapply exists_fin_pt_nat_fst_seg; eassumption.

  simpl in Hnsn.
  remember (ac_root (Φq pol ns)) as c₁.
  remember (next_pol pol (β ns) (γ ns) c) as pol₁.
  remember (List.hd phony_ns (newton_segments polp)) as ns₁.
  eapply IHn; [ idtac | eassumption ].
  reflexivity.
Qed.

Lemma Qnum_inv_Qnat_sub : ∀ j k,
  (j < k)%nat
  → Qnum (/ (Qnat k - Qnat j)) = 1%Z.
Proof.
intros j k Hjk.
rewrite Qnum_inv; [ reflexivity | simpl ].
do 2 rewrite Z.mul_1_r.
rewrite Z.add_opp_r.
rewrite <- Nat2Z.inj_sub.
 rewrite <- Nat2Z.inj_0.
 apply Nat2Z.inj_lt.
 apply Nat.lt_add_lt_sub_r; assumption.

 apply Nat.lt_le_incl; assumption.
Qed.

Lemma Qden_inv_Qnat_sub : ∀ j k,
  (j < k)%nat
  → Qden (/ (Qnat k - Qnat j)) = Pos.of_nat (k - j).
Proof.
intros j k Hjk.
apply Pos2Z.inj.
rewrite Qden_inv.
 simpl.
 do 2 rewrite Z.mul_1_r.
 symmetry.
 rewrite <- positive_nat_Z; simpl.
 rewrite Nat2Pos.id.
  rewrite Nat2Z.inj_sub; auto.
  apply Nat.lt_le_incl; assumption.

  intros H.
  apply Nat.sub_0_le in H.
  apply Nat.nlt_ge in H; contradiction.

 simpl.
 do 2 rewrite Z.mul_1_r.
 rewrite Z.add_opp_r.
 rewrite <- Nat2Z.inj_sub.
  rewrite <- Nat2Z.inj_0.
  apply Nat2Z.inj_lt.
  apply Nat.lt_add_lt_sub_r; assumption.

  apply Nat.lt_le_incl; assumption.
Qed.

Lemma ps_lap_in_0th : ∀ la, (la ≠ [])%pslap → ps_lap_in (ps_lap_nth 0 la) la.
Proof.
intros la Hla.
unfold ps_lap_nth.
destruct la as [| a]; [ exfalso; apply Hla; reflexivity | simpl ].
left; split; [ assumption | reflexivity ].
Qed.

Lemma next_lap_not_nil : ∀ pol ns ns₁ c la αj₁ αk₁,
  la = next_lap pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments POL la%pol)
  → ini_pt ns₁ = (0, αj₁)
  → fin_pt ns₁ = (1, αk₁)
  → (la ≠ [])%pslap.
Proof.
intros pol ns ns₁ c la αj₁ αk₁ Hla Hns₁ Hini₁ Hfin₁.
intros H.
symmetry in Hla.
inversion H; subst.
 rewrite <- H0 in Hini₁, Hfin₁.
 simpl in Hini₁, Hfin₁.
 discriminate Hfin₁.

 rewrite <- H2 in Hini₁, Hfin₁.
 unfold newton_segments in Hini₁, Hfin₁.
 unfold points_of_ps_polynom in Hini₁, Hfin₁.
 unfold points_of_ps_lap in Hini₁, Hfin₁.
 unfold points_of_ps_lap_gen in Hini₁, Hfin₁.
 simpl in Hini₁, Hfin₁.
 simpl in H0.
 apply order_inf in H0.
 rewrite H0 in Hini₁, Hfin₁.
 remember 1%nat as pow.
 assert (1 <= pow)%nat as Hpow by (subst pow; reflexivity).
 clear Heqpow.
 clear x H0 H2.
 revert pow Hpow Hini₁ Hfin₁.
 induction l as [| a]; intros; [ discriminate Hfin₁ | idtac ].
 simpl in Hini₁, Hfin₁.
 apply lap_eq_cons_nil_inv in H1.
 destruct H1 as (Ha, Hla).
 simpl in Ha.
 apply order_inf in Ha.
 rewrite Ha in Hini₁, Hfin₁.
 apply IHl with (pow := S pow); auto.
Qed.

Lemma num_m_den_is_pos : ∀ pol ns j αj m,
  ns ∈ newton_segments pol
  → ini_pt ns = (Qnat j, αj)
  → (0 < Qnum αj)%Z
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → (0 < Z.to_nat (Qnum αj * ' m / ' Qden αj))%nat.
Proof.
intros pol ns j αj m Hns Hini Hn Hm.
assert (' Qden αj | Qnum αj * ' m)%Z as H.
 eapply den_αj_divides_num_αj_m; eauto .

 destruct H as (d, Hd).
 rewrite Hd.
 rewrite Z.div_mul; auto.
 destruct d as [| d| d].
  simpl in Hd.
  apply Z.eq_mul_0_l in Hd; auto.
  rewrite Hd in Hn.
  exfalso; revert Hn; apply Z.lt_irrefl.

  apply Pos2Nat.is_pos.

  simpl in Hd.
  pose proof (Pos2Z.neg_is_neg (d * Qden αj)) as I.
  rewrite <- Hd in I.
  apply Z.nle_gt in I.
  exfalso; apply I.
  apply Z.mul_nonneg_nonneg; auto.
  apply Z.lt_le_incl; assumption.
Qed.

Lemma points_of_nil_ps_lap : ∀ la,
  (la = [])%pslap
  → points_of_ps_lap la = [].
Proof.
intros la Hla.
unfold points_of_ps_lap, points_of_ps_lap_gen, qpower_list.
remember O as pow; clear Heqpow; revert pow.
induction la as [| a]; intros; [ reflexivity | simpl ].
apply lap_eq_cons_nil_inv in Hla.
destruct Hla as (Ha, Hla); simpl in Ha.
apply order_inf in Ha; rewrite Ha.
apply IHla; assumption.
Qed.

Lemma next_next_pow : ∀ p₁ p₂ p₃ p₄ ns m,
  p₂ = next_pow p₁ ns m
  → p₄ = next_pow p₃ ns m
  → (p₁ + p₄)%nat = (p₂ + p₃)%nat.
Proof.
intros p₁ p₂ p₃ p₄ ns m Hp₂ Hp₄.
subst p₂ p₄.
unfold next_pow; simpl.
rewrite Nat.add_assoc, Nat.add_shuffle0.
reflexivity.
Qed.

Lemma next_pow_add : ∀ p q ns m,
  next_pow (p + q) ns m = (next_pow p ns m + q)%nat.
Proof.
intros p q ns m.
unfold next_pow.
rewrite Nat.add_shuffle0; reflexivity.
Qed.

Lemma nat_compare_add : ∀ a b c,
  Nat.compare a b = Nat.compare (a + c) (b + c).
Proof.
intros a b c.
remember (Nat.compare a b) as c₁ eqn:Hc₁ .
remember (Nat.compare (a + c) (b + c)) as c₂ eqn:Hc₂ .
symmetry in Hc₁, Hc₂.
destruct c₁.
 apply nat_compare_eq in Hc₁.
 destruct c₂; auto.
  apply nat_compare_lt in Hc₂.
  exfalso; omega.

  apply nat_compare_gt in Hc₂.
  exfalso; omega.

 apply nat_compare_lt in Hc₁.
 destruct c₂; auto.
  apply nat_compare_eq in Hc₂.
  exfalso; omega.

  apply nat_compare_gt in Hc₂.
  exfalso; omega.

 apply nat_compare_gt in Hc₁.
 destruct c₂; auto.
  apply nat_compare_eq in Hc₂.
  exfalso; omega.

  apply nat_compare_lt in Hc₂.
  exfalso; omega.
Qed.

Lemma find_coeff_step : ∀ pol ns m c pol₁ ns₁ i di p dp np,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
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

Theorem find_coeff_add : ∀ pol ns m mx p dp i,
  (find_coeff mx (p + dp) m pol ns (i + dp) =
   find_coeff mx p m pol ns i)%K.
Proof.
intros pol ns m mx p dp i.
revert pol ns m p dp i.
induction mx; intros; [ reflexivity | simpl ].
destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁]; auto.
rewrite <- nat_compare_add.
remember (Nat.compare p i) as cmp eqn:Hcmp .
symmetry in Hcmp.
destruct cmp; auto.
rewrite next_pow_add.
apply IHmx.
Qed.

Lemma zerop_1st_n_const_coeff_succ : ∀ pol ns n,
  zerop_1st_n_const_coeff (S n) pol ns =
  zerop_1st_n_const_coeff 0 pol ns ||
  zerop_1st_n_const_coeff n (nth_pol 1 pol ns) (nth_ns 1 pol ns).
Proof.
intros pol ns n; simpl.
destruct (ps_zerop R (ps_poly_nth 0 pol)); reflexivity.
Qed.

Lemma zerop_1st_n_const_coeff_succ2 : ∀ pol ns n,
  zerop_1st_n_const_coeff (S n) pol ns =
  zerop_1st_n_const_coeff n pol ns ||
  zerop_1st_n_const_coeff 0 (nth_pol (S n) pol ns) (nth_ns (S n) pol ns).
Proof.
intros pol ns n.
revert pol ns.
induction n; intros.
 simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol)); reflexivity.

 remember (S n) as sn; simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
  rewrite Heqsn in |- * at 1; simpl.
  destruct (ps_zerop R (ps_poly_nth 0 pol)); [ auto | contradiction ].

  remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
  remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  rewrite IHn; simpl.
  remember (nth_pol sn pol₁ ns₁) as poln eqn:Hpoln .
  destruct (ps_zerop R (ps_poly_nth 0 poln)) as [H₂| H₂].
   do 2 rewrite Bool.orb_true_r; reflexivity.

   do 2 rewrite Bool.orb_false_r.
   subst sn; simpl.
   destruct (ps_zerop R (ps_poly_nth 0 pol)); [ contradiction | subst; auto ].
Qed.

Lemma zerop_1st_n_const_coeff_false_iff : ∀ pol ns n,
  zerop_1st_n_const_coeff n pol ns = false
  ↔ ∀ i : nat, i ≤ n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps.
Proof.
intros pol ns n.
split; intros H.
 intros i Hin.
 revert pol ns i H Hin.
 induction n; intros.
  simpl in H.
  apply Nat.le_0_r in Hin; subst i.
  destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
  discriminate H.

  simpl in H.
  destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
   discriminate H.

   destruct i; auto; simpl.
   apply IHn; auto.
   apply Nat.succ_le_mono; assumption.

 revert pol ns H.
 induction n; intros; simpl.
  destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁]; auto.
  pose proof (H O (Nat.le_refl 0)) as H₂.
  contradiction.

  destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
   pose proof (H O (Nat.le_0_l (S n))) as H₂.
   contradiction.

   apply IHn; intros i Hin.
   apply Nat.succ_le_mono, H in Hin; assumption.
Qed.

Lemma root_tail_succ : ∀ pol ns m n c pol₁ ns₁,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (ps_poly_nth 0 pol ≠ 0)%ps ∨ zerop_1st_n_const_coeff n pol₁ ns₁ = true
  → (root_tail m (S n) pol ns = root_tail m n pol₁ ns₁)%ps.
Proof.
intros pol ns m n c pol₁ ns₁ Hc Hpol₁ Hns₁ Hnz.
unfold root_tail.
rewrite zerop_1st_n_const_coeff_succ; simpl.
rewrite <- Hc, <- Hpol₁, <- Hns₁.
destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| ]; [ simpl | reflexivity ].
destruct Hnz as [Hnz| Hnz]; [ contradiction | idtac ].
rewrite Hnz; reflexivity.
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
  (∀ i, (i < b)%nat → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps)
  → (root_tail m (a + b) pol ns =
     root_tail m a (nth_pol b pol ns) (nth_ns b pol ns))%ps.
Proof.
intros pol ns m a b Hnz.
revert pol ns m a Hnz.
induction b; intros; simpl.
 rewrite Nat.add_0_r; reflexivity.

 rewrite Nat.add_succ_r.
 remember (ac_root (Φq pol ns)) as c eqn:Hc .
 remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
 remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
 rewrite root_tail_succ; eauto .
  apply IHb; intros i Hib.
  apply Nat.succ_lt_mono, Hnz in Hib; simpl in Hib.
  subst; auto.

  pose proof (Hnz O (Nat.lt_0_succ b)) as H; auto.
Qed.

Lemma nth_in_newton_segments : ∀ pol₁ ns₁ c₁ poln nsn n m,
  ns₁ ∈ newton_segments pol₁
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol₁)
  → c₁ = ac_root (Φq pol₁ ns₁)
  → root_multiplicity acf c₁ (Φq pol₁ ns₁) = 1%nat
  → (∀ i, (i ≤ n)%nat → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
  → poln = nth_pol n pol₁ ns₁
  → nsn = nth_ns n pol₁ ns₁
  → nsn ∈ newton_segments poln.
Proof.
intros pol₁ ns₁ c₁ poln nsn n m Hns₁ Hm Hc₁ Hr₁ Hpsi Hpoln Hnsn.
subst poln nsn.
revert pol₁ ns₁ c₁ m Hns₁ Hm Hc₁ Hr₁ Hpsi.
induction n; intros; [ assumption | simpl ].
rewrite <- Hc₁.
remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
assert (1 ≤ S n) as H₁.
 apply -> Nat.succ_le_mono.
 apply Nat.le_0_l.

 apply Hpsi in H₁; simpl in H₁.
 rewrite <- Hc₁, <- Hpol₂ in H₁.
 remember (q_of_m m (γ ns₁)) as q₀ eqn:Hq₀ .
 eapply IHn with (m := (m * q₀)%positive); eauto .
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

  eapply next_pol_in_K_1_mq; eauto .

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
  → (root_tail (m * q₀) 0 pol₁ ns₁ =
     root_head 0 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum 0 0 pol₁ ns₁) *
       root_tail (m * q₀) 1 pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁.
remember (m * q₀)%positive as m₁.
unfold root_tail, root_head; simpl.
destruct (ps_zerop _ (ps_poly_nth 0 pol₁)) as [H₁| H₁].
 rewrite rng_add_0_l, rng_mul_0_r; reflexivity.

 rename H₁ into Hnz₁.
 remember Hns as HK₁; clear HeqHK₁.
 eapply next_pol_in_K_1_mq in HK₁; eauto .
 remember Hns as H; clear HeqH.
 eapply r_1_next_ns in H; eauto .
 destruct H as (αj₁, (αk₁, H)).
 destruct H as (_, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
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
 destruct (ps_zerop _ (ps_poly_nth 0 pol₂)) as [Hps₁| Hps₁].
  rewrite ps_mul_0_r, ps_add_0_r.
  unfold root_tail_from_cγ_list, ps_monom; simpl.
  rewrite Hini₁, Hfin₁; simpl.
  rewrite Hαk₁; simpl.
  rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
  rewrite Pos2Z.inj_mul, Z.mul_shuffle0.
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
     rewrite Nat.mul_comm in Hd; rewrite Hd.
     rewrite Nat.div_mul; auto.
     unfold root_tail_series_from_cγ_list.
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
  eapply r_1_next_ns in H; eauto .
  destruct H as (αj₂, (αk₂, H)).
  destruct H as (_, (Hini₂, (Hfin₂, (Hαj₂, Hαk₂)))).
  unfold root_tail_from_cγ_list; simpl.
  unfold ps_add, ps_mul; simpl.
  unfold cm; simpl.
  unfold ps_terms_add; simpl.
  unfold ps_ordnum_add; simpl.
  rewrite Hini₁, Hfin₁, Hini₂, Hfin₂; simpl.
  rewrite Hαk₁, Hαk₂; simpl.
  do 2 rewrite Z.mul_1_r, Z.add_0_r, Pos.mul_1_r.
  remember (Qnum αj₁ * ' Qden αk₁)%Z as nd.
  remember (Qden αj₁ * Qden αk₁)%positive as dd.
  remember (dd * m₁)%positive as x.
  rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
  rewrite Z.div_mul_cancel_r; auto.
  subst x.
  do 2 rewrite fold_series_const.
  rewrite series_stretch_const.
  rewrite series_mul_1_l.
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
       unfold root_tail_series_from_cγ_list; simpl.
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
        unfold root_tail_series_from_cγ_list; simpl.
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
        unfold root_tail_series_from_cγ_list.
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
          rewrite <- Heqm₁ in HK₁.
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
    rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
    rewrite Z.div_mul_cancel_r; auto.
    rewrite Z.mul_assoc.
    apply Z.mul_cancel_r; auto.
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

Lemma q_eq_1_nth : ∀ pol ns pol₁ ns₁ c₁ m q₀,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → ps_lap_forall (λ a, in_K_1_m a (m * q₀)) (al pol₁)
  → c₁ = ac_root (Φq pol ns)
  → root_multiplicity acf c₁ (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ∀ n nsn,
    (∀ i : nat, i ≤ n → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps)
    → nsn = nth_ns n pol₁ ns₁
    → q_of_m (m * q₀) (γ nsn) = 1%positive.
Proof.
intros pol ns pol₁ ns₁ c₁ m q₀.
intros Hns Hm Hm₁ Hc₁ Hr₁ Hpol₁ Hns₁.
intros n nsn Hpsi Hnsn.
revert nsn Hpsi Hnsn.
revert Hns Hm Hm₁ Hc₁ Hr₁ Hpol₁ Hns₁.
revert pol ns pol₁ ns₁ c₁ m q₀.
induction n; intros.
 subst nsn; simpl.
 eapply q_eq_1; eauto .
 pose proof (Hpsi O (Nat.le_refl O)) as H; assumption.

 simpl in Hnsn.
 remember (ac_root (Φq pol₁ ns₁)) as c₂ eqn:Hc₂ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₂) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 remember Hns as H; clear HeqH.
 eapply r_1_next_ns in H; eauto .
  destruct H as (αj₁, (αk₁, H)).
  destruct H as (Hoth₁, (Hini₁, (Hfin₁, (Hαj₁, Hαk₁)))).
  remember Hns₁ as Hns₁₁; clear HeqHns₁₁.
  eapply hd_newton_segments in Hns₁₁; eauto .
  remember (m * q₀)%positive as m₁.
  replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
  eapply IHn with (pol₁ := pol₂) (ns := ns₁) (pol := pol₁); eauto .
   eapply next_pol_in_K_1_mq with (pol := pol₁); eauto .
   symmetry; subst m₁.
   eapply q_eq_1 with (ns := ns); eauto .
   pose proof (Hpsi O (Nat.le_0_l (S n))) as H; assumption.

   eapply multiplicity_1_remains_in_nth with (ns := ns) (n := O); eauto .
   intros i Hi.
   apply Nat.le_0_r in Hi; subst i; simpl.
   pose proof (Hpsi O (Nat.le_0_l (S n))) as H; assumption.

   intros i Hi.
   apply Nat.succ_le_mono in Hi.
   apply Hpsi in Hi.
   simpl in Hi.
   rewrite <- Hc₂, <- Hpol₂, <- Hns₂ in Hi; assumption.

  clear H.
  pose proof (Hpsi O (Nat.le_0_l (S n))) as H; assumption.
Qed.

Lemma root_tail_from_0₉ : ∀ pol ns pol₁ ns₁ c m q₀ b,
  ns ∈ newton_segments pol
  → ps_lap_forall (λ a, in_K_1_m a m) (al pol)
  → q₀ = q_of_m m (γ ns)
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) = 1%nat
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → (root_tail (m * q₀) b pol₁ ns₁ =
     root_head b 0 pol₁ ns₁ +
       ps_monom 1%K (γ_sum b 0 pol₁ ns₁) *
       root_tail (m * q₀) (b + 1) pol₁ ns₁)%ps.
Proof.
intros pol ns pol₁ ns₁ c m q₀ b Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁.
remember (m * q₀)%positive as m₁.
destruct b; [ subst m₁; eapply root_tail_split_1st; eauto  | idtac ].
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
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
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
 remember Hr as Hr₁; clear HeqHr₁.
 eapply multiplicity_1_remains in Hr₁; eauto .
 assert (∀ i : nat, i ≤ b₁ → (ps_poly_nth 0 (nth_pol i pol₁ ns₁) ≠ 0)%ps).
  apply zerop_1st_n_const_coeff_false_iff; subst b₁.
  rewrite zerop_1st_n_const_coeff_succ.
  rewrite Hpsi, Bool.orb_false_r; simpl.
  destruct (ps_zerop R (ps_poly_nth 0 pol₁)); auto.
  contradiction.

  clear Hpsi; rename H into Hpsi.
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
  rewrite <- Hns₂ in Hpolb, Hnsb, Hpolb₂.
  rewrite <- Nat.add_1_r, <- Hpolb₂.
  remember Hns₁₁ as H; clear HeqH.
  eapply nth_in_newton_segments with (n := b) in H; eauto .
  remember Hns as Hrb₁; clear HeqHrb₁.
  eapply multiplicity_1_remains_in_nth with (n := b) in Hrb₁; eauto .
  remember (nth_ns b pol₁ ns₁) as nsb₁ eqn:Hnsb₁ .
  remember (nth_pol b pol₁ ns₁) as polb₁ eqn:Hpolb₁ .
  remember (ac_root (Φq polb₁ nsb₁)) as cb₁ eqn:Hcb₁ .
  pose proof (Hpsi (S b) (Nat.le_refl (S b))) as Hpsb.
  simpl in Hpsb.
  rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hpsb.
  erewrite <- nth_pol_n with (c₁ := c₁) in Hpsb; eauto .
  erewrite nth_ns_n with (c := c₁) in Hnsb; eauto .
  eapply r_1_j_0_k_1 with (ns₁ := nsb) (m := (m * q₀)%positive) in H; eauto .
   Focus 2.
   eapply lap_forall_nth with (ns := ns₁) (n := b); eauto .
    eapply q_eq_1 with (ns := ns); eauto .
    eapply next_pol_in_K_1_mq with (ns := ns); eauto .

    eapply next_pol_in_K_1_mq with (ns := ns); eauto .

   erewrite <- nth_ns_n with (c := c₁) in Hnsb; eauto .
   erewrite nth_pol_n with (c₁ := c₁) in Hpsb; eauto .
  rewrite <- Hpolb in Hpsb.
  destruct H as (Hjb, (Hkb, (Hαjb, (Hαkb, Hothb)))).
  subst jb kb.
  unfold Qlt in Hαjb; simpl in Hαjb.
  unfold Qeq in Hαkb; simpl in Hαkb.
  rewrite Z.mul_1_r in Hαjb, Hαkb.
  destruct (ps_zerop R (ps_poly_nth 0 polb₂)) as [H₁| H₁].
   rewrite rng_mul_0_r, rng_add_0_r, Nat.add_1_r.
   unfold root_tail_from_cγ_list, ps_monom; simpl.
   rewrite Hinib, Hfinb; simpl.
   rewrite Hαkb; simpl.
   rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
   rewrite Z.mul_shuffle0, Pos2Z.inj_mul.
   rewrite Z.div_mul_cancel_r; auto.
   rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
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
     rewrite Nat.mul_comm in Hd; rewrite Hd.
     rewrite Nat.div_mul; auto.
     unfold root_tail_series_from_cγ_list.
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
   rewrite Nat.add_1_r; simpl.
   rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
   remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
   remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
   remember (List.hd phony_ns (newton_segments pol₃)) as ns₃ eqn:Hns₃ .
   rewrite Nat.add_comm in Hpolb₂; simpl in Hpolb₂.
   rewrite <- Hc₂, <- Hpol₃, <- Hns₃ in Hpolb₂.
   rewrite <- Hpolb₂.
   remember (nth_ns b pol₃ ns₃) as nsb₂ eqn:Hnsb₂ .
   remember Hns₃ as H; clear HeqH.
   eapply nth_ns_n with (c := c₂) in H; eauto .
   rewrite <- Hnsb₂ in H.
   erewrite nth_pol_n with (c₁ := c₂) in H; eauto .
   rewrite <- Hpolb₂ in H.
   rename H into Hbns₂.
   remember Hbns₂ as H; clear HeqH.
   erewrite <- nth_pol_n with (c₁ := c₂) in Hpolb₂; eauto .
   eapply r_1_next_ns with (m := (m * q₀)%positive) in H; eauto .
    Focus 2.
    eapply lap_forall_nth with (ns := ns₁); eauto .
     eapply q_eq_1 with (ns := ns); eauto .
     eapply next_pol_in_K_1_mq with (ns := ns); eauto .

     simpl.
     rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
     assumption.

     eapply next_pol_in_K_1_mq with (ns := ns); eauto .
   destruct H as (αjb₂, (αkb₂, H)).
   destruct H as (Hothb₂, (Hinib₂, (Hfinb₂, (Hαjb₂, Hαkb₂)))).
   unfold root_tail_from_cγ_list; simpl.
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
        unfold root_tail_series_from_cγ_list; simpl.
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
        unfold root_tail_series_from_cγ_list; simpl.
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
        unfold root_tail_series_from_cγ_list.
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

            eapply
             multiplicity_1_remains with (ns := nsb) (m := (m * q₀)%positive);
             eauto .
            eapply lap_forall_nth with (ns := ns₂); eauto .
             eapply hd_newton_segments; eauto .

             eapply multiplicity_1_remains with (ns := ns₁); eauto .

             rewrite <- Heqm₁.
             replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
             eapply q_eq_1 with (ns := ns₁); eauto .
             eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .
             symmetry.
             rewrite Heqm₁.
             eapply q_eq_1 with (ns := ns); eauto .
             eapply next_pol_in_K_1_mq with (ns := ns); eauto .

             intros j Hj.
             apply Nat.succ_le_mono in Hj.
             apply Hpsi in Hj; simpl in Hj.
             rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hj.
             assumption.

             rewrite <- Heqm₁.
             replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
             eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .
             symmetry.
             rewrite Heqm₁.
             eapply q_eq_1 with (ns := ns); eauto .
             eapply next_pol_in_K_1_mq with (ns := ns); eauto .

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

Lemma root_tail_sep_1st_monom₉ : ∀ pol ns pol₁ ns₁ c m q₀ n,
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
(* à nettoyer *)
intros pol ns pol₁ ns₁ c m q₀ n Hns Hm Hq₀ Hc Hr Hpol₁ Hns₁ Hpsi.
remember (m * q₀)%positive as m₁.
remember (S n) as sn.
unfold root_tail, ps_monom; simpl.
rewrite fold_series_const.
rewrite fold_series_const.
remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
remember (nth_pol n pol₁ ns₁) as poln₁ eqn:Hpoln₁ .
remember (nth_pol n pol₂ ns₂) as poln₂ eqn:Hpoln₂ .
subst sn.
rewrite zerop_1st_n_const_coeff_succ2.
remember (zerop_1st_n_const_coeff n pol₁ ns₁) as z₁ eqn:Hz₁ .
symmetry in Hz₁.
destruct z₁.
 apply zerop_1st_n_const_coeff_false_iff in Hpsi.
 rewrite Hpsi in Hz₁.
 discriminate Hz₁.

 rewrite Bool.orb_false_l.
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
 remember (nth_ns n pol₁ ns₁) as nsn₁ eqn:Hnsn₁ .
 simpl.
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
 rewrite <- Hpoln₂.
 remember (nth_ns n pol₂ ns₂) as nsn₂ eqn:Hnsn₂.
 destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₂| H₂].
  rewrite ps_mul_0_r, ps_add_0_r.
  unfold root_tail_from_cγ_list; simpl.
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
      unfold root_tail_series_from_cγ_list; simpl.
      destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₃| H₃].
       pose proof (Hpsi n (Nat.le_refl n)) as H.
       rewrite <- Hpoln₁ in H.
       contradiction.

       symmetry.
       apply nth_c_root; auto.

      unfold root_tail_series_from_cγ_list; simpl.
      destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [| H₄]; auto.
      clear H₄.
      destruct d.
       exfalso; subst i; revert H₃; apply Nat.lt_irrefl.

       remember (ac_root (Φq poln₁ nsn₁)) as cn₁ eqn:Hcn₁ .
       remember (next_pol poln₁ (β nsn₁) (γ nsn₁) cn₁) as poln₁s eqn:Hpoln₁s .
       erewrite nth_pol_n with (ns₁ := ns₁) in Hpoln₁s; eauto .
       rewrite <- Hpoln₂ in Hpoln₁s; subst poln₁s.
       remember (List.hd phony_ns (newton_segments poln₂)) as nsn₂'.
       simpl.
       destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₄| H₄]; auto.
       contradiction.

     destruct (zerop i) as [H₄| H₄]; auto.
     subst i; rewrite Nat.mod_0_l in H₃; auto.
     exfalso; revert H₃; apply Nat.lt_irrefl.

    apply Pos.mul_comm; reflexivity.

   remember Hns₁i as H; clear HeqH.
   eapply nth_in_newton_segments with (m := (m * q₀)%positive) in H; eauto .
    rename H into Hnsn₁i.
    eapply den_αj_divides_num_αj_m with (ns := nsn₁); eauto .
    eapply lap_forall_nth with (ns := ns₁); eauto .
     rewrite Heqm₁.
     eapply q_eq_1 with (ns := ns); eauto .
     eapply next_pol_in_K_1_mq with (ns := ns); eauto .

     rewrite Heqm₁.
     eapply next_pol_in_K_1_mq with (ns := ns); eauto .

    eapply next_pol_in_K_1_mq with (ns := ns); eauto .

  remember Hns as H; clear HeqH.
  eapply r_1_nth_ns with (poln := poln₁) in H; eauto .
  destruct H as (αjn₁, (αkn₁, H)).
  destruct H as (_, (Hinin₁, (Hfinn₁, (Hαjn₁, Hαkn₁)))).
  assert (ps_poly_nth 0 pol₂ ≠ 0)%ps as Hps₂.
   destruct n; [ simpl in Hpoln₂; subst poln₂; assumption | idtac ].
   assert (1 ≤ S n)%nat as H by fast_omega .
   apply Hpsi in H; simpl in H.
   rewrite <- Hc₁, <- Hpol₂ in H; assumption.

   assert (ps_lap_forall (λ a, in_K_1_m a m₁) (al pol₁)) as Hps₁.
    rewrite Heqm₁.
    eapply next_pol_in_K_1_mq with (ns := ns); eauto .

    assert (ns₂ ∈ newton_segments pol₂) as Hns₂i.
     remember Hns₂ as H; clear HeqH.
     eapply r_1_next_ns with (pol := pol₁) in H; eauto .
     destruct H as (αj₂, (αk₂, H)).
     destruct H as (Hoth₂, (Hini₂, (Hfin₂, (Hαj₂, Hαk₂)))).
     eapply hd_newton_segments; eauto .

     remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
     assert (root_multiplicity acf c₂ (Φq pol₂ ns₂) = 1%nat) as Hr₂.
      eapply multiplicity_1_remains with (ns := ns₁); eauto .

      assert (q_of_m m₁ (γ ns₁) = 1%positive) as Hq₁.
       rewrite Heqm₁.
       eapply q_eq_1 with (ns := ns); eauto .
       eapply next_pol_in_K_1_mq with (ns := ns); eauto .

       assert (q_of_m m₁ (γ ns₂) = 1%positive) as Hq₂.
        replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
        eapply q_eq_1 with (ns := ns₁); eauto .
        eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .

        rename Hps₂ into Hnz₂.
        assert (ps_lap_forall (λ a, in_K_1_m a m₁) (al pol₂)) as Hps₂.
         replace m₁ with (m₁ * 1)%positive by apply Pos.mul_1_r.
         eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .

         assert (ps_lap_forall (λ a, in_K_1_m a m₁) (al poln₂)) as Hpsn₂.
          eapply lap_forall_nth with (ns := ns₂); eauto .
          intros i Hin.
          destruct (eq_nat_dec i n) as [H₃| H₃].
           subst i.
           rewrite <- Hpoln₂; assumption.

           apply le_neq_lt in Hin; auto.
           apply Hpsi in Hin.
           simpl in Hin.
           rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hin.
           assumption.

          remember Hns as H; clear HeqH.
          eapply r_1_nth_ns with (poln := poln₂) (n := S n) in H; eauto .
           destruct H as (αjn₂, (αkn₂, H)).
           destruct H as (_, (Hinin₂, (Hfinn₂, (Hαjn₂, Hαkn₂)))).
           simpl in Hinin₂, Hfinn₂.
           rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hinin₂, Hfinn₂.
           rewrite <- Hnsn₂ in Hinin₂, Hfinn₂.
           unfold ps_add, ps_mul; simpl.
           unfold cm; simpl.
           unfold ps_terms_add, ps_ordnum_add; simpl.
           unfold root_tail_from_cγ_list; simpl.
           rewrite Hinin₁, Hfinn₁, Hinin₂, Hfinn₂; simpl.
           rewrite Hαkn₁, Hαkn₂; simpl.
           rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
           erewrite nth_γ_n; eauto ; simpl.
           rewrite Hαkn₁; simpl.
           rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
           rewrite Z.add_0_r, Z.mul_1_r, Pos.mul_1_r.
           remember (Qnum αjn₁ * ' Qden αkn₁)%Z as nd₁ eqn:Hnd₁ .
           remember (Qden αjn₁ * Qden αkn₁)%positive as dd₁ eqn:Hdd₁ .
           remember (Qnum αjn₂ * ' Qden αkn₂)%Z as nd₂ eqn:Hnd₂ .
           remember (Qden αjn₂ * Qden αkn₂)%positive as dd₂ eqn:Hdd₂ .
           remember (nd₂ * ' m₁ / ' dd₂ * ' dd₁)%Z as x.
           rewrite Hnd₂, Hdd₂, Hdd₁ in Heqx.
           rewrite Pos2Z.inj_mul, Z.mul_shuffle0 in Heqx.
           rewrite Z.div_mul_cancel_r in Heqx; auto.
           rewrite <- Hdd₁ in Heqx.
           remember (Qnum αjn₂ * ' m₁ / ' Qden αjn₂)%Z as nmd₂ eqn:Hnmd₂ .
           subst x.
           rewrite Z.min_l.
            rewrite Z.min_r.
             rewrite Z.sub_diag; simpl.
             rewrite series_stretch_const.
             rewrite series_mul_1_l.
             rewrite Z.mul_add_distr_r.
             rewrite Pos2Z.inj_mul.
             rewrite Z.mul_shuffle0.
             rewrite Z.mul_assoc.
             rewrite Z.add_simpl_l.
             unfold adjust_series at 1.
             rewrite series_shift_0, series_stretch_const.
             rewrite ps_adjust_eq with (n := O) (k := (dd₁ * dd₁)%positive).
             unfold adjust_ps; simpl.
             rewrite series_shift_0, Z.sub_0_r.
             rewrite Pos2Z.inj_mul, Z.mul_assoc.
             rewrite Z_div_mul_swap.
              rewrite Z.div_mul; auto.
              rewrite Z.mul_shuffle0.
              apply mkps_morphism; auto.
               unfold adjust_series; simpl.
               rewrite <- series_stretch_stretch.
               rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
               rewrite Z2Nat_inj_mul_pos_r.
               rewrite <- stretch_shift_series_distr.
               rewrite
                <- series_stretch_const with (k := (dd₁ * dd₁)%positive).
               rewrite <- series_stretch_add_distr.
               apply stretch_morph; auto.
               constructor; intros i; simpl.
               assert (nsn₂ ∈ newton_segments poln₂) as Hnsn₂i.
                eapply hd_newton_segments; eauto .
                subst nsn₂.
                eapply nth_ns_n with (c := c₁); eauto .
                erewrite nth_pol_n with (c₁ := c₁); eauto .

                unfold root_tail_series_from_cγ_list; simpl.
                destruct (ps_zerop R (ps_poly_nth 0 poln₁)) as [H₃| H₃].
                 pose proof (Hpsi n (Nat.le_refl n)) as H.
                 rewrite <- Hpoln₁ in H.
                 contradiction.

                 clear H₃.
                 destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₃| H₃].
                  contradiction.

                  clear H₃.
                  remember (ac_root (Φq poln₁ nsn₁)) as cn₁ eqn:Hcn₁ .
                  remember (next_pol poln₁ (β nsn₁) (γ nsn₁) cn₁) as poln₁s
                   eqn:Hpoln₁s .
                  erewrite nth_pol_n with (ns₁ := ns₁) in Hpoln₁s; eauto .
                  rewrite <- Hpoln₂ in Hpoln₁s; subst poln₁s.
                  destruct i.
                   simpl.
                   destruct (lt_dec 0 (Z.to_nat nmd₂)) as [H₃| H₃].
                    rewrite rng_add_0_r; subst cn₁; symmetry.
                    apply nth_c_root; auto.

                    exfalso; apply H₃; subst nmd₂.
                    eapply num_m_den_is_pos with (ns := nsn₂) (pol := poln₂);
                     eauto .

                   remember Hnsn₂ as H; clear HeqH.
                   erewrite nth_ns_n with (c := c₁) in H; eauto .
                   erewrite nth_pol_n with (c₁ := c₁) in H; eauto .
                   rewrite <- Hpoln₂ in H.
                   rename H into Hnsn₂p.
                   rewrite <- Hnsn₂p.
                   remember (ac_root (Φq poln₂ nsn₂)) as cn₂ eqn:Hcn₂ .
                   remember (next_pol poln₂ (β nsn₂) (γ nsn₂) cn₂) as poln₃.
                   remember
                    (List.hd phony_ns (newton_segments poln₃)) as nsn₃.
                   remember (find_coeff (S i)) as f; simpl; subst f.
                   rewrite rng_add_0_l.
                   destruct (lt_dec (S i) (Z.to_nat nmd₂)) as [H₃| H₃].
                    remember (S i) as si.
                    unfold next_pow; simpl.
                    rewrite Hinin₂, Hfinn₂; simpl.
                    rewrite Hαkn₂; simpl.
                    rewrite Z.add_0_r, Z.mul_1_r.
                    do 2 rewrite Pos.mul_1_r.
                    rewrite Pos2Z.inj_mul, Z.mul_shuffle0.
                    rewrite Z.div_mul_cancel_r; auto.
                    subst si; simpl.
                    destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₄| H₄];
                     auto.
                    clear H₄.
                    rewrite <- Hnmd₂.
                    remember (Nat.compare (Z.to_nat nmd₂) (S i)) as cmp₂
                     eqn:Hcmp₂ .
                    symmetry in Hcmp₂.
                    destruct cmp₂; auto.
                     apply nat_compare_eq in Hcmp₂.
                     rewrite Hcmp₂ in H₃.
                     exfalso; revert H₃; apply Nat.lt_irrefl.

                     apply nat_compare_lt in Hcmp₂.
                     exfalso; fast_omega H₃ Hcmp₂.

                    apply Nat.nlt_ge in H₃.
                    remember (S i) as si.
                    unfold next_pow at 1; simpl.
                    rewrite Hinin₂, Hfinn₂; simpl.
                    rewrite Hαkn₂; simpl.
                    rewrite Z.add_0_r, Z.mul_1_r.
                    do 2 rewrite Pos.mul_1_r.
                    rewrite Pos2Z.inj_mul, Z.mul_shuffle0.
                    rewrite Z.div_mul_cancel_r; auto.
                    rewrite <- Hnmd₂.
                    subst si; simpl.
                    destruct (ps_zerop R (ps_poly_nth 0 poln₂)) as [H₄| H₄];
                     auto.
                     contradiction.

                     clear H₄.
                     remember (Nat.compare (Z.to_nat nmd₂) (S i)) as cmp₂
                      eqn:Hcmp₂ .
                     symmetry in Hcmp₂.
                     destruct cmp₂; auto.
                      apply nat_compare_eq in Hcmp₂.
                      rewrite Hcmp₂.
                      rewrite Nat.sub_diag; simpl.
                      symmetry.
                      rewrite Hcn₂; reflexivity.

                      apply nat_compare_lt in Hcmp₂.
                      rewrite <- Hcn₂, <- Heqpoln₃, <- Heqnsn₃.
                      remember (Z.to_nat nmd₂) as x eqn:Hx .
                      symmetry in Hx.
                      destruct x.
                       exfalso; symmetry in Hx; revert Hx.
                       apply lt_0_neq.
                       subst nmd₂.
                       eapply num_m_den_is_pos with (ns := nsn₂); eauto .

                       remember (i - x)%nat as ix.
                       destruct ix;
                        [ exfalso; fast_omega Heqix Hcmp₂ | idtac ].
                       replace (S x) with (0 + S x)%nat by fast_omega .
                       rewrite next_pow_add.
                       replace (S i) with (S ix + S x)%nat
                        by fast_omega Heqix.
                       rewrite find_coeff_add.
                       destruct i; [ exfalso; fast_omega Heqix | idtac ].
                       simpl.
                       destruct (ps_zerop R (ps_poly_nth 0 poln₃))
                        as [H₄| H₄]; auto.
                       remember
                        (Nat.compare (next_pow 0 nsn₃ m₁) (S ix)) as cmp₃
                        eqn:Hcmp₃ .
                       symmetry in Hcmp₃.
                       destruct cmp₃; auto.
                       remember (ac_root (Φq poln₃ nsn₃)) as cn₃ eqn:Hcn₃ .
                       remember
                        (next_pol poln₃ (β nsn₃) (γ nsn₃) cn₃) as poln₄
                        eqn:Hpoln₄ .
                       remember
                        (List.hd phony_ns (newton_segments poln₄)) as nsn₄
                        eqn:Hnsn₄ .
                       remember (next_pow 0 nsn₃ m₁) as np₁ eqn:Hnp₁ .
                       symmetry.
                       rewrite <- Nat.add_1_r.
                       symmetry.
                       rewrite Nat.add_1_r.
                       rewrite Heqix.
                       rewrite <- find_coeff_add with (dp := x).
                       replace (S i - x + x)%nat with 
                        (S i) by fast_omega Hcmp₂.
                       symmetry.
                       rewrite <- find_coeff_add with (dp := x).
                       replace (S i - x + x)%nat with 
                        (S i) by fast_omega Hcmp₂.
                       rewrite <- next_pow_add.
                       symmetry.
                       rewrite <- Nat.add_1_r.
                       replace ix with (S i - S x)%nat by fast_omega Heqix.
                       remember Heqnsn₃ as H; clear HeqH.
                       eapply r_1_next_ns with (pol := poln₂) in H; eauto .
                        destruct H as (αjn₃, (αkn₃, H)).
                        destruct H as (_, (Hinin₃, (Hfinn₃, (Hαjn₃, Hαkn₃)))).
                        assert (0 < np₁)%nat as Hnp₁p.
                         subst np₁.
                         unfold next_pow; simpl.
                         rewrite Hinin₃, Hfinn₃; simpl.
                         rewrite Hαkn₃; simpl.
                         rewrite Z.add_0_r, Z.mul_1_r.
                         do 2 rewrite Pos.mul_1_r.
                         rewrite Pos2Z.inj_mul, Z.mul_shuffle0.
                         rewrite Z.div_mul_cancel_r; auto.
                         eapply
                          num_m_den_is_pos with (ns := nsn₃) (pol := poln₃);
                          eauto .
                          eapply hd_newton_segments; eauto .

                          replace m₁ with (m₁ * 1)%positive
                           by apply Pos.mul_1_r.
                          eapply next_pol_in_K_1_mq with (ns := nsn₂); eauto .
                          symmetry.
                          replace m₁ with (m₁ * 1)%positive
                           by apply Pos.mul_1_r.
                          eapply q_eq_1 with (pol := poln₁) (ns := nsn₁);
                           eauto .
                           eapply hd_newton_segments; eauto .
                           rewrite Hnsn₁.
                           eapply nth_ns_n with (c := c); eauto .
                           erewrite nth_pol_n with (c₁ := c); eauto .

                           eapply lap_forall_nth with (ns := ns₁); eauto .

                           erewrite
                            nth_pol_n with (pol₁ := pol₁) (ns₁ := ns₁); 
                            eauto .
                           eapply lap_forall_nth with (ns := ns₂); eauto .
                            eapply q_eq_1 with (ns := ns₁); eauto .
                            eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .

                            clear i H₃ Hcmp₂ Heqix.
                            intros i Hisn.
                            destruct (eq_nat_dec i n) as [H₅| H₅].
                             subst i; simpl.
                             rewrite <- Hpoln₂.
                             assumption.

                             apply le_neq_lt in Hisn; auto.
                             apply Hpsi in Hisn; simpl in Hisn.
                             rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                             assumption.

                            eapply next_pol_in_K_1_mq with (ns := ns₁); eauto .

                           eapply
                            multiplicity_1_remains_in_nth with (ns := ns);
                            eauto .

                           erewrite nth_pol_n with (c₁ := c₁); eauto .
                           rewrite <- Hpoln₂.
                           assumption.

                           erewrite nth_pol_n with (c₁ := c₁) (pol₂ := pol₂);
                            eauto .
                           rewrite <- Hpoln₂; assumption.

                         destruct (eq_nat_dec i x) as [H₅| H₅].
                          subst i.
                          rewrite minus_Sn_n in Heqix.
                          apply Nat.succ_inj in Heqix.
                          rewrite Nat.sub_diag; subst ix.
                          apply nat_compare_lt in Hcmp₃.
                          exfalso; fast_omega Hcmp₃ Hnp₁p.

                          eapply
                           find_coeff_step
                            with
                              (ns := nsn₃)
                              (pol := poln₃)
                              (dp := (np₁ - 1)%nat); 
                           eauto .
                           eapply hd_newton_segments; eauto .

                           replace m₁ with (m₁ * 1)%positive
                            by apply Pos.mul_1_r.
                           eapply next_pol_in_K_1_mq with (ns := nsn₂); eauto .
                           symmetry.
                           replace m₁ with (m₁ * 1)%positive
                            by apply Pos.mul_1_r.
                           eapply q_eq_1 with (pol := poln₁) (ns := nsn₁);
                            eauto .
                            eapply hd_newton_segments; eauto .
                            rewrite Hnsn₁.
                            eapply nth_ns_n with (c := c); eauto .
                            erewrite nth_pol_n with (c₁ := c); eauto .

                            eapply lap_forall_nth with (ns := ns₁); eauto .

                            erewrite
                             nth_pol_n with (pol₁ := pol₁) (ns₁ := ns₁);
                             eauto .
                            eapply lap_forall_nth with (ns := ns₂); eauto .
                             eapply q_eq_1 with (ns := ns₁); eauto .
                             eapply next_pol_in_K_1_mq with (ns := ns₁);
                              eauto .

                             clear i H₅ H₃ Hcmp₂ Heqix.
                             intros i Hisn.
                             destruct (eq_nat_dec i n) as [H₅| H₅].
                              subst i; simpl.
                              rewrite <- Hpoln₂.
                              assumption.

                              apply le_neq_lt in Hisn; auto.
                              apply Hpsi in Hisn; simpl in Hisn.
                              rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                              assumption.

                             eapply next_pol_in_K_1_mq with (ns := ns₁);
                              eauto .

                            eapply
                             multiplicity_1_remains_in_nth with (ns := ns);
                             eauto .

                            erewrite nth_pol_n with (c₁ := c₁); eauto .
                            rewrite <- Hpoln₂.
                            assumption.

                            erewrite nth_pol_n with (c₁ := c₁) (pol₂ := pol₂);
                             eauto .
                            rewrite <- Hpoln₂; assumption.

                           replace m₁ with (m₁ * 1)%positive
                            by apply Pos.mul_1_r.
                           eapply q_eq_1 with (pol := poln₂) (ns := nsn₂);
                            eauto .
                            eapply next_pol_in_K_1_mq with (ns := nsn₂);
                             eauto .
                            symmetry.
                            replace m₁ with (m₁ * 1)%positive
                             by apply Pos.mul_1_r.
                            eapply q_eq_1_nth with (ns := ns₁); eauto .
                             eapply next_pol_in_K_1_mq with (ns := ns₁);
                              eauto .

                             clear i H₅ H₃ Hcmp₂ Heqix.
                             intros i Hisn.
                             destruct (eq_nat_dec i n) as [H₅| H₅].
                              subst i; simpl.
                              rewrite <- Hpoln₂.
                              assumption.

                              apply le_neq_lt in Hisn; auto.
                              apply Hpsi in Hisn; simpl in Hisn.
                              rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                              assumption.

                            eapply
                             multiplicity_1_remains_in_nth with (ns := ns₁);
                             eauto .
                            clear i H₅ H₃ Hcmp₂ Heqix.
                            intros i Hisn.
                            destruct (eq_nat_dec i n) as [H₅| H₅].
                             subst i; simpl.
                             rewrite <- Hpoln₂.
                             assumption.

                             apply le_neq_lt in Hisn; auto.
                             apply Hpsi in Hisn; simpl in Hisn.
                             rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                             assumption.

                           eapply multiplicity_1_remains with (ns := nsn₂);
                            eauto .
                           eapply
                            multiplicity_1_remains_in_nth with (ns := ns₁);
                            eauto .
                           clear i H₅ H₃ Hcmp₂ Heqix.
                           intros i Hisn.
                           destruct (eq_nat_dec i n) as [H₅| H₅].
                            subst i; simpl.
                            rewrite <- Hpoln₂.
                            assumption.

                            apply le_neq_lt in Hisn; auto.
                            apply Hpsi in Hisn; simpl in Hisn.
                            rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                            assumption.

                           split; [ fast_omega  | idtac ].
                           fast_omega H₅ Hcmp₂.

                           fast_omega Hnp₁p.

                           replace (S x + (np₁ - 1))%nat with (np₁ + x)%nat ;
                            auto.
                           fast_omega Hnp₁p.

                        eapply multiplicity_1_remains_in_nth with (ns := ns₁);
                         eauto .
                        clear i H₃ Hcmp₂ Heqix.
                        intros i Hisn.
                        destruct (eq_nat_dec i n) as [H₅| H₅].
                         subst i; simpl.
                         rewrite <- Hpoln₂.
                         assumption.

                         apply le_neq_lt in Hisn; auto.
                         apply Hpsi in Hisn; simpl in Hisn.
                         rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hisn.
                         assumption.

                      apply nat_compare_gt in Hcmp₂.
                      apply Nat.nle_gt in Hcmp₂; contradiction.

               rewrite Pos.mul_comm, Pos.mul_assoc; reflexivity.

              subst dd₁ nd₁.
              rewrite Pos2Z.inj_mul.
              rewrite Z.mul_shuffle0.
              apply Z.mul_divide_cancel_r; auto.
              eapply den_αj_divides_num_αj_m with (ns := nsn₁) (pol := poln₁);
               eauto .
               eapply hd_newton_segments; eauto .
               rewrite Hnsn₁.
               eapply nth_ns_n with (c := c); eauto .
               rewrite Hpoln₁.
               symmetry.
               eapply nth_pol_n with (c₁ := c); eauto .

               eapply lap_forall_nth with (ns := ns₁); eauto .

             rewrite Pos2Z.inj_mul, Z.mul_add_distr_r.
             rewrite Z.mul_assoc, Z.mul_shuffle0.
             apply Z.le_sub_le_add_l.
             rewrite Z.sub_diag.
             apply Z.mul_nonneg_nonneg; auto.
             apply Z.mul_nonneg_nonneg; auto.
             subst nmd₂.
             apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
             apply Z.mul_nonneg_nonneg; auto.
             apply Z.lt_le_incl; assumption.

            rewrite Pos2Z.inj_mul, Z.mul_add_distr_r.
            rewrite Z.mul_assoc, Z.mul_shuffle0.
            apply Z.le_sub_le_add_l.
            rewrite Z.sub_diag.
            apply Z.mul_nonneg_nonneg; auto.
            apply Z.mul_nonneg_nonneg; auto.
            subst nmd₂.
            apply Z.div_pos; [ idtac | apply Pos2Z.is_pos ].
            apply Z.mul_nonneg_nonneg; auto.
            apply Z.lt_le_incl; assumption.

           intros i Hisn.
           destruct (eq_nat_dec i (S n)) as [H₃| H₃].
            subst i; simpl.
            rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
            rewrite <- Hpoln₂; assumption.

            apply le_neq_lt in Hisn; auto.
            apply Nat.succ_le_mono in Hisn.
            clear H₃.
            revert i Hisn; assumption.

           simpl.
           rewrite <- Hc₁, <- Hpol₂, <- Hns₂.
           assumption.
Qed.

Lemma zerop_1st_n_const_coeff_true_if : ∀ pol ns b,
  zerop_1st_n_const_coeff b pol ns = true
  → ∀ n, zerop_1st_n_const_coeff (b + n) pol ns = true.
Proof.
intros pol ns b Hz n.
revert pol ns Hz n.
induction b; intros.
 simpl.
 revert pol ns Hz.
 induction n; intros; auto.
 simpl in Hz; simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
 discriminate Hz.

 simpl in Hz; simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
Qed.

Lemma root_head_from_cγ_list_succ : ∀ pol ns b n i,
  zerop_1st_n_const_coeff (b + i) pol ns = false
  → (root_head_from_cγ_list pol ns b (S n) i =
     root_head_from_cγ_list pol ns b n i +
      (if zerop_1st_n_const_coeff (b + i + S n) pol ns then 0
       else
         ps_monom (nth_c (b + i + S n) pol ns)
           (γ_sum b (i + S n) pol ns)))%ps.
Proof.
intros pol ns b n i Hz; simpl.
revert b i Hz.
induction n; intros; simpl.
 symmetry; rewrite rng_add_0_r; symmetry.
 rewrite Nat.add_1_r.
 remember (zerop_1st_n_const_coeff (S (b + i)) pol ns) as z₁ eqn:Hz₁ .
 symmetry in Hz₁.
 rewrite Nat.add_succ_r.
 destruct z₁.
  rewrite zerop_1st_n_const_coeff_succ2 in Hz₁.
  rewrite Hz, Bool.orb_false_l in Hz₁.
  remember (nth_pol (S (b + i)) pol ns) as p.
  simpl in Hz₁.
  destruct (ps_zerop R (ps_poly_nth 0 p)) as [H₂| H₂]; subst p.
   reflexivity.

   discriminate Hz₁.

  apply zerop_1st_n_const_coeff_false_iff with (i := S (b + i)) in Hz₁.
   remember (nth_pol (S (b + i)) pol ns) as p.
   destruct (ps_zerop R (ps_poly_nth 0 p)) as [H₂| H₂]; subst p.
    contradiction.

    rewrite rng_add_0_r, Nat.add_1_r; reflexivity.

   reflexivity.

 rewrite <- rng_add_assoc; simpl.
 apply rng_add_compat_l; simpl.
 remember (nth_pol (b + S i) pol ns) as p.
 destruct (ps_zerop R (ps_poly_nth 0 p)) as [H₁| H₁]; subst p.
  rewrite rng_add_0_l.
  remember (zerop_1st_n_const_coeff (b + i + S (S n)) pol ns) as z₁ eqn:Hz₁ .
  symmetry in Hz₁.
  destruct z₁; [ reflexivity | idtac ].
  rewrite zerop_1st_n_const_coeff_false_iff in Hz₁.
  assert (b + S i ≤ b + i + S (S n)) as H by fast_omega .
  apply Hz₁ in H; contradiction.

  rewrite IHn.
   do 7 rewrite Nat.add_succ_r; rewrite Nat.add_succ_l.
   reflexivity.

   rewrite Nat.add_succ_r.
   rewrite zerop_1st_n_const_coeff_succ2.
   rewrite Hz, Bool.orb_false_l.
   rewrite <- Nat.add_succ_r.
   apply zerop_1st_n_const_coeff_false_iff.
   intros j Hj.
   apply Nat.le_0_r in Hj; subst j.
   assumption.
Qed.

Lemma root_head_succ : ∀ pol ns b n,
  zerop_1st_n_const_coeff b pol ns = false
  → (root_head b (S n) pol ns =
     root_head b n pol ns +
     if zerop_1st_n_const_coeff (b + S n) pol ns then 0
     else ps_monom (nth_c (b + S n) pol ns) (γ_sum b (S n) pol ns))%ps.
Proof.
intros pol ns b n Hz.
unfold root_head; rewrite Hz.
rewrite root_head_from_cγ_list_succ.
 rewrite Nat.add_0_r, Nat.add_0_l.
 reflexivity.

 rewrite Nat.add_0_r; assumption.
Qed.

End theorems.
