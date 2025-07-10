(* PosOrder.v *)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Sorted Morphisms.

Require Import A_PosArith A_ZArith A_QArith.
Require Import Misc.
Require Import NbarM.
Require Import QbarM.
Require Import SplitList.
Require Import Field2.
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
Require Import PSpolynomial.
Require Import AlgCloCharPol.
Require Import CharactPolyn.
Require Import F1Eq.

Set Implicit Arguments.

Theorem ps_lap_in_compat : ∀ α (R : ring α) (K : field R) a b la lb,
  (a = b)%ps
  → (la = lb)%pslap
  → ps_lap_in a la
  → ps_lap_in b lb.
Proof.
intros α R K a b la lb Hab Hlab Hla.
progress unfold ps_lap_eq in Hlab.
revert a b Hab lb Hlab Hla.
induction la as [| c]; intros; [ contradiction | idtac ].
simpl in Hla.
destruct Hla as [(Hcla, Hca)| Hla]. {
  destruct lb as [| d]; [ contradiction | idtac ].
  apply lap_eq_cons_inv in Hlab.
  destruct Hlab as (Hcd, Hlab).
  left.
  split. {
    intros H; apply Hcla; clear Hcla.
    rewrite <- H.
    constructor; assumption.
  }
  rewrite <- Hcd, <- Hab; assumption.
}
simpl.
destruct lb as [| d]. {
  apply lap_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Hc, Hlab).
  eapply IHla; eassumption.
} {
  apply lap_eq_cons_inv in Hlab.
  destruct Hlab as (Hcd, Hlab).
  right.
  eapply IHla; eassumption.
}
Qed.

Global Instance list_in_eq_ps_morph α (R : ring α) (K : field R) :
  Proper (eq_ps ==> (@lap_eq _ (ps_ring K)) ==> iff) (@ps_lap_in α R K).
Proof.
intros a b Hab la lb Hlab.
split; intros Hl. {
  eapply ps_lap_in_compat; eassumption.
}
symmetry in Hab, Hlab.
eapply ps_lap_in_compat; eassumption.
Qed.

Definition g_lap_of_ns α {R : ring α} {K : field R}
    {acf : algeb_closed_field K} f L :=
  let c₁ := ac_root (Φq f L) in
  let pl := [ini_pt L … oth_pts L ++ [fin_pt L]] in
  let tl := List.map (term_of_point f) pl in
  let l₁ := List.map (λ t, power t) tl in
  let l₂ := list_seq_except 0 (length (al f)) l₁ in
  ([ps_monom 1%K (- β L)] *
   (ps_lap_summ ps_field l₁
      (λ h,
       let āh := ps_poly_nth h f in
       let ah := ps_monom (coeff_of_term R h tl) 0 in
       let αh := ord_of_pt h pl in
       [((āh - ah * ps_monom 1%K αh) * ps_monom 1%K (Qnat h * γ L))%ps] *
       [ps_monom c₁ 0; 1%ps … []] ^ h) +
    ps_lap_summ ps_field l₂
      (λ l,
       let āl := ps_poly_nth l f in
       [(āl * ps_monom 1%K (Qnat l * γ L))%ps] *
       [ps_monom c₁ 0; 1%ps … []] ^ l)))%pslap.

Definition g_of_ns α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} f L := (POL (g_lap_of_ns f L))%pol.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Theorem coeff_of_hl_eq_order : ∀ h la li,
  h ∈ li
  → coeff_of_hl K la h li = order_coeff (List.nth h la 0%ps).
Proof.
intros h la li Hh.
induction li as [| i]; [ contradiction | simpl ].
destruct (eq_nat_dec h i) as [| Hhi]; [ subst; reflexivity | idtac ].
apply IHli.
apply Nat.neq_sym in Hhi.
destruct Hh as [Hh| ]; [ contradiction | assumption ].
Qed.

(* [Walker, p 101] « O(āh - ah.x^αh) > 0 » (with fixed typo) *)
Theorem order_āh_minus_ah_xαh_gt_αh : ∀ f L pl tl h āh ah αh,
  newton_segments f = Some L
  → pl = [ini_pt L … oth_pts L ++ [fin_pt L]]
  → tl = List.map (term_of_point f) pl
  → h ∈ List.map (λ t, power t) tl
  → āh = ps_poly_nth h f
  → ah = ps_monom (coeff_of_term R h tl) 0
  → αh = ord_of_pt h pl
  → (order (āh - ah * ps_monom 1%K αh)%ps > qfin αh)%Qbar.
Proof.
intros f L pl tl h āh ah αh HL Hpl Htl Hh Hāh Hah Hαh.
remember HL as Hval; clear HeqHval.
eapply order_in_newton_segment with (h := h) (αh := αh) in Hval; eauto. {
  rewrite <- Hāh in Hval.
  progress unfold order, Qbar.gt.
  remember (āh - ah * ps_monom 1%K αh)%ps as s eqn:Hs .
  remember (series_order (ps_terms s) 0) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ]; [ idtac | constructor ].
  apply Qbar.qfin_lt_mono.
  progress unfold order in Hval.
  remember (series_order (ps_terms āh) 0) as m eqn:Hm .
  symmetry in Hm.
  destruct m as [m| ]; [ idtac | discriminate Hval ].
  injection Hval; clear Hval; intros Hval.
  rewrite <- Hval.
  subst s; simpl.
  progress unfold cm; simpl.
  progress unfold cm; simpl.
  subst ah; simpl.
  progress unfold ps_ordnum_add; simpl.
  progress unfold cm, cm_factor; simpl.
  rewrite Z.mul_1_r.
  progress unfold Q.lt; simpl.
  rewrite Pos2Z.inj_mul.
  rewrite Z.mul_assoc.
  rewrite Z.mul_mul_swap.
  apply Z.compare_lt_iff; cbn.
  do 2 rewrite q_Den_num_den.
  rewrite Pos.mul_1_l.
  rewrite Z.mul_1_r.
  rewrite (Pos.mul_comm (ps_polydo _)).
  rewrite Pos2Z.inj_mul.
  rewrite Z.mul_assoc.
  apply Z.mul_lt_mono_pos_r; [ easy | ].
  rewrite <- Hval; simpl.
  rewrite Z.mul_min_distr_nonneg_r; [ idtac | easy ].
  rewrite Z.min_l. {
    rewrite Z.mul_add_distr_r.
    apply Z.add_lt_mono_l.
    rewrite <- Z.pos_nat, <- Nat2Z.inj_mul.
    apply Nat2Z.inj_lt.
    apply Nat.nle_gt; intros Hmn.
    apply series_order_iff in Hn.
    remember ps_add as g; simpl in Hn; subst g.
    destruct Hn as (Hni, Hn).
    remember (ps_monom (coeff_of_term R h tl) 0 * ps_monom 1%K αh)%ps as v.
    simpl in Hn.
    progress unfold cm, cm_factor in Hn; simpl in Hn.
    subst v; simpl in Hn.
    progress unfold cm in Hn; simpl in Hn.
    rewrite Pos.mul_1_l in Hn.
    rewrite Z.mul_1_r in Hn.
    rewrite <- Hval in Hn; simpl in Hn.
    rewrite Z.min_l in Hn. {
      rewrite Z.sub_diag in Hn; simpl in Hn.
      rewrite Nat.sub_0_r in Hn.
      rewrite Z.min_r in Hn. {
        destruct (zerop (n mod Pos.to_nat (ps_polydo āh))) as [Hnp| Hnp]. {
          apply Nat.Div0.mod_divides in Hnp.
          destruct Hnp as (p, Hp).
          rewrite Nat.mul_comm in Hp.
          rewrite Hp in Hmn.
          apply Nat.mul_le_mono_pos_r in Hmn; [ | apply Pos2Nat.is_pos ].
          rewrite Hp in Hn.
          rewrite Nat.div_mul in Hn; auto with Arith; simpl in Hn.
          rewrite Z.mul_add_distr_r in Hn.
          rewrite Z.add_comm, Z.add_sub in Hn.
          rewrite Z2Nat.inj_mul in Hn; simpl in Hn. {
            rewrite Nat2Z.id in Hn.
            rewrite <- Hp in Hn.
            destruct (eq_nat_dec p m) as [Hpm| Hpm]. {
              subst p.
              rewrite <- Hp, Nat.sub_diag in Hn.
              destruct (lt_dec n n) as [Hnn| Hnn]. {
                revert Hnn; apply Nat.lt_irrefl.
              }
              rewrite Nat.Div0.mod_0_l in Hn; cbn in Hn.
              rewrite Nat.Div0.div_0_l in Hn; cbn in Hn.
              rewrite Nat.Div0.mod_0_l in Hn; simpl in Hn.
              rewrite rng_mul_1_r, rng_add_0_r in Hn.
              rewrite Htl in Hn.
              rewrite coeff_of_term_pt_eq in Hn.
              rewrite Hāh in Hn; simpl in Hn.
              progress unfold ps_poly_nth, ps_lap_nth in Hn; simpl in Hn.
              rewrite Hāh in Hm.
              progress unfold coeff_of_pt in Hn.
              rewrite coeff_of_hl_eq_order in Hn. {
                progress unfold order_coeff in Hn.
                progress unfold ps_poly_nth, ps_lap_nth in Hm.
                rewrite Hm in Hn.
                rewrite rng_add_opp_r in Hn.
                apply Hn; reflexivity.
              }
              subst tl; simpl in Hh.
              revert Hh; clear; intros.
              induction pl as [| (i, ai)]; [ assumption | simpl ].
              simpl in Hh.
              destruct Hh as [Hh| Hh]; [ left; assumption | idtac ].
              right; apply IHpl; assumption.
            }
            destruct (lt_dec n (m * Pos.to_nat (ps_polydo āh)))
              as [Hnp| Hnp]. {
              apply series_order_iff in Hm.
              destruct Hm as (Hmi, Hm).
              apply Nat_le_neq_lt in Hmn; [ idtac | assumption ].
              apply Hmi in Hmn.
              rewrite rng_add_0_r in Hn; contradiction.
            }
            apply Hnp.
            rewrite Hp.
            apply Nat.mul_lt_mono_pos_r; [ apply Pos2Nat.is_pos | idtac ].
            apply Nat_le_neq_lt; assumption.
          } {
            apply Nat2Z.is_nonneg.
          } {
            apply Pos2Z.is_nonneg.
          }
        }
        rewrite rng_add_0_l in Hn.
        rewrite Z.mul_add_distr_r in Hn.
        rewrite Z.add_comm, Z.add_sub in Hn.
        rewrite Z2Nat.inj_mul in Hn; simpl in Hn. {
          rewrite Nat2Z.id in Hn.
          destruct (lt_dec n (m * Pos.to_nat (ps_polydo āh))) as [Hnm| Hnm]. {
            apply Hn; reflexivity.
          }
          apply Hnm; clear Hnm.
          destruct (eq_nat_dec n (m * Pos.to_nat (ps_polydo āh)))
            as [Heq| Hne]. {
            rewrite Heq in Hnp.
            rewrite Nat.Div0.mod_mul in Hnp.
            exfalso; revert Hnp; apply Nat.lt_irrefl.
          }
          apply Nat_le_neq_lt; assumption.
        } {
          apply Nat2Z.is_nonneg.
        } {
          apply Pos2Z.is_nonneg.
        }
      }
      rewrite Z.mul_add_distr_r.
      apply Z.le_sub_le_add_l.
      rewrite Z.sub_diag, <- Z.pos_nat, <- Nat2Z.inj_mul.
      apply Nat2Z.is_nonneg.
    }
    rewrite Z.mul_add_distr_r.
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag, <- Z.pos_nat, <- Nat2Z.inj_mul.
    apply Nat2Z.is_nonneg.
  }
  apply Z.le_sub_le_add_l.
  rewrite Z.sub_diag.
  apply Nat2Z.is_nonneg.
}
rewrite Hαh.
rewrite Htl in Hh; simpl in Hh.
rewrite List.map_map in Hh.
simpl in Hh.
apply ord_is_ord_of_pt; [ idtac | assumption ].
rewrite Hpl.
eapply ini_oth_fin_pts_sorted; eassumption.
Qed.

(* [Walker, p 101] « O(āl.x^(l.γ₁)) > β₁ » *)
Theorem order_āl_xlγ₁_gt_β₁ : ∀ f L pl tl l₁ l₂ l āl,
  newton_segments f = Some L
  → pl = [ini_pt L … oth_pts L ++ [fin_pt L]]
  → tl = List.map (term_of_point f) pl
  → l₁ = List.map (λ t, power t) tl
  → split_list (List.seq 0 (length (al f))) l₁ l₂
  → l ∈ l₂
  → āl = ps_poly_nth l f
  → (order (āl * ps_monom 1%K (Qnat l * γ L))%ps >
       qfin (β L))%Qbar.
Proof.
intros f L pl tl l₁ l₂ l āl HL Hpl Htl Hl₁ Hsl Hl Hāl.
remember (āl * ps_monom 1%K (Qnat l * γ L))%ps as s eqn:Hs .
remember (series_order (ps_terms s) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]. {
  remember (points_of_ps_polynom f) as pts eqn:Hpts .
  remember Hpts as Hval; clear HeqHval.
  remember (order āl) as m eqn:Hm .
  symmetry in Hm.
  destruct m as [m| ]. {
    eapply in_pol_in_pts in Hval; try eassumption.
    remember HL as H; clear HeqH.
    eapply points_not_in_any_newton_segment with (αh := m) (h := l) in H;
    try eassumption. {
      progress unfold order, Qbar.gt.
      rewrite Hn.
      apply Qbar.qfin_lt_mono.
      remember (β L) as βL.
      remember (γ L) as γL.
      rewrite Hs, Hāl; simpl.
      progress unfold cm; simpl.
      rewrite Pos.mul_1_l.
      rewrite <- Hāl.
      eapply Q.lt_le_trans; [ eassumption | idtac ].
      progress unfold Q.le; simpl.
Search (z_pos _ = _).
...
      do 2 rewrite Pos2Z.inj_mul.
      do 2 rewrite Z.mul_assoc.
      apply Z.mul_le_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
      do 3 rewrite Z.mul_add_distr_r.
      rewrite Z.add_shuffle0.
      apply Z.add_le_mono. {
        progress unfold order in Hm.
        remember (series_order (ps_terms āl) 0) as p eqn:Hp .
        symmetry in Hp.
        destruct p as [p| ]; [ idtac | discriminate Hm ].
        injection Hm; clear Hm; intros Hm.
        rewrite <- Hm; simpl.
        do 2 rewrite Z.mul_add_distr_r.
        apply Z.add_le_mono_l.
        apply Z.mul_le_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
        rewrite <- Z.pos_nat.
        rewrite <- Nat2Z.inj_mul.
        apply Nat2Z.inj_le.
        rewrite Hs in Hn; simpl in Hn.
        progress unfold cm_factor in Hn; simpl in Hn.
        apply series_order_iff in Hn; simpl in Hn.
        apply series_order_iff in Hp; simpl in Hp.
        destruct Hn as (Hni, Hn).
        destruct Hp as (Hpi, Hp).
        progress unfold convol_mul in Hn.
        rewrite summation_only_one_non_0 with (v := n) in Hn. {
          rewrite Nat.sub_diag in Hn; simpl in Hn.
          rewrite Nat.Div0.mod_0_l in Hn; simpl in Hn.
          rewrite Nat.Div0.div_0_l in Hn; simpl in Hn.
          rewrite rng_mul_1_r in Hn.
          destruct (zerop (n mod Pos.to_nat (Qden (γL)))) as [Hng| Hng]. {
            apply Nat.Div0.mod_divides in Hng.
            destruct Hng as (g, Hg).
            rewrite Hg, Nat.mul_comm.
            apply Nat.mul_le_mono_l.
            rewrite Hg in Hn.
            rewrite Nat.mul_comm in Hn.
            rewrite Nat.div_mul in Hn; auto with Arith.
            apply Nat.nlt_ge.
            clear H; intros H.
            apply Hpi in H.
            contradiction.
          }
          exfalso; apply Hn; reflexivity.
        }
        split; [ apply Nat.le_0_l | reflexivity ].
        intros i (_, Hin) Hinn.
        apply rng_mul_eq_0.
        right.
        progress unfold series_stretch; simpl.
        destruct (zerop ((n - i) mod Pos.to_nat (ps_polydo āl)))
          as [Hz| Hz]. {
          apply Nat.Div0.mod_divides in Hz.
          destruct Hz as (c, Hc).
          rewrite Nat.mul_comm in Hc; rewrite Hc.
          rewrite Nat.div_mul; auto with Arith.
          destruct c; [ idtac | reflexivity ].
          rewrite Nat.mul_0_l in Hc.
          apply Nat.sub_0_le in Hc.
          exfalso; apply Hinn, Nat.le_antisymm; auto with Arith.
        }
        reflexivity.
      }
      rewrite Z.mul_shuffle0; reflexivity.
    }
    split; [ eassumption | idtac ].
    intros Hlm.
    apply split_list_comm in Hsl.
    eapply sorted_split_in_not_in in Hsl; try eassumption. {
      apply Hsl; clear Hsl.
      subst l₁ tl pl.
      rewrite List.map_map; simpl.
      destruct Hlm as [Hlm| Hlm]; [ now left; rewrite Hlm | ].
      right.
      rewrite List.map_app; simpl.
      apply List.in_or_app.
      destruct Hlm as [Hlm| Hlm]; [ now right; rewrite Hlm; left | ].
      left.
      revert Hlm; clear; intros.
      remember (oth_pts L) as pts; clear Heqpts.
      induction pts as [| (i, ai)]; [ contradiction | idtac ].
      destruct Hlm as [Hlm| Hlm]. {
        now injection Hlm; clear Hlm; intros; subst; left.
      }
      right; apply IHpts, Hlm.
    }
    remember (length (al f)) as len; clear.
    (* lemma to do *)
    remember 0%nat as b; clear Heqb.
    revert b.
    induction len; intros; [ constructor | simpl ].
    constructor; [ apply IHlen | idtac ].
    destruct len; constructor.
    apply Nat.lt_succ_diag_r.
  }
  progress unfold order in Hm.
  remember (series_order (ps_terms āl) 0) as v eqn:Hv .
  symmetry in Hv.
  destruct v; [ discriminate Hm | idtac ].
  apply ps_series_order_inf_iff in Hv.
  assert (s = 0)%ps as Hsz. {
    rewrite Hs.
    rewrite Hv.
    rewrite ps_mul_0_l; reflexivity.
  }
  apply order_inf in Hsz.
  rewrite Hsz; constructor.
}
progress unfold order; simpl.
rewrite Hn; constructor.
Qed.

Theorem order_mul : ∀ a b, (order (a * b)%ps = order a + order b)%Qbar.
Proof.
intros a b.
symmetry.
pose proof (ps_adjust_eq K a 0 (ps_polydo b)) as Ha.
pose proof (ps_adjust_eq K b 0 (ps_polydo a)) as Hb.
rewrite Hb in |- * at 1.
rewrite Ha in |- * at 1.
progress unfold order; simpl.
progress unfold cm_factor, cm; simpl.
do 2 rewrite series_shift_0.
remember (series_stretch (ps_polydo b) (ps_terms a)) as sa eqn:Hsa .
remember (series_stretch (ps_polydo a) (ps_terms b)) as sb eqn:Hsb .
remember (series_order sa 0) as na eqn:Hna .
remember (series_order sb 0) as nb eqn:Hnb .
remember (series_order (sa * sb)%ser 0) as nc eqn:Hnc .
symmetry in Hna, Hnb, Hnc.
destruct na as [na| ]. {
  destruct nb as [nb| ]. {
    destruct nc as [nc| ]. {
      simpl.
      rewrite Z.sub_0_r.
      rewrite Z.sub_0_r.
      progress unfold Qeq; simpl.
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
      apply series_order_iff in Hna; simpl in Hna.
      apply series_order_iff in Hnb; simpl in Hnb.
      apply series_order_iff in Hnc; simpl in Hnc.
      destruct Hna as (Hia, Hna).
      destruct Hnb as (Hib, Hnb).
      destruct Hnc as (Hic, Hnc).
      rewrite <- Nat2Z.inj_add.
      apply Nat2Z.inj_iff.
      destruct (lt_dec (na + nb) nc) as [Hlt| Hge]. {
        apply Hic in Hlt.
        progress unfold convol_mul in Hlt.
        rewrite summation_only_one_non_0 with (v := na) in Hlt. {
          rewrite Nat.add_comm, Nat.add_sub in Hlt.
          apply fld_eq_mul_0_l in Hlt; try assumption; contradiction.
        } {
          split; [ apply Nat.le_0_l | apply Nat.le_add_r ].
        }
        intros i (_, Hiab) Hina.
        destruct (lt_dec i na) as [Hilt| Hige]. {
          rewrite Hia; [ idtac | assumption ].
          rewrite rng_mul_0_l; reflexivity.
        }
        apply Nat.nlt_ge in Hige.
        rewrite Hib; [ rewrite rng_mul_0_r; reflexivity | idtac ].
        apply Nat.add_lt_mono_r with (p := i).
        rewrite Nat.sub_add; auto with Arith.
        rewrite Nat.add_comm.
        apply Nat.add_lt_mono_l, Nat_le_neq_lt; auto with Arith.
      }
      apply Nat.nlt_ge in Hge.
      destruct (lt_dec nc (na + nb)) as [Hclt| Hcge]. {
        progress unfold convol_mul in Hnc.
        rewrite all_0_summation_0 in Hnc. {
          exfalso; apply Hnc; reflexivity.
        }
        intros h (_, Hhc).
        destruct (lt_dec h na) as [Hha| Hha]. {
          rewrite Hia; [ idtac | assumption ].
          rewrite rng_mul_0_l; reflexivity.
        }
        destruct (lt_dec (nc - h) nb) as [Hhb| Hhb]. {
          rewrite Hib; [ idtac | assumption ].
          rewrite rng_mul_0_r; reflexivity.
        }
        exfalso; apply Hhb; clear Hhb.
        apply Nat.add_lt_mono_r with (p := h).
        rewrite Nat.sub_add; auto with Arith.
        eapply Nat.lt_le_trans; eauto .
        rewrite Nat.add_comm.
        apply Nat.add_le_mono_l.
        apply Nat.nlt_ge in Hha; auto with Arith.
      }
      apply Nat.nlt_ge in Hcge.
      apply Nat.le_antisymm; assumption.
    }
    exfalso.
    apply series_order_iff in Hna; simpl in Hna.
    apply series_order_iff in Hnb; simpl in Hnb.
    apply series_order_iff in Hnc; simpl in Hnc.
    destruct Hna as (Hia, Hna).
    destruct Hnb as (Hib, Hnb).
    pose proof (Hnc (na + nb)%nat) as Hnab.
    progress unfold convol_mul in Hnab.
    destruct (le_dec na nb) as [Hab| Hab]. {
      rewrite summation_only_one_non_0 with (v := na) in Hnab. {
        rewrite Nat.add_comm, Nat.add_sub in Hnab.
        apply fld_eq_mul_0_l in Hnab; try assumption; contradiction.
      } {
        split; [ apply Nat.le_0_l | apply Nat.le_add_r ].
      }
     intros i (_, Hiab) Hina.
     destruct (lt_dec i na) as [Hilt| Hige]. {
       rewrite Hia; [ idtac | assumption ].
       rewrite rng_mul_0_l; reflexivity.
     }
     apply Nat.nlt_ge in Hige.
     rewrite Hib. {
       rewrite rng_mul_0_r; reflexivity.
     }
     apply Nat.add_lt_mono_r with (p := i).
     rewrite Nat.sub_add; auto with Arith.
     rewrite Nat.add_comm.
     apply Nat.add_lt_mono_l, Nat_le_neq_lt; auto with Arith.
    }
    apply Nat.nle_gt in Hab.
    rewrite summation_only_one_non_0 with (v := na) in Hnab. {
      rewrite Nat.add_comm, Nat.add_sub in Hnab.
      apply fld_eq_mul_0_l in Hnab; try assumption; contradiction.
    } {
      split; [ apply Nat.le_0_l | apply Nat.le_add_r ].
    }
    intros i (_, Hiab) Hina.
    destruct (lt_dec i na) as [Hilt| Hige]. {
      rewrite Hia; [ idtac | assumption ].
      rewrite rng_mul_0_l; reflexivity.
    }
    apply Nat.nlt_ge in Hige.
    rewrite Hib; [ rewrite rng_mul_0_r; reflexivity | idtac ].
    apply Nat.add_lt_mono_r with (p := i).
    rewrite Nat.sub_add; auto with Arith.
    rewrite Nat.add_comm.
    apply Nat.add_lt_mono_l, Nat_le_neq_lt; auto with Arith.
  }
  simpl.
  apply series_series_order_inf_iff in Hnb.
  rewrite Hnb in Hnc.
  rewrite rng_mul_0_r in Hnc.
  simpl in Hnc.
  rewrite series_order_series_0 in Hnc.
  subst nc; constructor.
}
simpl.
apply series_series_order_inf_iff in Hna.
rewrite Hna in Hnc.
rewrite rng_mul_0_l in Hnc.
simpl in Hnc.
rewrite series_order_series_0 in Hnc.
subst nc; constructor.
Qed.

Theorem order_add : ∀ a b,
  (order (a + b)%ps ≥ Qbar.min (order a) (order b))%Qbar.
Proof.
intros a b.
progress unfold Qbar.ge.
set (k₁ := ps_polydo b).
set (k₂ := ps_polydo a).
set (v₁ := (ps_ordnum a * Zpos k₁)%Z).
set (v₂ := (ps_ordnum b * Zpos k₂)%Z).
set (n₁ := Z.to_nat (v₂ - Z.min v₁ v₂)).
set (n₂ := Z.to_nat (v₁ - Z.min v₁ v₂)).
pose proof (ps_adjust_eq K a n₂ k₁) as Ha.
pose proof (ps_adjust_eq K b n₁ k₂) as Hb.
rewrite Hb in |- * at 1.
rewrite Ha in |- * at 1.
rewrite eq_ps_add_add₂.
progress unfold ps_add₂.
progress unfold adjust_ps_from.
fold k₁ k₂.
fold v₁ v₂.
rewrite Z.min_comm.
fold n₁ n₂.
remember (adjust_ps n₂ k₁ a) as pa eqn:Hpa .
remember (adjust_ps n₁ k₂ b) as pb eqn:Hpb .
progress unfold order; simpl.
remember (ps_terms pa) as sa eqn:Hsa .
remember (ps_terms pb) as sb eqn:Hsb .
remember (series_order sa 0) as na eqn:Hna .
remember (series_order sb 0) as nb eqn:Hnb .
remember (series_order (sa + sb)%ser 0) as nc eqn:Hnc .
symmetry in Hna, Hnb, Hnc.
destruct na as [na| ]. {
  destruct nb as [nb| ]. {
    destruct nc as [nc| ]; [ simpl | constructor ].
    apply Qbar.le_qfin.
    rewrite Hpa, Hpb; simpl.
    subst k₁ k₂ n₁ n₂; simpl.
    subst v₁ v₂; simpl.
    rewrite Pos.mul_comm.
    rewrite Qmin_same_den.
    progress unfold Qle; simpl.
    apply Z.mul_le_mono_nonneg_r; [ apply Pos2Z.is_nonneg | idtac ].
    remember (ps_ordnum a * Zpos (ps_polydo b))%Z as ab.
    remember (ps_ordnum b * Zpos (ps_polydo a))%Z as ba.
    rewrite Z2Nat.id. {
      rewrite Z2Nat.id. {
        rewrite Z.sub_sub_distr.
        rewrite Z.sub_diag, Z.add_0_l.
        rewrite Z.sub_sub_distr.
        rewrite Z.sub_diag, Z.add_0_l.
        rewrite Z.add_min_distr_l.
        apply Z.add_le_mono_l.
        rewrite <- Nat2Z.inj_min.
        apply Nat2Z.inj_le.
        apply series_order_iff in Hna; simpl in Hna.
        apply series_order_iff in Hnb; simpl in Hnb.
        apply series_order_iff in Hnc; simpl in Hnc.
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
      }
      rewrite <- Z.sub_max_distr_l.
      rewrite Z.sub_diag.
      rewrite Z.max_comm, <- Z2Nat_id_max.
      apply Nat2Z.is_nonneg.
    }
    rewrite <- Z.sub_max_distr_l.
    rewrite Z.sub_diag.
    rewrite <- Z2Nat_id_max.
    apply Nat2Z.is_nonneg.
  }
  destruct nc as [nc| ]; [ simpl | constructor ].
  apply Qbar.le_qfin.
  progress unfold Qle; simpl.
  apply Z.mul_le_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
  apply Z.add_le_mono_l.
  apply Nat2Z.inj_le.
  apply series_series_order_inf_iff in Hnb.
  rewrite Hnb in Hnc.
  rewrite rng_add_0_r in Hnc.
  rewrite Hna in Hnc.
  injection Hnc; intros; subst na; reflexivity.
}
simpl.
apply series_series_order_inf_iff in Hna.
rewrite Hna in Hnc.
rewrite rng_add_0_l in Hnc.
rewrite Hnb in Hnc; subst nc.
destruct nb as [nb| ]; [ idtac | constructor ].
apply Qbar.le_qfin.
rewrite Hpa, Hpb; simpl.
subst k₁ k₂ n₁ n₂; simpl.
subst v₁ v₂; simpl.
rewrite Pos.mul_comm.
progress unfold Qle; simpl.
apply Z.mul_le_mono_pos_r; [ apply Pos2Z.is_pos | idtac ].
apply Z.add_le_mono_r.
rewrite Z2Nat.id. {
  rewrite Z2Nat.id. {
    do 2 rewrite Z.sub_sub_distr.
    do 2 rewrite Z.sub_diag; simpl.
    reflexivity.
  }
  rewrite <- Z.sub_max_distr_l.
  rewrite Z.sub_diag.
  rewrite <- Z2Nat_id_max.
  apply Nat2Z.is_nonneg.
}
rewrite <- Z.sub_max_distr_l.
rewrite Z.sub_diag.
rewrite Z.max_comm.
rewrite <- Z2Nat_id_max.
apply Nat2Z.is_nonneg.
Qed.

Theorem list_in_ps_lap_in : ∀ a l,
  (a ≠ 0)%ps
  → a ∈ l
  → ps_lap_in a l.
Proof.
intros a l Ha Hal.
revert a Ha Hal.
induction l as [| x]; intros; [ assumption | idtac ].
destruct Hal as [Hal| Hal]. {
  subst a; left; split; [ idtac | reflexivity ].
  intros H.
  apply lap_eq_cons_nil_inv in H.
  destruct H; contradiction.
}
right; apply IHl; assumption.
Qed.

Theorem ps_lap_nilp : ∀ la : list (puiseux_series α),
  {@lap_eq _ (ps_ring K) la []} +
  {not (@lap_eq _ (ps_ring K) la [])}.
Proof.
intros la.
induction la as [| a]; [ left; reflexivity | idtac ].
destruct IHla as [IHla| IHla]. {
  destruct (ps_zerop _ a) as [Ha| Ha]. {
    left.
    rewrite IHla, Ha.
    constructor; reflexivity.
  }
  right.
  intros H; apply Ha.
  apply lap_eq_cons_nil_inv in H.
  destruct H; assumption.
}
right.
intros H; apply IHla.
apply lap_eq_cons_nil_inv in H.
destruct H; assumption.
Qed.

Theorem ps_lap_in_add : ∀ la lb,
  (∀ m, ps_lap_in m la → (order m > 0)%Qbar)
  → (∀ m, ps_lap_in m lb → (order m > 0)%Qbar)
  → (∀ m, ps_lap_in m (la + lb) → (order m > 0)%Qbar).
Proof.
intros la lb Hla Hlb m Hlab.
progress unfold ps_lap_add in Hlab.
destruct (ps_lap_nilp la) as [Hlaz| Hlanz]. {
  rewrite Hlaz in Hlab.
  rewrite lap_add_nil_l in Hlab.
  apply Hlb; assumption.
}
destruct (ps_lap_nilp lb) as [Hlbz| Hlbnz]. {
  rewrite Hlbz in Hlab.
  rewrite lap_add_nil_r in Hlab.
  apply Hla; assumption.
}
revert lb Hlb Hlab Hlbnz.
induction la as [| a]; intros. {
  simpl in Hlab.
  apply Hlb; assumption.
}
rename m into n.
simpl in Hlab.
destruct lb as [| b]; [ apply Hla; assumption | idtac ].
simpl in Hlab.
destruct Hlab as [(Hlab, Hab)| Hlab]. {
  rewrite <- Hab.
  pose proof (order_add a b) as H.
  assert (order a > 0)%Qbar as Ha. {
    apply Hla.
    left; split; [ assumption | reflexivity ].
  }
  assert (order b > 0)%Qbar as Hb. {
    apply Hlb.
    left; split; [ assumption | reflexivity ].
  }
  progress unfold Qbar.ge in H.
  progress unfold Qbar.gt in Ha, Hb.
  destruct (Qbar.min_dec (order a) (order b)) as [Hoab| Hoab]. {
    rewrite Hoab in H.
    eapply Qbar.lt_le_trans; [ idtac | eassumption ].
    assumption.
  }
  rewrite Hoab in H.
  eapply Qbar.lt_le_trans; [ idtac | eassumption ].
  assumption.
}
destruct (ps_zerop _ a) as [Haz| Hanz]. {
  rewrite Haz in Hlanz.
  destruct (ps_zerop _ b) as [Hbz| Hbnz]. {
    rewrite Hbz in Hlbnz.
    eapply IHla. {
      intros m Hm; apply Hla; right; assumption.
    } {
      intros HH; apply Hlanz.
      constructor; [ reflexivity | assumption ].
    } {
      intros m Hm; apply Hlb; right; eassumption.
    } {
      assumption.
    }
    intros HH; apply Hlbnz.
    constructor; [ reflexivity | assumption ].
  }
  clear Hlbnz.
  destruct (ps_lap_nilp lb) as [Hlbz| Hlbnz]. {
    rewrite Hlbz in Hlab.
    rewrite lap_add_nil_r in Hlab.
    apply Hla; right; assumption.
  }
  eapply IHla. {
    intros m Hm; apply Hla; right; assumption.
  } {
    intros HH; apply Hlanz.
    constructor; [ reflexivity | assumption ].
  } {
    intros m Hm; apply Hlb; right; eassumption.
  } {
    assumption.
  }
  assumption.
}
destruct (ps_zerop _ b) as [Hbz| Hbnz]. {
  rewrite Hbz in Hlbnz.
  clear Hlanz.
  destruct (ps_lap_nilp la) as [Hlaz| Hlanz]. {
    rewrite Hlaz in Hlab.
    rewrite lap_add_nil_l in Hlab.
    apply Hlb; right; assumption.
  }
  eapply IHla. {
    intros m Hm; apply Hla; right; assumption.
  } {
    assumption.
  } {
    intros m Hm; apply Hlb; right; eassumption.
  } {
    assumption.
  }
  intros HH; apply Hlbnz.
  constructor; [ reflexivity | assumption ].
}
clear Hlanz.
clear Hlbnz.
destruct (ps_lap_nilp la) as [Hlaz| Hlanz]. {
  rewrite Hlaz in Hlab.
  rewrite lap_add_nil_l in Hlab.
  apply Hlb; right; assumption.
}
destruct (ps_lap_nilp lb) as [Hlbz| Hlbnz]. {
  rewrite Hlbz in Hlab.
  rewrite lap_add_nil_r in Hlab.
  apply Hla; right; assumption.
}
eapply IHla. {
  intros m Hm; apply Hla; right; assumption.
} {
  assumption.
} {
  intros m Hm; apply Hlb; right; eassumption.
} {
  assumption.
} {
  assumption.
}
Qed.

(* very close to 'ps_lap_in_add'. Is there a way to have only one theorem?
   or a theorem grouping these two together? *)
Theorem ps_lap_in_add_ge : ∀ la lb,
  (∀ m, ps_lap_in m la → (order m ≥ 0)%Qbar)
  → (∀ m, ps_lap_in m lb → (order m ≥ 0)%Qbar)
    → (∀ m, ps_lap_in m (la + lb) → (order m ≥ 0)%Qbar).
Proof.
intros la lb Hla Hlb m Hlab.
progress unfold ps_lap_add in Hlab.
destruct (ps_lap_nilp la) as [Hlaz| Hlanz]. {
  rewrite Hlaz in Hlab.
  rewrite lap_add_nil_l in Hlab.
  apply Hlb; assumption.
}
destruct (ps_lap_nilp lb) as [Hlbz| Hlbnz]. {
  rewrite Hlbz in Hlab.
  rewrite lap_add_nil_r in Hlab.
  apply Hla; assumption.
}
revert lb Hlb Hlab Hlbnz.
induction la as [| a]; intros. {
  simpl in Hlab.
  apply Hlb; assumption.
}
rename m into n.
simpl in Hlab.
destruct lb as [| b]; [ apply Hla; assumption | idtac ].
simpl in Hlab.
destruct Hlab as [(Hlab, Hab)| Hlab]. {
  rewrite <- Hab.
  pose proof (order_add a b) as H.
  assert (order a ≥ 0)%Qbar as Ha. {
    apply Hla.
    left; split; [ assumption | reflexivity ].
  }
  assert (order b ≥ 0)%Qbar as Hb. {
    apply Hlb.
    left; split; [ assumption | reflexivity ].
  }
  progress unfold Qbar.ge in H.
  destruct (Qbar.min_dec (order a) (order b)) as [Hoab| Hoab]. {
    rewrite Hoab in H.
    eapply Qbar.le_trans; [ idtac | eassumption ].
    assumption.
  }
  rewrite Hoab in H.
  eapply Qbar.le_trans; [ idtac | eassumption ].
  assumption.
}
destruct (ps_zerop _ a) as [Haz| Hanz]. {
  rewrite Haz in Hlanz.
  destruct (ps_zerop _ b) as [Hbz| Hbnz]. {
    rewrite Hbz in Hlbnz.
    eapply IHla. {
      intros m Hm; apply Hla; right; assumption.
    } {
      intros HH; apply Hlanz.
      constructor; [ reflexivity | assumption ].
    } {
      intros m Hm; apply Hlb; right; eassumption.
    } {
      assumption.
    }
    intros HH; apply Hlbnz.
    constructor; [ reflexivity | assumption ].
  }
  clear Hlbnz.
  destruct (ps_lap_nilp lb) as [Hlbz| Hlbnz]. {
    rewrite Hlbz in Hlab.
    rewrite lap_add_nil_r in Hlab.
    apply Hla; right; assumption.
  }
  eapply IHla. {
    intros m Hm; apply Hla; right; assumption.
  } {
    intros HH; apply Hlanz.
    constructor; [ reflexivity | assumption ].
  } {
    intros m Hm; apply Hlb; right; eassumption.
  } {
    assumption.
  } {
    assumption.
  }
}
destruct (ps_zerop _ b) as [Hbz| Hbnz]. {
  rewrite Hbz in Hlbnz.
  clear Hlanz.
  destruct (ps_lap_nilp la) as [Hlaz| Hlanz]. {
    rewrite Hlaz in Hlab.
    rewrite lap_add_nil_l in Hlab.
    apply Hlb; right; assumption.
  }
  eapply IHla. {
    intros m Hm; apply Hla; right; assumption.
  } {
    assumption.
  } {
    intros m Hm; apply Hlb; right; eassumption.
  } {
    assumption.
  }
  intros HH; apply Hlbnz.
  constructor; [ reflexivity | assumption ].
}
clear Hlanz.
clear Hlbnz.
destruct (ps_lap_nilp la) as [Hlaz| Hlanz]. {
  rewrite Hlaz in Hlab.
  rewrite lap_add_nil_l in Hlab.
  apply Hlb; right; assumption.
}
destruct (ps_lap_nilp lb) as [Hlbz| Hlbnz]. {
  rewrite Hlbz in Hlab.
  rewrite lap_add_nil_r in Hlab.
  apply Hla; right; assumption.
}
eapply IHla. {
  intros m Hm; apply Hla; right; assumption.
} {
  assumption.
} {
  intros m Hm; apply Hlb; right; eassumption.
} {
  assumption.
} {
  assumption.
}
Qed.

Theorem ps_lap_in_mul : ∀ la lb,
  (∀ m, ps_lap_in m la → (order m > 0)%Qbar)
  → (∀ m, ps_lap_in m lb → (order m ≥ 0)%Qbar)
    → (∀ m, ps_lap_in m (la * lb) → (order m > 0)%Qbar).
Proof.
intros la lb Hla Hlb m Hlab.
progress unfold ps_lap_mul in Hlab.
revert m lb Hlb Hlab.
induction la as [| a]; intros. {
  rewrite lap_mul_nil_l in Hlab; contradiction.
}
rewrite lap_mul_cons_l in Hlab.
eapply ps_lap_in_add; [ idtac | idtac | eassumption ]. {
  intros n Hn.
  destruct (ps_zerop _ a) as [Ha| Ha]. {
    rewrite Ha in Hn.
    rewrite lap_eq_0 in Hn.
    rewrite lap_mul_nil_l in Hn; contradiction.
  }
  assert (order a > 0)%Qbar as Hoa. {
    apply Hla; left; split; [ idtac | reflexivity ].
    intros H.
    apply lap_eq_cons_nil_inv in H.
    destruct H; contradiction.
  }
  revert Hlb Hn Hoa; clear -K; intros.
  rewrite lap_mul_const_l in Hn.
  induction lb as [| b]; [ contradiction | idtac ].
  simpl in Hn.
  destruct Hn as [(Hab, Hn)| Hn]. {
    rewrite <- Hn, order_mul.
    eapply Qbar.lt_le_trans; [ eassumption | idtac ].
    apply Qbar.le_sub_le_add_l.
    rewrite Qbar.sub_diag.
    destruct (ps_zerop _ b) as [Hb| Hb]. {
      rewrite Hb, order_0; constructor.
    }
    apply Hlb; left; split; [ idtac | reflexivity ].
    intros H; apply Hb.
    apply lap_eq_cons_nil_inv in H.
    destruct H; assumption.
  }
  apply IHlb; [ idtac | assumption ].
  intros p Hp.
  apply Hlb; right; assumption.
}
intros n Hn.
simpl in Hn.
destruct Hn as [(Hab, Hn)| Hn].
symmetry in Hn.
rewrite Hn, order_0; constructor.
eapply IHla; try eassumption.
intros p Hp.
apply Hla; right; assumption.
Qed.

Theorem ps_lap_in_mul_ge : ∀ la lb,
  (∀ m, ps_lap_in m la → (order m ≥ 0)%Qbar)
  → (∀ m, ps_lap_in m lb → (order m ≥ 0)%Qbar)
    → (∀ m, ps_lap_in m (la * lb) → (order m ≥ 0)%Qbar).
Proof.
intros la lb Hla Hlb m Hlab.
progress unfold ps_lap_mul in Hlab.
revert m lb Hlb Hlab.
induction la as [| a]; intros.
 rewrite lap_mul_nil_l in Hlab; contradiction.

 rewrite lap_mul_cons_l in Hlab.
 eapply ps_lap_in_add_ge; [ idtac | idtac | eassumption ].
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

    revert Hlb Hn Hoa; clear -K; intros.
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

Theorem ps_lap_in_summation : ∀ f l,
  (∀ i, i ∈ l → ∀ m, ps_lap_in m (f i) → (order m > 0)%Qbar)
  → (∀ m, ps_lap_in m (ps_lap_summ ps_field l f) → (order m > 0)%Qbar).
Proof.
intros f l Hi m Hm.
revert m Hm.
induction l as [| j]; intros; [ contradiction | idtac ].
simpl in Hm.
apply ps_lap_in_add in Hm; [ assumption | idtac | idtac ].
 intros n Hn.
 apply IHl; [ idtac | assumption ].
 intros k Hk p Hp.
 eapply Hi; [ idtac | eassumption ].
 right; assumption.

 intros k Hk.
 eapply Hi; [ idtac | eassumption ].
 left; reflexivity.
Qed.

Theorem ps_monom_order : ∀ c n, (c ≠ 0)%K → order (ps_monom c n) = qfin n.
Proof.
intros c n Hc.
progress unfold order.
remember (series_order (ps_terms (ps_monom c n)) 0) as m eqn:Hm .
symmetry in Hm.
apply series_order_iff in Hm.
simpl in Hm; simpl.
destruct m as [m| ].
 destruct Hm as (Him, Hm).
 destruct m as [| m]; [ simpl | exfalso; apply Hm; reflexivity ].
 simpl in Hm.
 rewrite Z.add_0_r; destruct n; reflexivity.

 pose proof (Hm 0%nat); contradiction.
Qed.

Theorem ps_monom_0_order : ∀ c n, (c = 0)%K → order (ps_monom c n) = qinf.
Proof.
intros c n Hc.
progress unfold order.
remember (series_order (ps_terms (ps_monom c n)) 0) as m eqn:Hm .
symmetry in Hm.
apply series_order_iff in Hm.
simpl in Hm; simpl.
destruct m as [m| ]; [ exfalso | reflexivity ].
destruct Hm as (Him, Hm).
destruct m as [| m]; apply Hm; [ assumption | reflexivity ].
Qed.

Theorem ps_monom_order_ge : ∀ c n, (order (ps_monom c n) ≥ qfin n)%Qbar.
Proof.
intros c n.
progress unfold order.
remember (series_order (ps_terms (ps_monom c n)) 0) as m eqn:Hm .
symmetry in Hm.
progress unfold Qbar.ge.
destruct m as [m| ]; [ idtac | constructor ].
apply Qbar.le_qfin.
apply series_order_iff in Hm.
simpl in Hm; simpl.
destruct Hm as (Him, Hm).
destruct m as [| m]; [ simpl | exfalso; apply Hm; reflexivity ].
simpl in Hm.
rewrite Z.add_0_r; destruct n; simpl.
progress unfold Qle; simpl; reflexivity.
Qed.

Theorem ps_lap_in_power : ∀ la n,
  (∀ a, ps_lap_in a la → (order a ≥ 0)%Qbar)
  → (∀ m, ps_lap_in m (la ^ n) → (order m ≥ 0)%Qbar).
Proof.
intros la n Ha m Hm.
revert m la Ha Hm.
induction n; intros.
 simpl in Hm.
 destruct Hm as [(H₁, Hm)| ]; [ idtac | contradiction ].
 rewrite <- Hm.
 apply ps_monom_order_ge.

 simpl in Hm.
 eapply ps_lap_in_mul_ge in Hm; try eassumption.
 intros p Hp.
 eapply IHn; eassumption.
Qed.

(* [Walker, p 101 « each power of y₁ in g(x,y₁) has a coefficient of
   positive order » *)
Theorem each_power_of_y₁_in_g_has_coeff_pos_ord : ∀ f L g,
  newton_segments f = Some L
  → g = g_of_ns f L
    → ∀ m, m ∈ al g → (order m > 0)%Qbar.
Proof.
intros f L g HL Hg m Hm.
remember (al g) as la eqn:Hla .
subst g.
progress unfold g_of_ns, g_lap_of_ns in Hla.
remember (ac_root (Φq f L)) as c₁ eqn:Hc₁ .
remember [ini_pt L … oth_pts L ++ [fin_pt L]] as pl eqn:Hpl .
remember (List.map (term_of_point f) pl) as tl eqn:Htl .
remember (List.map (λ t, power t) tl) as l₁ eqn:Hl₁ .
remember (list_seq_except 0 (length (al f)) l₁) as l₂ eqn:Hl₂ .
simpl in Hla.
remember (order m) as om eqn:Hom .
symmetry in Hom.
destruct om as [om| ]; [ idtac | constructor ].
assert (m ≠ 0)%ps as Hmnz. {
  intros H.
  apply order_inf in H.
  rewrite H in Hom; discriminate Hom.
}
subst la.
apply list_in_ps_lap_in in Hm; [ idtac | assumption ].
progress progress unfold ps_lap_add in Hm.
progress progress unfold ps_lap_mul in Hm.
rewrite lap_mul_add_distr_l in Hm.
rewrite <- Hom.
apply ps_lap_in_add in Hm; [ assumption | idtac | idtac ]. {
  clear m om Hom Hmnz Hm.
  intros m Hm.
  progress progress unfold ps_lap_summ in Hm.
  rewrite lap_mul_summation in Hm.
  eapply ps_lap_in_summation; [ idtac | eassumption ].
  clear m Hm.
  intros h Hh m Hm.
  simpl in Hm.
  rewrite lap_mul_assoc in Hm.
  apply ps_lap_in_mul in Hm; [ assumption | idtac | idtac ]. {
    clear m Hm.
    intros m Hm.
    remember (ps_poly_nth h f) as āh eqn:Hāh .
    remember (ps_monom (coeff_of_term R h tl) 0) as ah eqn:Hah .
    remember (ord_of_pt h pl) as αh eqn:Hαh .
    rewrite lap_mul_const_l in Hm; simpl in Hm.
    destruct Hm as [(Hmnz, Hm)| ]; [ idtac | contradiction ].
    rewrite <- Hm; simpl.
    rewrite order_mul.
    remember (āh - ah * ps_monom 1%K αh)%ps as aa.
    remember (ps_monom 1%K (Qnat h * γ L))%ps as bb.
    remember (ps_monom 1%K (- β L)) as cc.
    remember (order (aa * bb)) as oaa.
    apply Qbar.lt_le_trans with (m := (qfin (- β L) + oaa)%Qbar). {
      subst oaa.
      rewrite order_mul.
      rewrite Qbar.add_comm.
      rewrite Heqaa, Heqbb.
      apply Qbar.le_lt_trans with (m := qfin (αh + Qnat h * γ L - β L)). {
        apply Qbar.le_qfin.
        apply Qplus_le_l with (z := β L).
        rewrite <- Q_sub_sub_distr.
        rewrite Qminus_diag.
        rewrite Q_add_0_l.
        progress unfold Qminus, Qopp; simpl.
        rewrite Q_add_0_r.
        remember (points_of_ps_polynom f) as pts.
        eapply points_in_convex; try eassumption.
        eapply in_pol_in_pts; try eassumption.
        rewrite Hāh.
        eapply order_in_newton_segment; try eassumption.
        rewrite Hαh.
        apply ord_is_ord_of_pt. {
          rewrite Hpl.
          eapply ini_oth_fin_pts_sorted; eassumption.
        }
        rewrite Hl₁, Htl in Hh.
        rewrite List.map_map in Hh; assumption.
      }
      progress unfold Qminus.
      rewrite Qbar.qfin_inj_add.
      apply Qbar.add_lt_mono_r; [ intros H; discriminate H | idtac ].
      rewrite Qbar.qfin_inj_add.
      apply Qbar.add_lt_le_mono; [ intros H; discriminate H | | ]. {
        rewrite Hl₁ in Hh.
        eapply order_āh_minus_ah_xαh_gt_αh; eassumption.
      }
      apply ps_monom_order_ge.
    }
    destruct oaa as [oaa| ]. {
      apply Qbar.add_le_mono_r; [ intros H; discriminate H | idtac ].
      subst cc; apply ps_monom_order_ge.
    }
    simpl.
    rewrite Qbar.add_comm; constructor.
  }
  clear m Hm.
  intros m Hm.
  eapply ps_lap_in_power; [ idtac | eassumption ].
  clear m Hm.
  intros m Hm.
  simpl in Hm.
  destruct Hm as [(Hn, Hm)| Hm]. {
    rewrite <- Hm.
    apply ps_monom_order_ge.
  }
  destruct Hm as [(Hn, Hm)| ]; [ idtac | contradiction ].
  rewrite <- Hm.
  apply ps_monom_order_ge.
}
clear m om Hom Hmnz Hm.
intros m Hm.
progress progress unfold ps_lap_summ in Hm.
rewrite lap_mul_summation in Hm.
eapply ps_lap_in_summation; [ idtac | eassumption ].
clear m Hm.
intros h Hh m Hm.
simpl in Hm.
rewrite lap_mul_assoc in Hm.
apply ps_lap_in_mul in Hm; [ assumption | idtac | idtac ]. {
  clear m Hm.
  intros m Hm.
  simpl in Hm.
  destruct Hm as [(H₁, H₂)| Hm]; [ idtac | contradiction ].
  progress unfold summation in H₁, H₂; simpl in H₁, H₂.
  rewrite ps_add_0_r in H₂.
  rewrite <- H₂.
  rewrite order_mul.
  remember (ps_poly_nth h f) as āh.
  apply Qbar.lt_sub_lt_add_l; [ intros H; discriminate H | idtac ].
  rewrite Qbar.sub_0_l.
  destruct (fld_zerop 1%K) as [Hoz| Honz]. {
    rewrite ps_monom_0_order; [ simpl | assumption ].
    rewrite order_mul.
    rewrite ps_monom_0_order; [ simpl | assumption ].
    rewrite Qbar.add_comm; constructor.
  }
  rewrite ps_monom_order; [ simpl | assumption ].
  rewrite Q_opp_involutive.
  eapply order_āl_xlγ₁_gt_β₁; try eassumption.
  apply except_split_seq; [ idtac | idtac | assumption ]. {
    subst l₁ tl.
    rewrite List.map_map; simpl.
    apply Sorted_map; simpl.
    remember HL as Hsort; clear HeqHsort.
    apply ini_oth_fin_pts_sorted in Hsort.
    rewrite <- Hpl in Hsort.
    revert Hsort; clear; intros.
    induction pl as [| p]; [ constructor | idtac ].
    apply Sorted_inv in Hsort.
    destruct Hsort as (Hsort, Hrel).
    constructor; [ now apply IHpl | ].
    revert Hrel; clear; intros.
    induction pl as [| q]; constructor.
    apply HdRel_inv in Hrel.
    easy.
  }
  subst l₁; simpl.
  apply List.Forall_forall; intros i Hi.
  split; [ apply Nat.le_0_l | idtac ].
  subst tl; simpl in Hi.
  rewrite List.map_map in Hi.
  simpl in Hi.
  revert HL Hpl Hi; clear; intros.
  apply ord_is_ord_of_pt in Hi. {
    rewrite Hpl in Hi at 2.
    progress unfold newton_segments in HL.
    eapply ns_in_init_pts in Hi; [ idtac | eassumption ].
    eapply in_pts_in_pol with (def := 0%ps) in Hi; try reflexivity.
    destruct Hi as (Hi, Ho).
    apply Nat.nle_gt.
    intros H.
    apply List.nth_overflow with (d := 0%ps) in H.
    rewrite H in Ho.
    rewrite order_0 in Ho.
    discriminate Ho.
  }
  rewrite Hpl.
  eapply ini_oth_fin_pts_sorted; eassumption.
}
intros pt Hpt.
subst pl.
eapply ps_lap_in_power; [ idtac | eassumption ].
intros a Ha.
simpl in Ha.
destruct Ha as [(Hn, Ha)| Ha].
rewrite <- Ha.
apply ps_monom_order_ge.
destruct Ha as [(_, Ha)| Ha]; [ idtac | contradiction ].
rewrite <- Ha; simpl.
apply ps_monom_order_ge.
Qed.

End theorems.
