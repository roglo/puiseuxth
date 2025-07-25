(* F1Prop.v *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Sorted.

Require Import A_PosArith A_ZArith A_QArith.
Require Import Misc.
Require Import QbarM.
Require Import SplitList.
Require Import Field2.
Require Import Fpolynomial.
Require Import Fsummation.
Require Import Newton.
Require Import ConvexHullMisc.
Require Import ConvexHull.
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
Require Import PosOrder.
Require Import InK1m.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Theorem eq_poly_lap_add : ∀ α (R : ring α) la lb,
  (POL la + POL lb = POL (la + lb)%lap)%pol.
Proof. reflexivity. Qed.

Theorem ps_poly_lap_summ : ∀ f g l,
  (∀ i, (f i = POL (g i))%pspol)
  → (ps_pol_summ ps_field l f = POL (ps_lap_summ ps_field l g))%pspol.
Proof.
intros f g l Hi.
unfold ps_pol_eq, ps_pol in Hi.
unfold ps_pol_eq, ps_pol, ps_pol_summ, ps_lap_summ.
induction l as [| x]; [ reflexivity | simpl ].
rewrite <- eq_poly_lap_add.
rewrite <- IHl, <- Hi.
reflexivity.
Qed.

(* things similar with order_add, perhaps good theorems? *)
Theorem order_add_eq_min : ∀ a b,
  (order a ≠ order b)%Qbar
  → (order (a + b) = Qbar.min (order a) (order b))%Qbar.
Proof.
intros a b Hab.
set (k₁ := ps_polydo b).
set (k₂ := ps_polydo a).
set (v₁ := (ps_ordnum a * z_pos k₁)%Z).
set (v₂ := (ps_ordnum b * z_pos k₂)%Z).
set (n₁ := Z.to_nat (v₂ - Z.min v₁ v₂)).
set (n₂ := Z.to_nat (v₁ - Z.min v₁ v₂)).
pose proof (ps_adjust_eq K a n₂ k₁) as Ha.
pose proof (ps_adjust_eq K b n₁ k₂) as Hb.
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
remember (adjust_ps n₂ k₁ a) as pa eqn:Hpa .
remember (adjust_ps n₁ k₂ b) as pb eqn:Hpb .
remember (order pa) as opa eqn:Hopa .
remember (order pb) as opb eqn:Hopb .
progress unfold order in Hopa, Hopb.
progress unfold order; simpl.
remember (ps_terms pa) as sa eqn:Hsa .
remember (ps_terms pb) as sb eqn:Hsb .
remember (series_order sa 0) as na eqn:Hna .
remember (series_order sb 0) as nb eqn:Hnb .
remember (series_order (sa + sb)%ser 0) as nc eqn:Hnc .
symmetry in Hna, Hnb, Hnc.
clear Hsa Hsb Ha Hb.
apply series_order_iff in Hna; simpl in Hna.
apply series_order_iff in Hnb; simpl in Hnb.
apply series_order_iff in Hnc; simpl in Hnc.
destruct na as [na| ]. {
  destruct Hna as (Hina, Hna).
  destruct nb as [nb| ]. {
    destruct Hnb as (Hinb, Hnb).
    subst pa pb; simpl in Hopa, Hopb; simpl.
    subst k₁ k₂ n₁ n₂; simpl in Hopa, Hopb; simpl.
    subst v₁ v₂; simpl in Hopa, Hopb.
    rewrite Pos.mul_comm in Hopb.
    rewrite Z2Nat.id in Hopa. {
      rewrite Z2Nat.id in Hopb. {
        rewrite Z.sub_sub_distr in Hopa, Hopb.
        rewrite Z.sub_diag, Z.add_0_l in Hopa, Hopb.
        unfold cm_factor; simpl.
        rewrite Z2Nat.id. {
          rewrite Z.sub_sub_distr.
          rewrite Z.sub_diag, Z.add_0_l.
          subst opa opb; simpl.
          rewrite Qmin_same_den.
          progress unfold Q.eq; simpl.
          simpl in Hab.
          unfold Q.eq in Hab; simpl in Hab.
          destruct nc as [nc| ]. {
            destruct Hnc as (Hinc, Hnc).
            apply Z.compare_eq_iff; cbn.
            do 2 rewrite q_Den_num_den.
            rewrite Z.add_min_distr_l.
            rewrite <- Nat2Z.inj_min.
            f_equal; f_equal; f_equal.
            destruct (Nat.eq_dec (min na nb) nc) as [| H]; [ easy | ].
            exfalso; apply Hab; clear Hab.
            apply Z.compare_eq_iff; cbn.
            do 2 rewrite q_Den_num_den.
            f_equal; f_equal; f_equal.
            destruct (Nat.eq_dec na nb) as [| Hab]; [ easy |].
            exfalso; apply H; clear H.
            destruct (le_dec na nb) as [H₁| H₁]. {
              apply Nat_le_neq_lt in H₁; [ idtac | assumption ].
              destruct (lt_dec na nc) as [H₂| H₂]. {
                apply Hinb in H₁.
                apply Hinc in H₂.
                rewrite H₁, rng_add_0_r in H₂; contradiction.
              }
              apply Nat.nlt_ge in H₂.
              destruct (eq_nat_dec na nc) as [H₃| H₃]. {
                rewrite Nat.min_l; [ assumption | idtac ].
                apply Nat.lt_le_incl; assumption.
              }
              apply Nat.neq_sym in H₃.
              apply Nat_le_neq_lt in H₂; [ idtac | assumption ].
              eapply Nat.lt_trans in H₁; [ idtac | eassumption ].
              apply Hina in H₂.
              apply Hinb in H₁.
              rewrite H₂, H₁ in Hnc.
              rewrite rng_add_0_l in Hnc.
              exfalso; apply Hnc; reflexivity.
            }
            apply Nat.nle_gt in H₁.
            destruct (lt_dec nb nc) as [H₂| H₂]. {
              apply Hina in H₁.
              apply Hinc in H₂.
              rewrite H₁, rng_add_0_l in H₂; contradiction.
            }
            apply Nat.nlt_ge in H₂.
            destruct (eq_nat_dec nb nc) as [H₃| H₃]. {
              rewrite Nat.min_r; [ assumption | idtac ].
              apply Nat.lt_le_incl; assumption.
            }
            apply Nat.neq_sym in H₃.
            apply Nat_le_neq_lt in H₂; [ idtac | assumption ].
            eapply Nat.lt_trans in H₁; [ idtac | eassumption ].
            apply Hinb in H₂.
            apply Hina in H₁.
            rewrite H₂, H₁ in Hnc.
            rewrite rng_add_0_l in Hnc.
            exfalso; apply Hnc; reflexivity.
          }
          simpl in Hab.
          apply Hab; clear Hab.
          apply Z.compare_eq_iff; cbn.
          do 2 rewrite q_Den_num_den.
          f_equal; f_equal; f_equal.
          destruct (eq_nat_dec na nb) as [| Hab]; [ assumption | idtac ].
          destruct (le_dec na nb) as [H₁| H₁]. {
            apply Nat_le_neq_lt in H₁; [ idtac | assumption ].
            apply Hinb in H₁.
            pose proof (Hnc na) as H.
            rewrite H₁, rng_add_0_r in H.
            contradiction.
          }
          apply Nat.nle_gt in H₁.
          apply Hina in H₁.
          pose proof (Hnc nb) as H.
          rewrite H₁, rng_add_0_l in H.
          contradiction.
        }
        rewrite <- Z.sub_max_distr_l.
        rewrite Z.sub_diag.
        apply Z.le_max_l.
      }
      rewrite <- Z.sub_max_distr_l.
      rewrite Z.sub_diag.
      apply Z.le_max_r.
    }
    rewrite <- Z.sub_max_distr_l.
    rewrite Z.sub_diag.
    apply Z.le_max_l.
  }
  subst opb; simpl.
  rewrite Qbar.min_comm; simpl.
  destruct nc as [nc| ]. {
    destruct Hnc as (Hinc, Hnc).
    subst opa.
    apply Qbar.qfin_inj_wd.
    unfold Q.eq; simpl.
    apply Z.compare_eq_iff; cbn.
    do 2 rewrite q_Den_num_den.
    f_equal; f_equal; f_equal.
    destruct (eq_nat_dec na nc) as [| Hac]; [ assumption | idtac ].
    destruct (le_dec na nc) as [H₁| H₁]. {
      apply Nat_le_neq_lt in H₁; [ idtac | assumption ].
      apply Hinc in H₁.
      rewrite Hnb, rng_add_0_r in H₁.
      contradiction.
    }
    apply Nat.nle_gt in H₁.
    apply Hina in H₁.
    rewrite H₁, Hnb, rng_add_0_l in Hnc.
    exfalso; apply Hnc; reflexivity.
  }
  pose proof (Hnc na) as H.
  rewrite Hnb, rng_add_0_r in H.
  contradiction.
}
subst opa; simpl.
destruct nb as [nb| ]. {
  destruct Hnb as (Hinb, Hnb).
  destruct nc as [nc| ]. {
    destruct Hnc as (Hinc, Hnc).
    destruct (eq_nat_dec nb nc) as [| Hbc]; [ subst nb | idtac ]. {
      subst.
      subst n₁ n₂ v₁ v₂ k₁ k₂; simpl.
      unfold cm_factor; simpl.
      rewrite Z2Nat.id. {
        rewrite Z2Nat.id. {
          do 2 rewrite Z.sub_sub_distr.
          do 2 rewrite Z.sub_diag, Z.add_0_l.
          rewrite Pos.mul_comm; reflexivity.
        }
        rewrite <- Z.sub_max_distr_l.
        rewrite Z.sub_diag.
        apply Z.le_max_l.
      }
      rewrite <- Z.sub_max_distr_l.
      rewrite Z.sub_diag.
      apply Z.le_max_r.
    }
    destruct (le_dec nb nc) as [H₁| H₁]. {
      apply Nat_le_neq_lt in H₁; [ idtac | assumption ].
      apply Hinc in H₁.
      rewrite Hna, rng_add_0_l in H₁.
      contradiction.
    }
    apply Nat.nle_gt in H₁.
    apply Hinb in H₁.
    rewrite Hna, rng_add_0_l in Hnc.
    contradiction.
  }
  pose proof (Hnc nb) as H.
  rewrite Hna, rng_add_0_l in H.
  contradiction.
}
subst opb.
exfalso; apply Hab; reflexivity.
Qed.

Theorem ps_lap_nth_x_le_pow_mul : ∀ la m n,
  (n <= m)%nat
  → (ps_lap_nth m ([0; 1 … []] ^ n * la) = ps_lap_nth (m - n) la)%ps.
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

Theorem ps_lap_nth_x_gt_pow_mul : ∀ la m n,
  (m < n)%nat
  → (ps_lap_nth m ([0; 1 … []] ^ n * la) = 0)%ps.
Proof.
intros la m n Hmn.
revert m Hmn.
induction n; intros. {
  exfalso; revert Hmn; apply Nat.nlt_0_r.
}
unfold ps_lap_mul, ps_lap_pow; simpl.
rewrite <- lap_mul_assoc.
rewrite lap_mul_cons_l.
rewrite lap_eq_0, lap_mul_nil_l, lap_add_nil_l, lap_mul_1_l.
destruct m; [ reflexivity | idtac ].
apply Nat.succ_lt_mono in Hmn.
unfold ps_lap_nth; simpl.
apply IHn; assumption.
Qed.

Theorem ps_lap_nth_0_cons_pow : ∀ a la n,
  (ps_lap_nth 0 ([a … la] ^ n) = a ^ n)%ps.
Proof.
intros a la n.
induction n; simpl.
 progress unfold ps_lap_pow; simpl.
 reflexivity.

 unfold ps_lap_pow; simpl.
 unfold ps_lap_nth.
 rewrite list_nth_lap_mul; simpl.
 unfold summation; simpl.
 rewrite IHn.
 rewrite ps_add_0_r; reflexivity.
Qed.

Theorem eq_1_0_all_0 : (1 = 0)%K → ∀ a, (a = 0)%K.
Proof.
intros H a.
rewrite <- rng_mul_1_l.
rewrite H, rng_mul_0_l.
reflexivity.
Qed.

Theorem order_pow : ∀ a n,
  (a ≠ 0)%ps
  → (order (a ^ n) = qfin (Qnat n) * order a)%Qbar.
Proof.
intros a n Ha.
induction n; simpl. {
  remember (order a) as v eqn:Hv .
  symmetry in Hv.
  destruct v as [v| ]. {
    unfold Qnat; simpl.
    rewrite Q.mul_0_l.
    unfold ps_one.
    rewrite ps_monom_order; [ reflexivity | idtac ].
    intros H; apply Ha.
    rewrite <- ps_mul_1_l.
    unfold ps_one.
    rewrite H, ps_zero_monom_eq.
    rewrite ps_mul_0_l.
    reflexivity.
  }
  exfalso; apply Ha.
  apply order_inf; assumption.
}
rewrite order_mul.
rewrite IHn.
remember (order a) as v eqn:Hv .
symmetry in Hv.
destruct v as [v| ]; [ simpl | reflexivity ].
rewrite <- Nat.add_1_l.
unfold Qnat.
rewrite Nat2Z.inj_add, Q.inv_add_distr.
rewrite Q.mul_add_distr_r; simpl.
rewrite Q.mul_1_l; reflexivity.
Qed.

Theorem ps_lap_nth_0_apply_0 : ∀ la,
  (ps_lap_nth 0 la = @apply_lap _ (ps_ring K) la 0)%ps.
Proof.
intros la.
induction la as [| a]; [ reflexivity | simpl ].
rewrite ps_mul_0_r, ps_add_0_l.
reflexivity.
Qed.

Theorem apply_lap_inject_K_in_Kx_monom : ∀ P c,
  (@apply_lap _ (ps_ring K) (lap_inject_K_in_Kx P) (ps_monom c 0) =
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

Theorem ps_monom_0_coeff_0 : ∀ c pow, (ps_monom c pow = 0)%ps → (c = 0)%K.
Proof.
intros c pow Hc.
apply ps_series_order_inf_iff in Hc.
apply series_order_iff in Hc; simpl in Hc.
pose proof (Hc O); assumption.
Qed.

Theorem in_power_list_lt : ∀ A la h (hv : puiseux_series A) pow,
  (h, hv) ∈ power_list pow la
  → (h < pow + length la)%nat.
Proof.
intros A la h hv pow Hh.
unfold pair_rec in Hh; simpl in Hh.
revert pow Hh.
induction la as [| a]; intros; [ contradiction | simpl ].
simpl in Hh.
destruct Hh as [Hh| Hh]. {
  injection Hh; clear Hh; intros; subst h hv.
  apply Nat.lt_sub_lt_add_l.
  rewrite Nat.sub_diag.
  apply Nat.lt_0_succ.
}
rewrite Nat.add_succ_r, <- Nat.add_succ_l.
apply IHla; assumption.
Qed.

Theorem in_points_of_ps_lap_gen_lt : ∀ la pow pt,
  pt ∈ points_of_ps_lap_gen pow la
  → (fst pt < pow + length la)%nat.
Proof.
intros la pow pt Hpt.
unfold points_of_ps_lap_gen in Hpt.
destruct pt as (h, hv); simpl.
eapply in_pts_in_ppl with (def := 0%ps) in Hpt; try reflexivity.
destruct Hpt as (Hpt, Hord).
eapply in_power_list_lt; eassumption.
Qed.

Theorem in_points_of_ps_lap_lt : ∀ la pt,
  pt ∈ points_of_ps_lap la
  → (fst pt < length la)%nat.
Proof.
intros la pt Hpt.
apply in_points_of_ps_lap_gen_lt in Hpt.
assumption.
Qed.

(* [Walker, p. 101] «
      Since O(āh-ah.x^αh) > αh, and O(āl.x^lγ₁) > β₁, we obtain
         f₁(x,y₁) = b₁.y₁^r + b₂.y₁^(r+1) + ... + g(x,y₁) »

   We prove here that
         f₁(x,y₁) = y₁^r.(c₁+y)^j.Ψ(c₁+y) + g(x,y₁) »
*)
Theorem f₁_eq_term_with_Ψ_plus_g : ∀ f L j αj c₁ r f₁ Ψ,
  newton_segments f = Some L
  → ini_pt L = (j, αj)
    → c₁ = ac_root (Φq f L)
      → r = root_multiplicity acf c₁ (Φq f L)
        → Ψ = quotient_phi_x_sub_c_pow_r (Φq f L) c₁ r
          → f₁ = next_pol f (β L) (γ L) c₁
            → (f₁ =
               POL [0%ps; 1%ps … []] ^ r *
               POL [ps_monom c₁ 0; 1%ps … []] ^ j *
               POL (lap_inject_K_in_Kx (al Ψ)) ∘
               POL [ps_monom c₁ 0; 1%ps … []] +
               g_of_ns f L)%pspol.
Proof.
intros f L j αj c₁ r f₁ Ψ HL Hini Hc₁ Hr HΨ Hf₁.
subst f₁.
remember (g_lap_of_ns f L) as gg.
remember Heqgg as H; clear HeqH.
unfold g_lap_of_ns in H; subst gg.
rewrite <- Hc₁ in H.
remember [ini_pt L … oth_pts L ++ [fin_pt L]] as pl eqn:Hpl .
remember (List.map (term_of_point f) pl) as tl eqn:Htl .
remember (List.map (λ t : term α nat, power t) tl) as l₁ eqn:Hl₁ .
remember (list_seq_except 0 (length (al f)) l₁) as l₂ eqn:Hl₂ .
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
  apply Sorted_fst_lt_nat_num_fst. {
    eapply ini_oth_fin_pts_sorted; eassumption.
  }
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

Theorem nth_g_order_pos : ∀ f L h,
  newton_segments f = Some L
  → (order (ps_lap_nth h (g_lap_of_ns f L)) > 0)%Qbar.
Proof.
intros f L h HL.
destruct (lt_dec h (length (g_lap_of_ns f L))) as [Hlt| Hge]. {
  eapply each_power_of_y₁_in_g_has_coeff_pos_ord; try eassumption. {
    reflexivity.
  }
  unfold g_of_ns; simpl.
  unfold ps_lap_nth.
  apply List.nth_In; assumption.
}
apply Nat.nlt_ge in Hge.
unfold ps_lap_nth.
rewrite List.nth_overflow; [ idtac | assumption ].
rewrite order_0; constructor.
Qed.

Theorem order_nth_inject_K : ∀ la i,
  (0 ≤ order (ps_lap_nth i (lap_inject_K_in_Kx la)))%Qbar.
Proof.
intros la i.
revert i.
induction la as [| a]; intros; simpl.
 unfold ps_lap_nth.
 rewrite list_nth_nil.
 rewrite order_0; constructor.

 destruct i; [ idtac | apply IHla ].
 unfold ps_lap_nth; simpl.
 apply ps_monom_order_ge.
Qed.

Theorem monom_y_plus_c_is_inject_K : ∀ c,
  ([ps_monom c 0; 1%ps … []] = lap_inject_K_in_Kx [c; 1%K … []])%pslap.
Proof.
intros c.
unfold ps_lap_eq.
reflexivity.
Qed.

Theorem fold_lap_inject_K_in_Kx : ∀ la,
  List.map (λ c : α, ps_monom c 0) la = lap_inject_K_in_Kx la.
Proof. reflexivity. Qed.

Theorem lap_add_cons : ∀ α (R : ring α) a b la lb,
  ([a … la] + [b … lb] = [(a + b)%K … la + lb])%lap.
Proof. reflexivity. Qed.

Theorem lap_inject_add : ∀ la lb,
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
  constructor; [ simpl | apply IHla ].
  rewrite ps_monom_add; reflexivity.
Qed.

Theorem lap_inject_mul : ∀ la lb,
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
  constructor; [ simpl; apply ps_monom_mul | idtac ].
  symmetry.
  eapply ps_lap_eq_trans; [ apply lap_add_map_ps | ].
  unfold ps_lap_mul in IHla.
  unfold ps_lap_eq in IHla.
  rewrite IHla.
  progress unfold ps_lap_add.
  simpl.
  rewrite ps_zero_monom_eq.
  apply lap_add_compat; [ idtac | reflexivity ].
  eapply ps_lap_eq_trans; [ apply lap_add_map_ps | ].
  apply lap_add_compat.
   eapply ps_lap_eq_trans; [ apply lap_mul_map_ps | reflexivity ].
   eapply ps_lap_eq_trans; [ apply lap_mul_map_ps | reflexivity ].
Qed.

Theorem lap_inject_comp : ∀ la lb,
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
do 3 rewrite fold_lap_inject_K_in_Kx.
rewrite fold_ps_lap_mul.
rewrite lap_inject_mul.
rewrite <- lap_inject_add.
reflexivity.
Qed.

(* [Walker, p 101] « O(bi) ≥ 0,  i = 0,...,n » *)
Theorem order_bbar_nonneg : ∀ f L c₁ r f₁,
  newton_segments f = Some L
  → c₁ = ac_root (Φq f L)
    → r = root_multiplicity acf c₁ (Φq f L)
      → f₁ = next_pol f (β L) (γ L) c₁
        → ∀ i, (order (ps_poly_nth i f₁) ≥ 0)%Qbar.
Proof.
intros f L c₁ r f₁ HL Hc₁ Hr Hf₁ i.
remember (quotient_phi_x_sub_c_pow_r (Φq f L) c₁ r) as Ψ eqn:HΨ .
remember (ini_pt L) as j eqn:Hini.
destruct j as (j, αj).
symmetry in Hini.
rewrite f₁_eq_term_with_Ψ_plus_g; try eassumption.
unfold ps_poly_nth; simpl.
rewrite fold_ps_lap_add.
rewrite ps_lap_nth_add.
rewrite fold_ps_lap_comp.
eapply Qbar.le_trans; [ idtac | apply order_add ].
apply Qbar.min_glb. {
  rewrite <- lap_mul_assoc.
  rewrite fold_ps_lap_mul, fold_ps_lap_pow.
  destruct (le_dec r i) as [Hle| Hgt]. {
    rewrite ps_lap_nth_x_le_pow_mul; [ idtac | assumption ].
    progress unfold ps_lap_comp.
    rewrite monom_y_plus_c_is_inject_K.
    rewrite fold_ps_lap_pow.
    rewrite lap_power_map_ps.
    rewrite fold_ps_lap_comp.
    rewrite lap_inject_comp.
    rewrite fold_ps_lap_mul.
    rewrite lap_inject_mul.
    apply order_nth_inject_K.
  }
  apply Nat.nle_gt in Hgt.
  rewrite ps_lap_nth_x_gt_pow_mul; [ idtac | assumption ].
  rewrite order_0; constructor.
}
apply Qbar.lt_le_incl.
apply nth_g_order_pos; assumption.
Qed.

(* [Walker, p 101] « O(bi) > 0,  i = 0,...,r-1 » *)
Theorem order_bbar_pos : ∀ f L c₁ r f₁,
  newton_segments f = Some L
  → c₁ = ac_root (Φq f L)
    → r = root_multiplicity acf c₁ (Φq f L)
      → f₁ = next_pol f (β L) (γ L) c₁
        → ∀ i, (i < r)%nat
          → (order (ps_poly_nth i f₁) > 0)%Qbar.
Proof.
intros f L c₁ r f₁ HL Hc₁ Hr Hf₁ i Hir.
remember (quotient_phi_x_sub_c_pow_r (Φq f L) c₁ r) as Ψ eqn:HΨ .
remember (ini_pt L) as j eqn:Hini.
destruct j as (j, αj).
symmetry in Hini.
rewrite f₁_eq_term_with_Ψ_plus_g; try eassumption.
unfold ps_poly_nth; simpl.
rewrite fold_ps_lap_add.
rewrite ps_lap_nth_add.
rewrite fold_ps_lap_comp.
eapply Qbar.lt_le_trans; [ idtac | apply order_add ].
apply Qbar.min_glb_lt. {
  rewrite <- lap_mul_assoc.
  rewrite fold_ps_lap_mul.
  rewrite fold_ps_lap_pow.
  rewrite ps_lap_nth_x_gt_pow_mul; [ idtac | assumption ].
  rewrite order_0; constructor.
}
apply nth_g_order_pos; assumption.
Qed.

Theorem char_pol_root_ne_0 : ∀ f L m c₁,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → c₁ = ac_root (Φq f L)
  → (c₁ ≠ 0)%K.
Proof.
intros f L m c₁ HL Hm Hc₁.
remember HL as Happ; clear HeqHapp.
eapply cpol_degree_ge_1 with (K := K) in Happ; eauto .
apply ac_prop_root in Happ.
rewrite <- Hc₁ in Happ.
remember (ini_pt L) as j eqn:Hini.
destruct j as (j, αj).
symmetry in Hini.
intros Hc; rewrite Hc in Happ.
unfold apply_poly in Happ; simpl in Happ.
rewrite Nat.sub_diag, list_pad_0 in Happ.
simpl in Happ.
rewrite rng_mul_0_r, rng_add_0_l in Happ.
revert Happ.
eapply ord_coeff_non_zero_in_newt_segm; eauto .
now rewrite Hini; left; simpl.
Qed.

(* [Walker, p 101] « O(br) = 0 » *)
Theorem order_bbar_r_is_0 : ∀ f L m c₁ r f₁,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → c₁ = ac_root (Φq f L)
  → r = root_multiplicity acf c₁ (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c₁
  → (order (ps_poly_nth r f₁) = 0)%Qbar.
Proof.
intros f L m c₁ r f₁ HL Hm Hc₁ Hr Hf₁.
remember (quotient_phi_x_sub_c_pow_r (Φq f L) c₁ r) as Ψ eqn:HΨ .
remember (ini_pt L) as j eqn:Hini.
destruct j as (j, αj).
symmetry in Hini.
rewrite f₁_eq_term_with_Ψ_plus_g; try eassumption.
unfold ps_poly_nth; simpl.
remember ([0%ps; 1%ps … []] ^ r)%pslap as yr.
remember ([ps_monom c₁ 0; 1%ps … []] ^ j)%pslap as ycj.
remember (lap_inject_K_in_Kx (al Ψ)) as psi.
remember [ps_monom c₁ 0; 1%ps … []] as yc.
assert (order (ps_lap_nth r (yr * ycj * psi ∘ yc)) = 0)%Qbar as Hor.
 subst yr ycj psi yc.
 progress unfold ps_lap_mul.
 rewrite <- lap_mul_assoc.
 do 2 rewrite fold_ps_lap_mul.
 erewrite ps_lap_nth_x_le_pow_mul; [ idtac | reflexivity ].
 rewrite Nat.sub_diag.
 progress unfold ps_lap_mul.
 progress unfold lap_mul.
 progress unfold ps_lap_nth; simpl.
 rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
 unfold summation; simpl.
 rewrite ps_add_0_r.
 rewrite order_mul.
 rewrite fold_ps_lap_nth.
 rewrite ps_lap_nth_0_cons_pow.
 rewrite order_pow.
  rewrite ps_monom_order.
   rewrite Qbar.mul_0_r; [ idtac | intros HH; discriminate HH ].
   rewrite Qbar.add_0_l.
   rewrite fold_ps_lap_nth.
   rewrite ps_lap_nth_0_apply_0.
   unfold ps_lap_comp.
   rewrite apply_lap_compose.
   unfold apply_lap at 2; simpl.
   rewrite ps_mul_0_l, ps_add_0_l.
   rewrite ps_mul_0_r, ps_add_0_l.
   rewrite apply_lap_inject_K_in_Kx_monom.
   rewrite ps_monom_order; [ reflexivity | idtac ].
   eapply psi_c₁_ne_0 in HΨ; eassumption.

   eapply char_pol_root_ne_0; eassumption.

  intros HH.
  apply ps_monom_0_coeff_0 in HH.
  revert HH.
  eapply char_pol_root_ne_0; eassumption.

 subst yr ycj psi yc.
 rewrite fold_ps_lap_add.
 rewrite ps_lap_nth_add.
 rewrite fold_ps_lap_comp.
 rewrite order_add_eq_min; rewrite Hor.
 rewrite Qbar.min_l; [ reflexivity | idtac ].
  apply Qbar.lt_le_incl.
  apply nth_g_order_pos; assumption.

  apply Qbar.lt_neq.
  apply nth_g_order_pos; assumption.
Qed.

Theorem exists_pol_ord : ∀ f, ∃ m,
  m = ps_pol_com_polydo f ∧ pol_in_K_1_m f m.
Proof.
intros f.
unfold pol_in_K_1_m.
remember (ps_pol_com_polydo f) as m eqn:Hm.
exists m; split; [ reflexivity | ].
apply ps_lap_forall_forall.
 intros a b Hab H.
 rewrite <- Hab; assumption.

 intros a Ha.
 unfold ps_pol_com_polydo in Hm.
 remember (al f) as la; clear Heqla.
 revert a m Ha Hm.
 induction la as [| b]; intros; [ contradiction | idtac ].
 simpl in Ha.
 destruct Ha as [(Hbla, Hba)| Ha].
  constructor.
  simpl in Hm.
  remember (ps_lap_com_polydo la) as m' eqn:Hm' .
  exists (adjust_ps 0 m' b).
  split; [ idtac | simpl; rewrite Pos.mul_comm; symmetry; assumption ].
  transitivity b; [ idtac | assumption ].
  symmetry; apply ps_adjust_eq.

  subst m; simpl.
  apply in_K_1_m_lap_mul_r_compat.
  apply IHla; [ apply Ha | reflexivity ].
Qed.

(* [Walker, p 101] «
     O(bi) ≥ 0,  i = 0,...,n
     O(bi) > 0,  i = 0,...,r-1
     O(br) = 0
   »
*)
Theorem f₁_orders : ∀ f L c₁ r f₁,
  newton_segments f = Some L
  → c₁ = ac_root (Φq f L)
  → r = root_multiplicity acf c₁ (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c₁
  → (∀ i, (order (ps_poly_nth i f₁) ≥ 0)%Qbar)
    ∧ (∀ i, (i < r)%nat → (order (ps_poly_nth i f₁) > 0)%Qbar)
    ∧ (order (ps_poly_nth r f₁) = 0)%Qbar.
Proof.
intros f L c₁ r f₁ HL Hc₁ Hr Hf₁.
split; [ eapply order_bbar_nonneg; eassumption | idtac ].
split; [ eapply order_bbar_pos; eassumption | idtac ].
pose proof (exists_pol_ord f) as H.
destruct H as (m, (Hm, Hp)).
eapply order_bbar_r_is_0; eassumption.
Qed.

End theorems.
