(* CharactPolyn.v *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Sorted Arith Field.

Require Import A_PosArith A_ZArith A_QArith.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Misc.
Require Import NbarM.
Require Import QbarM.
Require Import Newton.
Require Import PolyConvexHull.
Require Import Field2.
Require Import Fpolynomial.
Require Import PSpolynomial.
Require Import Puiseux_base.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_div.
Require Import Slope_base.

Set Implicit Arguments.

Record term α β := { coeff : α; power : β }.

(* *)

Fixpoint make_char_pol α (R : ring α) pow tl :=
  match tl with
  | [] => []
  | [t₁ … tl₁] =>
      list_pad (power t₁ - pow) 0%K
        [coeff t₁ … make_char_pol R (S (power t₁)) tl₁]
    end.

Definition lap_term_of_point α {R : ring α} {K : field R} la (pt : (nat * Q)) :=
  let h := fst pt in
  let ps := List.nth h la 0%ps in
  let c := order_coeff ps in
  {| coeff := c; power := h |}.

Definition term_of_point α {R : ring α} {K : field R} f (pt : (nat * Q)) :=
  lap_term_of_point (al f) pt.

Definition Φq α {R : ring α} {K : field R} f L :=
  let pl := [ini_pt L … oth_pts L ++ [fin_pt L]] in
  let tl := List.map (term_of_point f) pl in
  let j := fst (ini_pt L) in
  {| al := make_char_pol R j tl |}.

Definition ps_lap_com_polydo α (psl : list (puiseux_series α)) :=
  List.fold_right (λ ps a, (a * ps_polydo ps)%pos) 1%pos psl.

Definition ps_pol_com_polydo {α} f := @ps_lap_com_polydo α (al f).
Arguments ps_pol_com_polydo _ f%_pol.

(* *)

Fixpoint list_shrink_aux α cnt k₁ (l : list α) :=
  match l with
  | [] => []
  | [x₁ … l₁] =>
      match cnt with
      | O => [x₁ … list_shrink_aux k₁ k₁ l₁]
      | S n => list_shrink_aux n k₁ l₁
      end
  end.

Definition list_shrink α k (l : list α) := list_shrink_aux 0 (k - 1) l.

Definition poly_shrink α k (p : polynomial α) :=
  POL (list_shrink k (al p))%pol.

Definition p_of_m m a :=
  let p := (q_num a * z_pos m)%Z in
  let q := q_den a in
  (p / Z.gcd p (z_pos q))%Z.

Definition q_of_m m a :=
  let p := (q_num a * z_pos m)%Z in
  let q := q_den a in
  Z.to_pos (z_pos q / Z.gcd p (z_pos q)).

Definition mh_of_m α m αh (hps : puiseux_series α) :=
  (q_num αh * z_pos m / z_pos (ps_polydo hps))%Z.

(* express that some puiseux series ∈ K(1/m)* *)
Inductive in_K_1_m {α} {R : ring α} {K : field R} ps m :=
  InK1m : (∃ ps₁, (ps₁ = ps)%ps ∧ ps_polydo ps₁ = m) → in_K_1_m ps m.

Arguments in_K_1_m _ _ _ ps%_ps m%_pos.

Definition pol_in_K_1_m {α} {R : ring α} {K : field R} f m :=
  ps_lap_forall (λ a, in_K_1_m a m) (al f).

Definition poly_shrinkable α (R : ring α) {K : field R} q f :=
  ∀ n, n mod q ≠ O → List.nth n (al f) 0%K = 0%K.

(* usable only if poly_shrinkable q (Φq f L) *)
Definition Φs α {R : ring α} {K : field R} q f L :=
  poly_shrink q (Φq f L).

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Theorem al_Φq : ∀ f L,
  al (Φq f L)
  = make_char_pol R (fst (ini_pt L))
      (List.map (term_of_point f) [ini_pt L … oth_pts L ++ [fin_pt L]]).
Proof.
intros f L; reflexivity.
Qed.

Theorem Φq_f : ∀ f L,
  Φq f L
  = POL
      (make_char_pol R (fst (ini_pt L))
         (List.map (term_of_point f)
            [ini_pt L … oth_pts L ++ [fin_pt L]]))%pol.
Proof.
intros f L.
progress unfold Φq; simpl.
reflexivity.
Qed.

Theorem in_seg_in_pts : ∀ pt pt₁ pt₂ pts,
  pt ∈ oth_pts (minimise_slope pt₁ pt₂ pts)
  → pt ∈ [pt₂ … pts].
Proof.
intros pt pt₁ pt₂ pts Hpt.
revert pt₂ Hpt.
induction pts as [| pt₃]; intros; [ contradiction | idtac ].
simpl in Hpt.
remember (minimise_slope pt₁ pt₃ pts) as ms₃.
remember (slope_expr pt₁ pt₂ ?= slope ms₃) as c.
destruct c; simpl in Hpt. {
  destruct Hpt as [Hpt| Hpt]. {
    subst pt; left; reflexivity.
  }
  right; subst ms₃; apply IHpts; assumption.
} {
  contradiction.
} {
  right; subst ms₃; apply IHpts; assumption.
}
Qed.

Theorem hull_seg_edge_in_init_pts : ∀ pts hs pt,
  lower_convex_hull_points pts = Some hs
  → pt ∈ oth_pts hs
  → pt ∈ pts.
Proof.
intros pts hs pt Hnp Hpt.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros Hnp.
subst hs; simpl in Hpt.
right; eapply in_seg_in_pts; eassumption.
Qed.

Theorem hull_seg_vert_in_init_pts : ∀ pts hs,
  lower_convex_hull_points pts = Some hs
  → ini_pt hs ∈ pts ∧ fin_pt hs ∈ pts.
Proof.
intros pts hs Hnp.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros Hnp; subst hs.
rewrite minimised_slope_beg_pt.
split; [ left; reflexivity | idtac ].
remember List.In as f; simpl; subst f.
right; eapply end_pt_in; reflexivity.
Qed.

Theorem oth_pts_in_init_pts : ∀ pts L pt,
  lower_convex_hull_points pts = Some L
  → pt ∈ oth_pts L
    → pt ∈ pts.
Proof.
intros pts L pt HL Hpt.
eapply hull_seg_edge_in_init_pts; try eassumption; reflexivity.
Qed.

Theorem ini_fin_ns_in_init_pts : ∀ pts L,
  lower_convex_hull_points pts = Some L
  → ini_pt L ∈ pts ∧ fin_pt L ∈ pts.
Proof.
intros pts L HL.
eapply hull_seg_vert_in_init_pts; try eassumption; reflexivity.
Qed.

Theorem ns_in_init_pts : ∀ pts L pt,
  lower_convex_hull_points pts = Some L
  → pt ∈ [ini_pt L … oth_pts L ++ [fin_pt L]]
    → pt ∈ pts.
Proof.
intros pts L pt HL Hpt.
destruct Hpt as [Hpt| Hpt]. {
 subst pt.
 apply ini_fin_ns_in_init_pts; assumption.
}
apply List.in_app_or in Hpt.
destruct Hpt as [Hpt| Hpt]. {
  eapply oth_pts_in_init_pts; eassumption.
}
destruct Hpt as [Hpt| ]; [ idtac | contradiction ].
subst pt.
apply ini_fin_ns_in_init_pts; assumption.
Qed.

Theorem pt₁_bef_seg : ∀ pt₁ pt₂ pts pth,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → pth ∈ oth_pts (minimise_slope pt₁ pt₂ pts)
  → (fst pt₁ < fst pth)%nat.
Proof.
intros pt₁ pt₂ pts pth Hsort Hh.
revert pt₁ pt₂ pth Hsort Hh.
induction pts as [| pt₃]; intros; [ contradiction | idtac ].
simpl in Hh.
remember (minimise_slope pt₁ pt₃ pts) as ms₃.
remember (slope_expr pt₁ pt₂ ?= slope ms₃) as c.
symmetry in Heqc.
destruct c. {
  simpl in Hh.
  destruct Hh as [Hh| Hh]. {
    subst pth.
    eapply Sorted_hd; [ eassumption | left; reflexivity ].
  }
  subst ms₃.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
} {
  contradiction.
} {
  subst ms₃.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
}
Qed.

Theorem vert_bef_edge : ∀ pts hs j αj h αh,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some hs
  → (j, αj) = ini_pt hs
  → (h, αh) ∈ oth_pts hs
  → (j < h)%nat.
Proof.
intros pts hs j αj h αh Hsort Hnp Hj Hh.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros Hhsl; subst hs.
simpl in Hj, Hh.
rewrite minimised_slope_beg_pt in Hj.
apply pt₁_bef_seg in Hh; [ subst pt₁; assumption | assumption ].
Qed.

Theorem jq_lt_hq : ∀ (f : puis_ser_pol α) j αj h αh L,
  newton_segments f = Some L
  → (j, αj) = ini_pt L
  → (h, αh) ∈ oth_pts L
  → (j < h)%nat.
Proof.
intros f j αj h αh L HL Hjαj Hhαh.
progress unfold newton_segments in HL.
remember (points_of_ps_polynom f) as pts.
apply points_of_polyn_sorted in Heqpts.
eapply vert_bef_edge; eassumption.
Qed.

Theorem j_lt_h : ∀ (f : puis_ser_pol α) j αj h αh L,
  newton_segments f = Some L
  → (j, αj) = ini_pt L
  → (h, αh) ∈ oth_pts L
  → (j < h)%nat.
Proof.
intros * HL Hj Hh.
eapply jq_lt_hq in Hh; eassumption.
Qed.

Theorem seg_bef_end_pt : ∀ pt₁ pt₂ pts ms₁ hq αh kq αk,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
  → (hq, αh) ∈ oth_pts ms₁
  → (kq, αk) = fin_pt ms₁
  → (hq < kq)%nat.
Proof.
fix IHpts 3.
intros pt₁ pt₂ pts ms₁ hq αh kq αk Hsort Hms₁ Hseg Hend.
destruct pts as [| pt₃]; [ subst ms₁; contradiction | idtac ].
simpl in Hms₁.
remember (minimise_slope pt₁ pt₃ pts) as ms₂.
symmetry in Heqms₂.
remember (slope_expr pt₁ pt₂ ?= slope ms₂) as c.
symmetry in Heqc.
destruct c. {
  subst ms₁; simpl in Hseg, Hend.
  destruct Hseg as [Hseg| Hseg]. {
    apply Sorted_inv_1 in Hsort.
    apply Sorted_hd with (pt₂ := (kq, αk)) in Hsort. {
      subst pt₂; assumption.
    }
    rewrite Hend.
    eapply end_pt_in; eassumption.
  }
  eapply IHpts with (pts := pts); try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
} {
  subst ms₁; simpl in Hseg, Hend; contradiction.
} {
  subst ms₁; simpl in Hseg, Hend.
  eapply IHpts with (pts := pts); try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
}
Qed.

Theorem hq_lt_kq : ∀ (f : puis_ser_pol α) hq αh kq αk L,
  newton_segments f = Some L
  → (hq, αh) ∈ oth_pts L
  → (kq, αk) = fin_pt L
  → (hq < kq)%nat.
Proof.
intros f hq αh kq αk L HL Hoth Hfin.
progress unfold newton_segments in HL.
remember (points_of_ps_polynom f) as pts.
apply points_of_polyn_sorted in Heqpts.
progress unfold lower_convex_hull_points in HL.
destruct pts as [| pt₁]; [ discriminate HL | idtac ].
destruct pts as [| pt₂]; [ discriminate HL | idtac ].
injection HL; clear HL; intros HL; subst L.
simpl in Hoth, Hfin.
eapply seg_bef_end_pt; try eassumption; reflexivity.
Qed.

Theorem j_lt_k : ∀ (f : puis_ser_pol α) j k L,
  newton_segments f = Some L
  → j = fst (ini_pt L)
  → k = fst (fin_pt L)
  → (j < k)%nat.
Proof.
intros f j k L HL Hj Hk.
progress unfold newton_segments in HL.
remember (points_of_ps_polynom f) as pts.
remember Heqpts as Hj₁; clear HeqHj₁; symmetry in Hj₁.
remember Heqpts as Hk₁; clear HeqHk₁; symmetry in Hk₁.
apply points_of_polyn_sorted in Heqpts.
assert (fst (ini_pt L) < fst (fin_pt L))%nat. {
  eapply ini_lt_fin_pt; eassumption.
}
congruence.
Qed.

Theorem jz_lt_kz : ∀ (f : puis_ser_pol α) jz kz L,
  newton_segments f = Some L
  → jz = fst (ini_pt L)
  → kz = fst (fin_pt L)
  → (jz < kz)%nat.
Proof.
intros f jz kz L HL Hjz Hkz.
remember HL as H; clear HeqH.
eapply j_lt_k in H; try reflexivity.
remember (ini_pt L) as jaj.
destruct jaj as (j, aj).
remember (fin_pt L) as kak.
destruct kak as (k, ak).
simpl in Hjz, Hkz, H.
now subst jz kz.
Qed.

(* *)

(* [Walker, p. 100]: « If Pj and Pk are the left and right hand ends
   of the segment L, v + γ₁ u = β₁ of the Newton polygon, then
           αj + j γ₁ = αk + k γ₁
    or
               αj - αk
          γ₁ = ------- = [...]
                k - j
  » *)
Theorem gamma_value_jk : ∀ L j k αj αk,
  (j, αj) = ini_pt L
  → (k, αk) = fin_pt L
  → γ L = (αj - αk) / (Qnat k - Qnat j).
Proof.
intros L j k αj αk Hjαj Hkαk.
progress unfold γ; simpl.
rewrite <- Hjαj, <- Hkαk; reflexivity.
Qed.

Theorem first_power_le : ∀ pow cl h hv,
  (h, hv) ∈ filter_finite_ord (power_list pow cl)
  → (pow <= h)%nat.
Proof.
intros pow cl h hv Hhhv.
progress unfold power_list in Hhhv.
revert pow Hhhv.
induction cl as [| c]; intros; [ contradiction | idtac ].
simpl in Hhhv.
destruct cl as [| c₁]. {
  simpl in Hhhv.
  destruct (order c); [ idtac | contradiction ].
  destruct Hhhv as [Hhhv| ]; [ idtac | contradiction ].
  injection Hhhv; clear Hhhv; intros; subst h hv.
  easy.
}
simpl in Hhhv.
simpl in IHcl.
destruct (order c). {
  destruct Hhhv as [Hhhv| Hhhv]. {
    now injection Hhhv; clear Hhhv; intros; subst h hv.
  }
  apply IHcl in Hhhv.
  transitivity (S pow); [ apply Nat.le_succ_r | assumption ].
  left; reflexivity.
} {
  apply IHcl in Hhhv.
  transitivity (S pow); [ apply Nat.le_succ_r | assumption ].
  left; reflexivity.
}
Qed.

Theorem in_pts_in_ppl : ∀ pow cl ppl pts h hv hps def,
  ppl = power_list pow cl
  → pts = filter_finite_ord ppl
  → (h, hv) ∈ pts
  → hps = List.nth (h - pow) cl def
  → (h, hps) ∈ ppl ∧ order hps = qfin hv.
Proof.
intros pow cl ppl pts h hv hps def Hppl Hpts Hhhv Hhps.
subst ppl pts.
destruct cl as [| c₁]; intros; [ contradiction | idtac ].
revert pow c₁ h hv hps Hhps Hhhv.
induction cl as [| c]; intros. {
  simpl in Hhhv.
  remember (order c₁) as v.
  symmetry in Heqv.
  destruct v as [v| ]; [ idtac | contradiction ].
  destruct Hhhv as [Hhhv| ]; [ idtac | contradiction ].
  injection Hhhv; clear Hhhv; intros; subst v h.
  remember (q_num (Qnat pow)) as x; simpl in Heqx; subst x.
  rewrite Nat.sub_diag in Hhps.
  simpl in Hhps; subst hps.
  split; [ left; reflexivity | assumption ].
} {
  remember [c … cl] as ccl; simpl in Hhhv; subst ccl.
  remember (order c₁) as v.
  symmetry in Heqv.
  destruct v as [v| ]. {
    destruct Hhhv as [Hhhv| Hhhv]. {
      injection Hhhv; clear Hhhv; intros; subst v h.
      remember (q_num (Qnat pow)) as x; simpl in Heqx; subst x.
      rewrite Nat.sub_diag in Hhps.
      simpl in Hhps; subst hps.
      split; [ left; reflexivity | assumption ].
    }
    destruct (le_dec (S pow) h) as [Hle| Hgt]. {
      eapply IHcl in Hhhv. {
        rewrite <- Nat.sub_succ in Hhps.
        rewrite Nat.sub_succ_l in Hhps; [ | easy ].
        simpl in Hhps.
        destruct Hhhv as (Hhhv, Hhv).
        split; [ right; eassumption | assumption ].
      }
      rewrite <- Nat.sub_succ in Hhps.
      rewrite Nat.sub_succ_l in Hhps; [ idtac | assumption ].
      simpl in Hhps; eassumption.
    }
    apply first_power_le in Hhhv; contradiction.
  }
  destruct (le_dec (S pow) h) as [Hle| Hgt]. {
    eapply IHcl in Hhhv. {
      rewrite <- Nat.sub_succ in Hhps.
      rewrite Nat.sub_succ_l in Hhps; [ idtac | assumption ].
      simpl in Hhps.
      destruct Hhhv as (Hhhv, Hhv).
      split; [ right; eassumption | assumption ].
    }
    rewrite <- Nat.sub_succ in Hhps.
    rewrite Nat.sub_succ_l in Hhps; [ idtac | assumption ].
    simpl in Hhps; eassumption.
  }
  apply first_power_le in Hhhv; contradiction.
}
Qed.

Theorem in_pts_in_psl : ∀ pow pts psl h hv hps def,
  pts = filter_finite_ord (power_list pow psl)
  → (h, hv) ∈ pts
  → hps = List.nth (h - pow) psl def
  → hps ∈ psl ∧ order hps = qfin hv.
Proof.
intros pow pts psl h hv hps def Hpts Hhv Hhps.
remember (power_list pow psl) as ppl.
assert (H : (pow <= h)%nat). {
  subst pts ppl.
  eapply first_power_le; eassumption.
}
eapply in_pts_in_ppl in Hhv; try eassumption.
destruct Hhv as (Hhps₁, Hv).
split; [ idtac | assumption ].
subst ppl.
destruct psl as [| ps₁]; [ contradiction | idtac ].
revert pow pts ps₁ h hv hps Hhps Hv Hhps₁ Hpts H.
induction psl as [| ps]; intros. {
  destruct Hhps₁ as [Hhps₁| ]; [ idtac | contradiction ].
  injection Hhps₁; clear Hhps₁; intros; subst h hps.
  now left.
}
destruct Hhps₁ as [Hhps₁| Hhps₁]. {
  injection Hhps₁; clear Hhps₁; intros; subst h hps.
  now left.
}
destruct (eq_nat_dec h pow) as [Heq| Hne]. {
  rewrite Heq, Nat.sub_diag in Hhps.
  subst hps; left; reflexivity.
}
right.
eapply IHpsl; try eassumption; try reflexivity. {
  rewrite <- Nat.sub_succ in Hhps.
  rewrite Nat.sub_succ_l in Hhps; [ assumption | idtac ].
  apply not_eq_sym in Hne.
  apply Nat_le_neq_lt; assumption.
}
apply not_eq_sym in Hne.
apply Nat_le_neq_lt; assumption.
Qed.

Theorem in_pts_in_pol : ∀ f pts h hv hps def,
  pts = points_of_ps_polynom f
  → (h, hv) ∈ pts
  → hps = List.nth h (al f) def
  → hps ∈ al f ∧ order hps = qfin hv.
Proof.
intros f pts h hv hps def Hpts Hhhv Hhps.
eapply in_pts_in_psl; try eassumption.
simpl; rewrite Nat.sub_0_r; eassumption.
Qed.

Theorem in_ppl_in_pts : ∀ pow cl ppl pts h hv hps,
  ppl = power_list pow cl
  → pts = filter_finite_ord ppl
  → (pow <= h)%nat
  → hps = List.nth (h - pow) cl 0%ps
  → order hps = qfin hv
  → (h, hv) ∈ pts.
Proof.
(* peut-être améliorable, simplifiable ; voir pourquoi cas cl=[] est à part ;
   et voir les deux cas de h - pow plus bas *)
intros pow cl ppl pts h hv hps Hppl Hpts Hph Hhhv Hhps.
subst ppl pts.
destruct cl as [| c₁]; intros; simpl. {
  rewrite list_nth_nil in Hhhv.
  assert (order hps = qinf) as H. {
    apply order_inf.
    subst hps; reflexivity.
  }
  rewrite Hhps in H; discriminate H.
}
revert pow c₁ h hv hps Hhps Hhhv Hph.
induction cl as [| c]; intros. {
  simpl in Hhhv.
  remember (h - pow)%nat as hp eqn:Hhp .
  symmetry in Hhp.
  destruct hp. {
    subst c₁; simpl.
    rewrite Hhps.
    apply Nat.sub_0_le in Hhp.
    apply Nat.le_antisymm in Hhp; [ idtac | assumption ].
    subst pow; left; reflexivity.
  }
  rewrite match_id in Hhhv.
  assert (order hps = qinf) as H. {
    apply order_inf.
    subst hps; reflexivity.
  }
  rewrite Hhps in H; discriminate H.
}
remember [c … cl] as x; simpl; subst x.
remember [c … cl] as x; simpl; subst x.
remember (order c₁) as n eqn:Hn.
symmetry in Hn.
destruct n as [n| ]. {
  simpl in Hhhv.
  remember (h - pow)%nat as hp eqn:Hhp .
  symmetry in Hhp.
  destruct hp. {
    subst c₁.
    apply Nat.sub_0_le in Hhp.
    apply Nat.le_antisymm in Hph; [ idtac | assumption ].
    subst pow.
    rewrite Hhps in Hn; injection Hn; intros; subst n.
    left; reflexivity.
  }
  right.
  destruct hp. {
    subst hps.
    apply Nat.add_sub_eq_nz in Hhp; [ idtac | intros H; discriminate H ].
    rewrite Nat.add_1_r in Hhp.
    eapply IHcl; try eassumption. {
      rewrite Hhp, Nat.sub_diag; reflexivity.
    }
    rewrite Hhp; reflexivity.
  }
  apply Nat.add_sub_eq_nz in Hhp; [ idtac | intros H; discriminate H ].
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hhp.
  eapply IHcl; try eassumption. {
    erewrite <- Hhp.
    rewrite Nat.add_comm, Nat.add_sub; assumption.
  }
  rewrite <- Hhp.
  apply Nat.le_add_r.
}
destruct (eq_nat_dec h pow) as [Hhp| Hhp]. {
  subst pow.
  rewrite Nat.sub_diag in Hhhv.
  simpl in Hhhv.
  subst c₁.
  rewrite Hhps in Hn; discriminate Hn.
}
eapply IHcl; try eassumption. {
  destruct h. {
    simpl in Hhhv; simpl.
    subst hps.
    rewrite Hhps in Hn; discriminate Hn.
  }
  rewrite Nat.sub_succ_l in Hhhv.
  rewrite Nat.sub_succ; assumption.
  apply Nat.neq_sym in Hhp.
  apply Nat_le_neq_lt in Hhp; [ idtac | assumption ].
  apply le_S_n; assumption.
}
apply Nat.neq_sym in Hhp.
apply Nat_le_neq_lt in Hhp; [ idtac | assumption ].
assumption.
Qed.

Theorem in_pol_in_pts : ∀ f pts h hv hps,
  pts = points_of_ps_polynom f
  → hps = List.nth h (al f) 0%ps
  → order hps = qfin hv
  → (h, hv) ∈ pts.
Proof.
intros f pts h hv hps Hpts Hhps Hv.
eapply in_ppl_in_pts; try eassumption; try reflexivity. {
  apply Nat.le_0_l.
}
rewrite Nat.sub_0_r; assumption.
Qed.

(* [Walker, p. 100]: «
                        p
          γ₁ = [...] = ---
                       m q
  » *)
Theorem any_is_p_mq : ∀ a m p q,
  p = p_of_m m a
  → q = q_of_m m a
  → a == p # m * q ∧ Z.gcd p (z_pos q) = 1%Z.
Proof.
intros a m p q Hp Hq.
progress unfold Q.eq; simpl.
subst p q; simpl.
progress unfold p_of_m, q_of_m; simpl.
remember (q_num a * z_pos m)%Z as p.
remember (q_den a) as q.
remember (Z.gcd p (z_pos q)) as g.
(**)
assert (Hg : (0 < g)%Z). {
  apply Z.lt_iff.
  split; [ rewrite Heqg; apply Z.gcd_nonneg | ].
  intros H; subst g.
  symmetry in H.
  now apply Z.gcd_eq_0 in H.
}
rewrite Z2Pos.id. 2: {
  specialize (Z.gcd_divide_r p (z_pos q)) as H1.
  rewrite <- Heqg in H1.
  destruct H1 as (n, Hn).
  rewrite Hn, Z.mul_div. 2: {
    now intros H; rewrite H in Hg; apply Z.lt_irrefl in Hg.
  }
  apply Z.divide_pos_le; [ | now exists n; rewrite Z.mul_1_r ].
  apply (Z.mul_lt_mono_pos_r g); [ easy | ].
  now rewrite <- Hn.
}
progress unfold Q.compare.
rewrite q_Den_num_den.
cbn.
rewrite Pos2Z.inj_mul.
rewrite Z.mul_assoc.
progress unfold Z.of_pos at 1.
rewrite <- Heqp.
pose proof (Z.gcd_divide_l p (z_pos q)).
rewrite <- Heqg in H.
destruct H as (gp, Hgp).
rewrite Hgp.
assert (g ≠ 0)%Z as Hg0. {
  intros H.
  rewrite Heqg in H.
  apply Z.gcd_eq_0_r in H; revert H; apply Pos2Z_ne_0.
}
rewrite Z.mul_div; auto.
pose proof (Z.gcd_divide_r p (z_pos q)).
rewrite <- Heqg in H.
destruct H as (gq, Hgq).
rewrite Hgq.
rewrite Z.mul_div; auto.
rewrite Z.mul_mul_swap, <- Z.mul_assoc.
rewrite Z2Pos.id. {
  rewrite <- Hgq.
  progress unfold q_Den.
  rewrite <- Heqq.
  progress unfold Z.of_pos.
  rewrite Z.compare_eq_iff.
  split; [ reflexivity | idtac ].
  apply Z.gcd_div_gcd in Heqg; auto.
  rewrite Hgp, Hgq in Heqg.
  rewrite Z.mul_div in Heqg; auto.
  rewrite Z.mul_div in Heqg; auto.
}
apply (Z.mul_le_mono_pos_r g); [ easy | ].
rewrite <- Hgq.
rewrite Z.mul_1_l, Heqg.
apply Z_gcd_pos_r_le.
Qed.

(* [Walker, p. 100]: « [...] where q > 0 and p and q are integers having
   no common factor. » *)
Theorem p_and_q_have_no_common_factors : ∀ a m p q,
  p = p_of_m m a
  → q = q_of_m m a
  → Z.gcd p (z_pos q) = 1%Z.
Proof.
intros a m p q Hp Hq.
eapply any_is_p_mq; eauto .
Qed.

(* [Walker, p. 100]: « If Ph is on L, then also
                   αj - αh
      [...] = γ₁ = ------- = [...]
                    h - j
   » *)
Theorem gamma_value_jh : ∀ f L j αj,
  newton_segments f = Some L
  → (j, αj) = ini_pt L
  → ∀ h αh, (h, αh) ∈ oth_pts L
  → γ L == (αj - αh) / (Qnat h - Qnat j).
Proof.
intros f L j αj HL Hjαj h αh Hhαh.
remember HL as Hh; clear HeqHh.
apply points_in_any_newton_segment with (h := h) (αh := αh) in Hh. {
  apply Qeq_plus_minus_eq_r in Hh.
  remember HL as Haj; clear HeqHaj.
  apply points_in_any_newton_segment with (h := j) (αh := αj) in Haj. {
    rewrite <- Hh, Haj.
    field.
    apply Qlt_not_0, Qnat_lt.
    eapply jq_lt_hq; try eassumption.
  }
  left; rewrite Hjαj; reflexivity.
}
right; right; assumption.
Qed.

Open Scope Z_scope.

Theorem pmq_qmpm : ∀ m p q j k jz kz mj mk,
  (j < k)%nat
  → jz = Z.of_nat j
  → kz = Z.of_nat k
  → p # m * q == (mj - mk # m) / (kz - jz # 1)
  → z_pos q * (mj - mk) = p * (kz - jz).
Proof.
intros m p q j k jz kz mj mk Hjk Hjz Hkz Hpq.
subst jz kz.
apply Z.compare_eq_iff in Hpq.
cbn in Hpq.
do 2 rewrite q_Den_num_den in Hpq.
rewrite Z.mul_1_r in Hpq.
progress unfold Q.div in Hpq.
progress unfold Q.mul in Hpq.
rewrite q_Den_num_den in Hpq.
cbn in Hpq.
do 2 rewrite Pos2Z.inj_mul in Hpq.
assert (Hnjk : Z.of_nat j < Z.of_nat k). {
  destruct j. {
    apply Z.lt_iff.
    split; [ apply Nat2Z.is_nonneg | ].
    cbn; intros H; symmetry in H.
    apply Z.of_nat_eq_0 in H.
    now revert H; apply Nat.neq_0_lt_0.
  }
  destruct k; [ easy | cbn ].
  progress unfold Z.lt; cbn.
  do 2 rewrite Nat.sub_0_r.
  apply Nat.compare_lt_iff.
  now apply Nat.succ_lt_mono in Hjk.
}
rewrite Z2Pos.id in Hpq. 2: {
  rewrite Z.abs_nonneg_eq. 2: {
    apply Z.le_0_sub.
    now apply Z.lt_le_incl.
  }
  apply Z.divide_pos_le. 2: {
    exists (Z.of_nat k - Z.of_nat j)%Z.
    symmetry; apply Z.mul_1_r.
  }
  now apply Z.lt_0_sub.
}
rewrite Z.mul_comm in Hpq; symmetry in Hpq.
rewrite Z.mul_comm in Hpq; symmetry in Hpq.
do 2 rewrite <- Z.mul_assoc in Hpq.
apply Z.mul_cancel_l in Hpq; [ idtac | apply Pos2Z_ne_0 ].
rewrite Z.mul_assoc, Z.mul_comm in Hpq.
symmetry in Hpq.
rewrite Z.mul_comm in Hpq.
symmetry in Hpq.
assert (Hsz : Z.sgn (Z.of_nat k - Z.of_nat j) = 1). {
  progress unfold Z.sgn.
  remember (Z.of_nat _ - Z.of_nat _) as kj eqn:Hkj.
  symmetry in Hkj.
  destruct kj as [| skj vkj]. {
    apply -> Z.sub_move_0_r in Hkj.
    rewrite Hkj in Hnjk.
    now apply Z.lt_irrefl in Hnjk.
  }
  destruct skj; [ easy | ].
  apply Z.lt_0_sub in Hnjk.
  now rewrite Hkj in Hnjk.
}
apply Z.div_unique_exact in Hpq; [ | now rewrite Hsz ].
progress unfold Z.of_pos in Hpq.
rewrite Hpq, Hsz.
rewrite Z.div_1_r.
progress f_equal.
apply Z.abs_nonneg_eq.
now apply Z.le_0_sub, Z.lt_le_incl.
Qed.

Theorem order_in_newton_segment : ∀ f L pl h αh,
  newton_segments f = Some L
  → pl = [ini_pt L … oth_pts L ++ [fin_pt L]]
  → (h, αh) ∈ pl
  → order (ps_poly_nth h f) = qfin αh.
Proof.
intros f L pl h αh HL Hpl Hαh.
remember (ini_pt L) as x eqn:Hini.
symmetry in Hini.
destruct x as (j, αj).
remember (fin_pt L) as x eqn:Hfin.
symmetry in Hfin.
destruct x as (k, αk).
progress unfold ps_poly_nth, ps_lap_nth; simpl.
edestruct in_pts_in_pol; try reflexivity; try eassumption.
subst pl.
simpl in Hαh.
destruct Hαh as [Hαh| Hαh]. {
  injection Hαh; clear Hαh; intros HH H; subst.
  rewrite <- Hini.
  apply ini_fin_ns_in_init_pts; assumption.
}
apply List.in_app_or in Hαh.
destruct Hαh as [Hαh| Hαh]. {
  eapply oth_pts_in_init_pts; try reflexivity; try eassumption.
}
destruct Hαh as [Hαh| Hαh]; [ idtac | contradiction ].
injection Hαh; clear Hαh; intros HH H; subst h αh.
rewrite <- Hfin.
apply ini_fin_ns_in_init_pts; assumption.
Qed.

Theorem qden_αj_is_ps_polydo : ∀ f L j αj,
  newton_segments f = Some L
  → (j, αj) = ini_pt L
  → q_den αj = ps_polydo (ps_poly_nth j f).
Proof.
intros f L j αj HL Hini.
remember HL as H; clear HeqH.
eapply order_in_newton_segment in H; eauto ; [ idtac | left; eauto  ].
progress unfold order in H.
remember (ps_poly_nth j f) as ps.
remember (series_order (ps_terms ps) 0) as v eqn:Hv .
symmetry in Hv.
destruct v; [ idtac | discriminate H ].
injection H; clear H; intros H.
rewrite <- H; reflexivity.
Qed.

Theorem in_K_1_m_order_eq : ∀ ps m v,
  in_K_1_m ps m
  → order ps = qfin v
  → ∃ n, v == n # m.
Proof.
intros ps m v Hin Ho.
progress unfold order in Ho.
remember (series_order (ps_terms ps) 0) as x.
symmetry in Heqx.
destruct x as [x| ]; [ idtac | discriminate Ho ].
injection Ho; clear Ho; intros Ho.
inversion_clear Hin.
destruct H as (ps₁, (Hps, Hm)).
subst v m.
progress unfold Q.eq; simpl.
inversion_clear Hps.
inversion_clear H.
clear H2.
progress unfold normalise_ps in H0, H1; simpl in H0, H1.
rewrite Heqx in H0, H1; simpl in H0, H1.
remember (series_order (ps_terms ps₁) 0) as y.
symmetry in Heqy.
destruct y as [y| ]; simpl in H0, H1. {
  remember (greatest_series_x_power K (ps_terms ps₁) y) as z₁.
  remember (greatest_series_x_power K (ps_terms ps) x) as z.
  remember (gcd_ps x z ps) as g.
  remember (gcd_ps y z₁ ps₁) as g₁.
  remember (ps_ordnum ps₁ + Z.of_nat y)%Z as p₁.
  remember (ps_ordnum ps + Z.of_nat x)%Z as p.
  remember (z_pos (ps_polydo ps₁))%Z as o₁.
  remember (z_pos (ps_polydo ps))%Z as o.
  exists p₁.
  apply Z.compare_eq_iff; cbn.
  do 2 rewrite q_Den_num_den.
  progress unfold Z.of_pos.
  rewrite <- Heqo₁, <- Heqo.
  pose proof (gcd_ps_is_pos x z ps) as Hgp.
  pose proof (gcd_ps_is_pos y z₁ ps₁) as Hgp₁.
  progress unfold gcd_ps in Heqg, Heqg₁, Hgp, Hgp₁.
  rewrite <- Heqp, <- Heqo in Heqg, Hgp.
  rewrite <- Heqp₁, <- Heqo₁ in Heqg₁, Hgp₁.
  subst g g₁.
  rewrite <- Z.gcd_assoc in H0.
  remember (Z.of_nat z₁) as t₁.
  remember (Z.of_nat z) as t.
  pose proof (Z.gcd_divide_l p₁ (Z.gcd o₁ t₁)) as H₁.
  destruct H₁ as (c₁, Hc₁).
  rewrite Hc₁ in H0 at 1.
  rewrite Z.mul_div in H0. 2: {
    symmetry.
    apply Z.lt_neq.
    now rewrite Z.gcd_assoc.
  }
  rewrite <- Z.gcd_assoc in H0.
  pose proof (Z.gcd_divide_l p (Z.gcd o t)) as H.
  destruct H as (c, Hc).
  rewrite Hc in H0 at 1.
  rewrite Z.mul_div in H0. 2: {
    symmetry.
    apply Z.lt_neq.
    rewrite Z.gcd_assoc.
    assumption.
  }
  subst c₁.
  rewrite Z.gcd_comm, Z.gcd_assoc in H1.
  pose proof (Z.gcd_divide_r (Z.gcd t₁ p₁) o₁) as H₁.
  destruct H₁ as (d₁, Hd₁).
  rewrite Hd₁ in H1 at 1.
  rewrite Z.mul_div in H1. 2: {
    symmetry.
    apply Z.lt_neq.
    rewrite <- Z.gcd_assoc, Z.gcd_comm.
    assumption.
  }
  rewrite Z.gcd_comm, Z.gcd_assoc in H1.
  pose proof (Z.gcd_divide_r (Z.gcd t p) o) as H.
  destruct H as (d, Hd).
  rewrite Hd in H1 at 1.
  rewrite Z.mul_div in H1. 2: {
    symmetry.
    apply Z.lt_neq.
    rewrite <- Z.gcd_assoc, Z.gcd_comm.
    assumption.
  }
  apply Z2Pos.inj in H1. {
    subst d₁.
    rewrite <- Z.gcd_assoc, Z.gcd_comm, <- Z.gcd_assoc in Hd.
    rewrite <- Z.gcd_assoc, Z.gcd_comm, <- Z.gcd_assoc in Hd₁.
    remember (Z.gcd p (Z.gcd o t)) as g.
    remember (Z.gcd p₁ (Z.gcd o₁ t₁)) as g₁.
    rewrite Hc, Hc₁, Hd, Hd₁.
    ring.
  } {
    specialize (proj1 (Z.lt_0_mul (Z.gcd (Z.gcd t₁ p₁) o₁) d₁)) as H2.
    assert (H : 0 < Z.gcd (Z.gcd t₁ p₁) o₁ * d₁). {
      now rewrite Z.mul_comm, <- Hd₁, Heqo₁.
    }
    specialize (H2 H); clear H.
    destruct H2 as [H2| (H2, H3)]; [ easy | ].
    exfalso; apply Z.nle_gt in H3.
    apply H3, Z.gcd_nonneg.
  } {
    specialize (proj1 (Z.lt_0_mul (Z.gcd (Z.gcd t p) o) d)) as H2.
    assert (H : 0 < Z.gcd (Z.gcd t p) o * d). {
      now rewrite Z.mul_comm, <- Hd, Heqo.
    }
    specialize (H2 H); clear H.
    destruct H2 as [H2| (H2, H3)]; [ easy | ].
    exfalso; apply Z.nle_gt in H3.
    apply H3, Z.gcd_nonneg.
  }
}
remember (greatest_series_x_power K (ps_terms ps) x) as z.
pose proof (gcd_ps_is_pos x z ps) as Hgp.
progress unfold gcd_ps in H0.
remember (ps_ordnum ps + Z.of_nat x)%Z as p.
remember (z_pos (ps_polydo ps))%Z as o.
remember (Z.of_nat z) as t.
pose proof (Z.gcd_divide_l p (Z.gcd o t)) as H.
destruct H as (c, Hc).
rewrite <- Z.gcd_assoc in H0.
rewrite Hc in H0 at 1.
rewrite Z.mul_div in H0. {
  subst c; simpl in Hc.
  move Hc at top; subst p.
  exists 0%Z; reflexivity.
}
progress unfold gcd_ps in Hgp.
rewrite <- Heqp, <- Heqo, <- Heqt in Hgp.
symmetry.
apply Z.lt_neq.
rewrite Z.gcd_assoc.
assumption.
Qed.

Theorem any_in_K_1_m : ∀ la m h αh,
  ps_lap_forall (λ a, in_K_1_m a m) la
  → (h, αh) ∈ points_of_ps_lap la
  → ∃ mh, αh == mh # m.
Proof.
intros la m h αh HinK Hin.
progress unfold points_of_ps_lap in Hin.
progress unfold points_of_ps_lap_gen in Hin.
progress unfold power_list in Hin.
remember O as pow; clear Heqpow.
revert pow Hin.
induction la as [| a]; intros; [ contradiction | idtac ].
simpl in Hin.
inversion_clear HinK. {
  apply lap_eq_cons_nil_inv in H.
  destruct H as (Ha, Hla); simpl in Ha.
  apply order_inf in Ha.
  rewrite Ha in Hin.
  eapply IHla; eauto.
  constructor; assumption.
}
remember (order a) as v eqn:Hv .
symmetry in Hv.
destruct v as [v| ]. {
  simpl in Hin.
  destruct Hin as [Hin| Hin]. {
    injection Hin; clear Hin; intros; subst v.
    eapply in_K_1_m_order_eq; eauto .
  }
  eapply IHla; eauto.
}
eapply IHla; eauto.
Qed.

Theorem den_αj_divides_num_αj_m : ∀ f L j αj m,
  newton_segments f = Some L
  → ini_pt L = (j, αj)
  → pol_in_K_1_m f m
  → (z_pos (q_den αj) | q_num αj * z_pos m)%Z.
Proof.
intros f L j αj m HL Hini HinK.
apply any_in_K_1_m with (h := j) (αh := αj) in HinK. {
  destruct HinK as (mh, Hmh).
  exists mh.
  apply Z.compare_eq_iff in Hmh; cbn in Hmh.
  rewrite q_Den_num_den in Hmh.
  easy.
}
progress unfold newton_segments in HL.
progress unfold points_of_ps_polynom in HL.
apply ini_fin_ns_in_init_pts in HL.
destruct HL; rewrite <- Hini; assumption.
Qed.

Theorem pol_ord_of_ini_pt : ∀ f L m j αj mj,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → (j, αj) = ini_pt L
  → mj = mh_of_m m αj (ps_poly_nth j f)
  → αj == mj # m.
Proof.
intros f L m j αj mj HL Hm Hini Hmj.
subst mj; simpl.
progress unfold mh_of_m; simpl.
apply Z.compare_eq_iff; cbn.
rewrite q_Den_num_den.
progress unfold q_Den.
rewrite Z.div_mul_swap. {
  erewrite qden_αj_is_ps_polydo; eauto with Arith.
  now rewrite Z.mul_div.
} {
  erewrite <- qden_αj_is_ps_polydo; eauto with Arith.
  eapply den_αj_divides_num_αj_m; eauto with Arith.
}
Qed.

Theorem qden_αk_is_ps_polydo : ∀ f L k αk,
  newton_segments f = Some L
  → (k, αk) = fin_pt L
  → q_den αk = ps_polydo (ps_poly_nth k f).
Proof.
intros f L k αk HL Hfin.
remember HL as H; clear HeqH.
eapply order_in_newton_segment with (h := k) (αh := αk) in H; eauto. {
  progress unfold order in H.
  remember (ps_poly_nth k f) as ps.
  remember (series_order (ps_terms ps) 0) as v eqn:Hv .
  symmetry in Hv.
  destruct v; [ idtac | discriminate H ].
  injection H; clear H; intros H.
  rewrite <- H; reflexivity.
}
rewrite Hfin.
rewrite List.app_comm_cons.
apply List.in_or_app.
right; left; reflexivity.
Qed.

Theorem den_αk_divides_num_αk_m : ∀ f L k αk m,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → fin_pt L = (k, αk)
  → (z_pos (q_den αk) | q_num αk * z_pos m)%Z.
Proof.
intros f L k αk m HL HinK Hini.
apply any_in_K_1_m with (h := k) (αh := αk) in HinK. {
  destruct HinK as (mh, Hmh).
  exists mh.
  apply Z.compare_eq_iff in Hmh; cbn in Hmh.
  rewrite q_Den_num_den in Hmh.
  easy.
}
progress unfold newton_segments in HL.
progress unfold points_of_ps_polynom in HL.
apply ini_fin_ns_in_init_pts in HL.
destruct HL; rewrite <- Hini; assumption.
Qed.

Theorem pol_ord_of_fin_pt : ∀ f L m k αk mk,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → (k, αk) = fin_pt L
  → mk = mh_of_m m αk (ps_poly_nth k f)
  → αk == mk # m.
Proof.
intros f L m k αk mk HL Hm Hini Hmk.
subst mk; simpl.
progress unfold mh_of_m; simpl.
apply Z.compare_eq_iff; cbn.
progress unfold q_Den; cbn.
rewrite Z.div_mul_swap. {
  erewrite qden_αk_is_ps_polydo; eauto with Arith.
  now rewrite Z.mul_div.
} {
  erewrite <- qden_αk_is_ps_polydo; eauto with Arith.
  eapply den_αk_divides_num_αk_m; eauto with Arith.
}
Qed.

Theorem qden_αh_is_ps_polydo : ∀ f L h αh,
  newton_segments f = Some L
  → (h, αh) ∈ oth_pts L
  → q_den αh = ps_polydo (ps_poly_nth h f).
Proof.
intros f L h αh HL Hoth.
remember HL as H; clear HeqH.
eapply order_in_newton_segment with (h := h) (αh := αh) in H; [ | easy | ]. {
  progress unfold order in H.
  remember (ps_poly_nth h f) as ps.
  remember (series_order (ps_terms ps) 0) as v eqn:Hv .
  symmetry in Hv.
  destruct v; [ idtac | discriminate H ].
  injection H; clear H; intros H.
  rewrite <- H; reflexivity.
}
right.
apply List.in_or_app.
left; assumption.
Qed.

Theorem den_αh_divides_num_αh_m : ∀ f L h αh m,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → (h, αh) ∈ oth_pts L
  → (z_pos (q_den αh) | q_num αh * z_pos m)%Z.
Proof.
intros f L h αh m HL HinK Hoth.
apply any_in_K_1_m with (h := h) (αh := αh) in HinK. {
  destruct HinK as (mh, Hmh).
  exists mh.
  apply Z.compare_eq_iff in Hmh; cbn in Hmh.
  rewrite q_Den_num_den in Hmh.
  easy.
} {
  progress unfold newton_segments in HL.
  progress unfold points_of_ps_polynom in HL.
  eapply oth_pts_in_init_pts in HL; eauto with Arith.
}
Qed.

Theorem pol_ord_of_oth_pt : ∀ f L m h αh mh,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → (h, αh) ∈ oth_pts L
  → mh = mh_of_m m αh (ps_poly_nth h f)
  → αh == mh # m.
Proof.
intros f L m h αh mh HL Hm Hfin Hmh.
subst mh; simpl.
progress unfold mh_of_m; simpl.
apply Z.compare_eq_iff; cbn.
progress unfold q_Den; cbn.
rewrite Z.div_mul_swap. {
  erewrite qden_αh_is_ps_polydo; eauto with Arith.
  now rewrite Z.mul_div.
} {
  erewrite <- qden_αh_is_ps_polydo; eauto with Arith.
  eapply den_αh_divides_num_αh_m; eauto with Arith.
}
Qed.

(* [Walker, p. 100]: « In the first place, we note that [...]

         q (mj - mh) = p (h - j)
   » *)
Theorem q_mj_mk_eq_p_h_j : ∀ f L j αj m mj p q,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → (j, αj) = ini_pt L
  → mj = mh_of_m m αj (ps_poly_nth j f)
  → p = p_of_m m (γ L)
  → q = Pos.to_nat (q_of_m m (γ L))
  → ∀ h αh mh, (h, αh) ∈ oth_pts L ++ [fin_pt L]
  → mh = mh_of_m m αh (ps_poly_nth h f)
  → αh == mh # m
    ∧ (Z.of_nat q * (mj - mh) = p * Z.of_nat (h - j))%Z.
Proof.
intros f L j αj m mj p q HL Hm Hj Hmj Hp Hq h αh mh Hh Hmh.
remember (points_of_ps_polynom f) as pts eqn:Hpts .
remember (ps_poly_nth h f) as hps.
apply List.in_app_or in Hh.
remember (fin_pt L) as x eqn:Hfin.
destruct x as (k, αk).
split. {
  apply Z.compare_eq_iff.
  progress unfold q_Den; cbn.
  rewrite Hmh; simpl.
  progress unfold mh_of_m; simpl.
  subst hps.
  destruct Hh as [Hh| [Hk| ]]; [ idtac | idtac | contradiction ]. {
    erewrite <- qden_αh_is_ps_polydo; eauto with Arith.
    rewrite Z.div_mul_swap; [ now rewrite Z.mul_div | ].
    eapply den_αh_divides_num_αh_m; eauto with Arith.
  }
  injection Hk; clear Hk; intros; subst h αh.
  erewrite <- qden_αk_is_ps_polydo; [ | apply HL | apply Hfin ].
  rewrite Z.div_mul_swap; [ now rewrite Z.mul_div | ].
  eapply den_αk_divides_num_αk_m; eauto with Arith.
}
destruct Hh as [Hh| [Hh| ]]; [ idtac | idtac | contradiction ]. {
  remember HL as Hgh; clear HeqHgh.
  eapply gamma_value_jh in Hgh; try eassumption.
  remember (q_of_m m (γ L)) as pq eqn:Hpq .
  pose proof (any_is_p_mq (γ L) m Hp Hpq) as H.
  destruct H as (Hgamma, Hg).
  rewrite Hgamma in Hgh.
  progress unfold Qnat in Hgh.
  rewrite <- Q.inv_sub_distr in Hgh.
  rewrite Nat2Z.inj_sub. {
    rewrite Hq.
    rewrite Z.pos_nat.
    eapply pmq_qmpm; try reflexivity. {
      eapply j_lt_h; try eassumption; reflexivity.
    }
    rewrite Hgh.
    remember Heqhps as Hhps; clear HeqHhps.
    eapply in_pts_in_pol in Hhps; try eassumption. {
      destruct Hhps as (Hhps, Hαh).
      do 2 rewrite Q.inv_sub_distr.
      eapply pol_ord_of_ini_pt in Hj; try eassumption; rewrite Hj.
      eapply pol_ord_of_oth_pt in Hh; try eassumption. {
        rewrite Hh; reflexivity.
      }
      subst hps; assumption.
    }
    eapply oth_pts_in_init_pts; try eassumption.
    progress unfold newton_segments in HL.
    rewrite <- Hpts in HL; assumption.
  }
  apply Nat.lt_le_incl.
  eapply j_lt_h; try eassumption; reflexivity.
}
remember Hj as Hgh; clear HeqHgh.
symmetry in Hh.
eapply gamma_value_jk in Hgh; [ idtac | eassumption ].
remember (q_of_m m (γ L)) as pq eqn:Hpq .
pose proof (any_is_p_mq (γ L) m Hp Hpq) as H.
destruct H as (Hgamma, Hg).
rewrite Hgh in Hgamma.
progress unfold Qnat in Hgamma.
rewrite <- Q.inv_sub_distr in Hgamma.
rewrite Nat2Z.inj_sub. {
  rewrite Hq.
  rewrite Z.pos_nat.
  eapply pmq_qmpm; try reflexivity. {
    eapply j_lt_k; try eassumption; [ now rewrite <- Hj; simpl | ].
    injection Hh; clear Hh; intros; subst h αh.
    now rewrite <- Hfin.
  }
  rewrite <- Hgamma.
  remember Heqhps as Hhps; clear HeqHhps.
  eapply in_pts_in_pol with (hv := αh) in Hhps; try eassumption. {
    destruct Hhps as (Hhps, Hαh).
    do 2 rewrite Q.inv_sub_distr.
    eapply pol_ord_of_ini_pt in Hj; try eassumption; rewrite Hj.
    injection Hh; clear Hh; intros; subst h αh.
    rewrite Q.inv_sub_distr.
    eapply pol_ord_of_fin_pt in Hfin; try eassumption. {
      rewrite Hfin; reflexivity.
    }
    subst hps; assumption.
  }
  rewrite Hh.
  injection Hh; clear Hh; intros; subst h αh.
  rewrite Hfin.
  eapply ini_fin_ns_in_init_pts; try eassumption.
  progress unfold newton_segments in HL.
  rewrite <- Hpts in HL; assumption.
}
apply Nat.lt_le_incl.
eapply j_lt_k; try eassumption. {
  rewrite <- Hj; simpl; reflexivity.
} {
  injection Hh; clear Hh; intros; subst h αh.
  now rewrite <- Hfin.
}
Qed.

Theorem mul_pos_nonneg : ∀ j k c d,
  (j < k)%nat
  → Z.of_nat (k - j) = c * Z.of_nat d
  → 0 <= c.
Proof.
intros j k c d Hjk Hc.
apply (Z.mul_le_mono_pos_r (Z.of_nat d)). {
  destruct d; [ | easy ].
  rewrite Z.mul_comm in Hc; simpl in Hc.
  apply Z.of_nat_eq_0 in Hc.
  apply Nat.sub_0_le in Hc.
  now apply Nat.nlt_ge in Hc.
}
rewrite <- Hc; simpl.
apply Nat2Z.is_nonneg.
Qed.

(* [Walker, p. 100]: « In the first place, we note that [...]
   and since p and q have no common factors, q is a factor
   of h - j. » *)
Theorem q_is_factor_of_h_minus_j : ∀ f L j αj m q,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → (j, αj) = ini_pt L
  → q = Pos.to_nat (q_of_m m (γ L))
  → ∀ h αh, (h, αh) ∈ oth_pts L ++ [fin_pt L]
  → Nat.divide q (h - j).
Proof.
intros f L j αj m q HL Hm Hj Hq h αh Hh.
remember (p_of_m m (γ L)) as p eqn:Hp .
remember HL as H; clear HeqH.
eapply q_mj_mk_eq_p_h_j in H; try eassumption; try reflexivity.
destruct H as (Hαh, Hqjh).
apply List.in_app_or in Hh.
remember (q_of_m m (γ L)) as pq eqn:Hpq ; subst q.
rename pq into q; rename Hpq into Hq.
remember Hp as Hgcd; clear HeqHgcd.
eapply p_and_q_have_no_common_factors in Hgcd; eauto with Arith.
rewrite Z.gcd_comm in Hgcd.
rewrite <- Z.pos_nat in Hgcd.
rewrite Z.gcd_comm in Hgcd.
rewrite Z.gcd_comm in Hgcd.
apply (Z.gauss _ _ (Z.of_nat (h - j))) in Hgcd. {
  destruct Hgcd as (c, Hc).
  exists (Z.to_nat c).
  apply Nat2Z.inj.
  rewrite Nat2Z.inj_mul.
  rewrite Z2Nat.id; [ assumption | idtac ].
  eapply mul_pos_nonneg; try eassumption.
  destruct Hh as [Hh| [Hk| ]]; [ idtac | idtac | contradiction ]. {
    eapply j_lt_h; try eassumption; reflexivity.
  }
  eapply j_lt_k; try eassumption. {
    rewrite <- Hj; simpl; reflexivity.
  } {
    rewrite Hk; simpl; reflexivity.
  }
}
rewrite <- Hqjh.
apply Z.divide_mul_l.
exists 1%Z; symmetry.
apply Z.mul_1_l.
Qed.

(* *)

Theorem list_pad_0 : ∀ z (r : list α), list_pad 0 z r = r.
Proof. reflexivity. Qed.

Open Scope nat_scope.

Theorem minimise_slope_lt_seg : ∀ pt₁ pt₂ pt₃ pts ms₂,
  Sorted fst_lt [pt₁; pt₂; pt₃ … pts]
  → minimise_slope pt₁ pt₃ pts = ms₂
  → HdRel fst_lt pt₂ (oth_pts ms₂).
Proof.
intros pt₁ pt₂ pt₃ pts ms₂ Hsort Hms₂.
revert pt₁ pt₂ pt₃ ms₂ Hsort Hms₂.
induction pts as [| pt₄]; intros; [ subst ms₂; constructor | ].
simpl in Hms₂.
remember (minimise_slope pt₁ pt₄ pts) as ms₄.
symmetry in Heqms₄.
remember (slope_expr pt₁ pt₃ ?= slope ms₄)%Q as c.
symmetry in Heqc.
destruct c. {
  subst ms₂; simpl.
  constructor.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort as (_, Hsort).
  apply Sorted_inv_2 in Hsort.
  destruct Hsort; assumption.
} {
  subst ms₂; constructor.
} {
  move Hms₂ at top; subst ms₄.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_3rd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
}
Qed.

Theorem minimise_slope_seg_sorted : ∀ pt₁ pt₂ pts ms₁,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
  → Sorted fst_lt (oth_pts ms₁).
Proof.
intros pt₁ pt₂ pts ms₁ Hsort Hms₁.
revert pt₁ pt₂ ms₁ Hsort Hms₁.
induction pts as [| pt₃]; intros; [ subst ms₁; constructor | ].
simpl in Hms₁.
remember (minimise_slope pt₁ pt₃ pts) as ms₂.
symmetry in Heqms₂.
remember (slope_expr pt₁ pt₂ ?= slope ms₂)%Q as c.
destruct c. {
  subst ms₁; simpl.
  constructor. {
    eapply IHpts; [ idtac | eassumption ].
    eapply Sorted_minus_2nd; [ idtac | eassumption ].
    intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
  }
  eapply minimise_slope_lt_seg; eassumption.
} {
  subst ms₁; constructor.
} {
  subst ms₂.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
}
Qed.

Theorem edge_pts_sorted : ∀ pts hs,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some hs
    → Sorted fst_lt (oth_pts hs).
Proof.
intros pts hs Hsort Hhs.
destruct pts as [| pt₁]; [ easy | idtac ].
destruct pts as [| pt₂]; [ easy | idtac ].
progress unfold lower_convex_hull_points in Hhs.
injection Hhs; clear Hhs; intros Hhs; subst hs; simpl.
eapply minimise_slope_seg_sorted; [ eassumption | reflexivity ].
Qed.

Theorem ini_oth_fin_pts_sorted : ∀ f L,
  newton_segments f = Some L
  → Sorted fst_lt [ini_pt L … oth_pts L ++ [fin_pt L]].
Proof.
intros f L HL.
constructor. {
  remember HL as HL_v; clear HeqHL_v.
  progress unfold newton_segments in HL.
  remember (points_of_ps_polynom f) as pts.
  apply points_of_polyn_sorted in Heqpts.
  apply Sorted_app_at_r. {
    eapply edge_pts_sorted; eassumption.
  }
  intros (hq, αh) Hh.
  eapply hq_lt_kq; try eassumption.
  symmetry; apply surjective_pairing.
}
remember (ini_pt L) as x eqn:Hini.
symmetry in Hini.
destruct x as (j, αj).
remember (fin_pt L) as x eqn:Hfin.
symmetry in Hfin.
destruct x as (k, αk).
symmetry in Hini, Hfin.
apply HdRel_app. {
  remember (oth_pts L) as pts eqn:Hpts .
  symmetry in Hpts.
  destruct pts as [| (h, ah)]; constructor.
  progress unfold fst_lt; cbn.
  eapply jq_lt_hq; try eassumption.
  rewrite Hpts; left; reflexivity.
}
constructor.
progress unfold fst_lt; cbn.
eapply jz_lt_kz; try eassumption. {
  rewrite <- Hini; reflexivity.
} {
  rewrite <- Hfin; reflexivity.
}
Qed.

Close Scope nat_scope.

(* not real degree, since last coefficient can be null *)
Definition pseudo_degree (p : polynomial α) := pred (List.length (al p)).

Theorem list_shrink_skipn : ∀ cnt k (l : list α),
  list_shrink_aux cnt k l = list_shrink_aux 0 k (List.skipn cnt l).
Proof.
intros cnt k l.
revert cnt.
induction l as [| x]; intros; [ now destruct cnt | simpl ].
destruct cnt; [ reflexivity | simpl ].
apply IHl.
Qed.

Theorem length_shrink_skipn_lt : ∀ k (l : list α) m,
  (length l < S k)%nat
  → length (list_shrink_aux 0 m (List.skipn k l)) = 0%nat.
Proof.
intros k l m Hk.
revert k m Hk.
induction l as [| x]; intros; [ destruct k; reflexivity | simpl ].
simpl in Hk.
apply Nat.succ_lt_mono in Hk.
destruct k. {
  exfalso; revert Hk; apply Nat.nlt_0_r.
}
simpl; apply IHl; assumption.
Qed.

Theorem length_shrink_skipn_eq : ∀ k (l : list α) m,
  length l = S k
  → length (list_shrink_aux 0 m (List.skipn k l)) = 1%nat.
Proof.
intros k l m Hk.
revert k m Hk.
induction l as [| x]; intros; [ discriminate Hk | simpl ].
simpl in Hk.
apply -> Nat.succ_inj_wd in Hk.
destruct k. {
  destruct l; [ reflexivity | discriminate Hk ].
}
simpl; apply IHl; assumption.
Qed.

Theorem list_length_shrink : ∀ cnt k (l : list α),
  (S cnt < length l)%nat
  → List.length (list_shrink_aux cnt k l) = S ((List.length l - S cnt) / S k).
Proof.
intros cnt k l Hcl.
revert cnt k Hcl.
induction l; intros. {
  exfalso; revert Hcl; apply Nat.nlt_0_r.
}
remember (S k) as k'; simpl; subst k'.
remember (S k) as k'; destruct cnt; simpl; subst k'. {
  rewrite Nat.sub_0_r.
  apply Nat.succ_inj_wd.
  destruct (lt_eq_lt_dec (S k) (length l)) as [[H₁| H₁]| H₁]. {
    rewrite IHl; [ idtac | assumption ].
    simpl in Hcl.
    assert (length l = length l - S k + 1 * S k)%nat as H. {
      rewrite Nat.mul_1_l.
      rewrite Nat.sub_add; auto with Arith.
      apply Nat.lt_le_incl; auto with Arith.
    }
    rewrite H in |- * at 2; clear H.
    rewrite Nat.div_add; [ idtac | intros H; discriminate H ].
    rewrite Nat.add_1_r; reflexivity.
  } {
    rewrite <- H₁.
    rewrite Nat.div_same; auto with Arith.
    rewrite list_shrink_skipn.
    apply length_shrink_skipn_eq; symmetry; assumption.
  } {
    rewrite Nat.div_small; [ idtac | assumption ].
    rewrite list_shrink_skipn.
    apply length_shrink_skipn_lt; assumption.
  }
}
simpl in Hcl.
apply Nat.succ_lt_mono in Hcl.
apply IHl; assumption.
Qed.

Theorem list_length_pad : ∀ n (z : α) l,
  List.length (list_pad n z l) = (n + List.length l)%nat.
Proof.
intros n z l.
induction n; [ reflexivity | simpl ].
rewrite IHn; reflexivity.
Qed.

Theorem length_char_pol_succ : ∀ j x l,
  (j < power (List.hd x l))%nat
  → Sorted (λ a b, (power a < power b)%nat) (l ++ [x])
  → List.length (make_char_pol R (S j) (l ++ [x])) = (power x - j)%nat.
Proof.
intros j x l Hjpx Hsort.
revert j x Hjpx Hsort.
induction l as [| a]; intros; simpl. {
  rewrite list_length_pad; simpl.
  simpl in Hjpx.
  rewrite <- Nat.add_sub_swap; auto with Arith.
  rewrite Nat.add_1_r; reflexivity.
}
rewrite list_length_pad; simpl.
simpl in Hjpx.
rewrite IHl. {
  eapply Sorted_trans_app in Hsort; [ idtac | idtac | left; eauto  ]. {
    rewrite <- Nat.add_sub_swap; auto with Arith.
    rewrite <- Nat.sub_succ_l; [ idtac | apply Nat.lt_le_incl; auto ].
    rewrite Nat.add_sub_assoc; [ idtac | apply Nat.lt_le_incl; auto ].
    rewrite Nat.add_sub_swap; auto with Arith.
    rewrite Nat.sub_diag; reflexivity.
  }
  clear x Hsort.
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
} {
  simpl in Hsort.
  destruct l as [| b]; simpl in Hsort; simpl. {
    apply Sorted_inv_2 in Hsort.
    destruct Hsort; assumption.
  } {
    apply Sorted_inv_2 in Hsort.
    destruct Hsort; assumption.
  }
}
simpl in Hsort.
apply Sorted_inv in Hsort.
destruct Hsort; assumption.
Qed.

Theorem length_char_pol : ∀ f L pl tl j αj k αk,
  newton_segments f = Some L
  → ini_pt L = (j, αj)
  → fin_pt L = (k, αk)
  → pl = [ini_pt L … oth_pts L ++ [fin_pt L]]
  → tl = List.map (term_of_point f) pl
  → length (make_char_pol R j tl) = S (k - j).
Proof.
intros f L pl tl j αj k αk HL Hini Hfin Hpl Htl.
rewrite Htl, Hpl, Hini; simpl.
rewrite Nat.sub_diag; simpl.
rewrite List.map_app; simpl.
rewrite length_char_pol_succ; simpl; [ now rewrite Hfin | | ]. {
  remember (List.map (term_of_point f) (oth_pts L)) as tl₂ eqn:Htl₂ .
  remember (term_of_point f (k, αk)) as tk eqn:Htk .
  progress unfold term_of_point, lap_term_of_point in Htk; simpl in Htk.
  subst tk; simpl.
  remember (oth_pts L) as pts eqn:Hpts .
  symmetry in Hpts.
  destruct pts as [| (h, αh)]. {
    subst tl₂; simpl.
    rewrite Hfin; simpl.
      eapply j_lt_k; try eassumption. {
      rewrite Hini; simpl; reflexivity.
    } {
      rewrite Hfin; simpl; reflexivity.
    }
  }
  subst tl₂; simpl.
  assert ((h, αh) ∈ oth_pts L) as Hh by now rewrite Hpts; left.
  remember Hh as H; clear HeqH.
  symmetry in Hini.
  eapply j_lt_h; eassumption.
}
remember HL as Hsort; clear HeqHsort.
apply ini_oth_fin_pts_sorted in Hsort.
apply Sorted_inv_1 in Hsort.
remember (oth_pts L ++ [fin_pt L]) as pts eqn:Hpts .
remember (List.map (term_of_point f) pts) as li eqn:Hli .
remember Hli as H; clear HeqH.
rewrite Hpts in Hli.
rewrite List.map_app in Hli; simpl in Hli.
rewrite <- Hli, H.
assert (Hnat : ∀ pt, pt ∈ pts → ∃ (h : nat) (αh : Q), pt = (h, αh)). {
  intros pt Hpt.
  destruct pt as (h, αh).
  now exists h, αh.
}
revert Hsort Hnat; clear; intros.
induction pts as [| pt]; [ constructor | simpl ].
constructor. {
  apply IHpts. {
    eapply Sorted_inv_1; eassumption.
  }
  intros pt₁ Hpt₁.
  apply Hnat.
  right; assumption.
}
apply Sorted_inv in Hsort.
destruct Hsort as (_, Hrel).
progress unfold fst_lt in Hrel.
revert Hrel Hnat; clear; intros.
destruct pts as [| pt₁]; constructor; simpl.
apply HdRel_inv in Hrel.
assert (pt ∈ [pt; pt₁ … pts]) as H₁ by now left.
assert (pt₁ ∈ [pt; pt₁ … pts]) as H₂ by now right; left.
apply Hnat in H₁.
apply Hnat in H₂.
destruct H₁ as (h₁, (ah₁, Hh₁)).
destruct H₂ as (h₂, (ah₂, Hh₂)).
now subst pt pt₁; simpl in Hrel; simpl.
Qed.

Theorem Sorted_fst_lt_nat_num_fst : ∀ l,
  Sorted fst_lt l
  → Sorted (λ x y, (fst x < fst y)%nat) l.
Proof.
intros l Hsort.
apply Sorted_LocallySorted_iff in Hsort.
apply Sorted_LocallySorted_iff.
induction l as [| a]; [ constructor | idtac ].
destruct l as [| b]; constructor. {
  apply IHl.
  inversion Hsort; assumption.
}
now inversion Hsort; subst.
Qed.

Theorem fold_char_pol : ∀ f j αj tl,
  [order_coeff (List.nth j (al f) 0%ps)
   … make_char_pol R (S j) (List.map (term_of_point f) tl)] =
  make_char_pol R j
    (List.map (term_of_point f) [(j, αj) … tl]).
Proof.
intros f j αj tl; simpl.
rewrite Nat.sub_diag; simpl.
reflexivity.
Qed.

Definition nat_fst_lt (x y : nat * Q) := (fst x < fst y)%nat.

Theorem shrinkable_if : ∀ f q pt₁ pts,
  Sorted nat_fst_lt [pt₁ … pts]
  → q ≠ O
  → List.Forall (λ pt, Nat.divide q (fst pt - fst pt₁))
       pts
  → poly_shrinkable q
      POL (make_char_pol R (fst pt₁)
            (List.map (term_of_point f) [pt₁ … pts]))%pol.
Proof.
intros f q pt₁ pts Hsort Hq Hpts; simpl.
rewrite Nat.sub_diag, list_pad_0.
rewrite List.Forall_forall in Hpts.
progress unfold poly_shrinkable; intros n Hn; simpl.
destruct n. {
  rewrite Nat.Div0.mod_0_l in Hn; auto with Arith.
  exfalso; apply Hn; reflexivity.
}
revert n pt₁ Hsort Hpts Hn.
induction pts as [| pt₂]; intros; [ destruct n; reflexivity | simpl ].
apply Sorted_inv in Hsort.
destruct Hsort as (Hsort, Hrel).
apply HdRel_inv in Hrel.
progress unfold nat_fst_lt in Hrel; simpl in Hrel.
destruct (lt_dec (fst pt₁) (fst pt₂)) as [H₁| H₁]. {
  progress unfold lt in H₁.
  remember (fst pt₁) as j eqn:Hj .
  remember (fst pt₂) as h eqn:Hh .
  destruct (eq_nat_dec (S j) h) as [H₂| H₂]. {
    assert (pt₂ ∈ [pt₂ … pts]) as H by now left.
    apply Hpts in H.
    rewrite <- Hh in H.
    rewrite <- H₂ in H.
    rewrite Nat_sub_succ_diag in H.
    destruct H as (c, Hc).
    symmetry in Hc.
    apply Nat.mul_eq_1 in Hc.
    destruct Hc as (Hc, Hq₁).
    rewrite Hq₁ in Hn.
    exfalso; apply Hn.
    reflexivity.
  }
  destruct (lt_dec n (h - S j)) as [H₃| H₃]. {
    rewrite list_nth_pad_lt; auto with Arith.
  }
  apply Nat.nlt_ge in H₃.
  rewrite list_nth_pad_sub; auto with Arith.
  destruct (eq_nat_dec (h - S j) n) as [H₄| H₄]. {
    exfalso.
    assert (pt₂ ∈ [pt₂ … pts]) as H by now left.
    apply Hpts in H.
    rewrite <- Hh in H.
    destruct H as (c, Hc).
    rewrite <- H₄ in Hn.
    simpl in Hsort; simpl.
    rewrite <- Nat.sub_succ_l in Hn; auto with Arith.
    rewrite Nat.sub_succ in Hn.
    rewrite Hc in Hn.
    apply Hn, Nat.Div0.mod_mul; auto with Arith.
  }
  remember (n - (h - S j))%nat as nhj eqn:Hnhj .
  symmetry in Hnhj.
  destruct nhj. {
    apply Nat.sub_0_le in Hnhj.
    apply Nat_le_neq_lt in H₃; auto with Arith.
    apply Nat.nle_gt in H₃.
    contradiction.
  }
  destruct (eq_nat_dec (S nhj mod q) 0) as [H₅| H₅]. {
    apply Nat.Div0.mod_divides in H₅; auto with Arith.
    destruct H₅ as (c, Hc).
    apply Nat.add_sub_eq_nz in Hnhj; [ idtac | intros H; discriminate H ].
    exfalso; apply Hn.
    rewrite <- Hnhj.
    rewrite Hc.
    rewrite <- Nat.add_succ_l.
    rewrite <- Nat.sub_succ_l; auto with Arith.
    rewrite Nat.sub_succ.
    assert (pt₂ ∈ [pt₂ … pts]) as H by now left.
    apply Hpts in H.
    rewrite <- Hh in H.
    destruct H as (d, Hd).
    rewrite Nat.mul_comm.
    rewrite Hd, <- Nat.mul_add_distr_r.
    apply Nat.Div0.mod_mul; auto with Arith.
  }
  rewrite Hh.
  apply IHpts; auto with Arith.
  intros pt Hpt.
  assert (pt ∈ [pt₂ … pts]) as H by now right.
  apply Hpts in H.
  destruct H as (c, Hc).
  rewrite <- Hh.
  progress unfold Nat.divide.
  assert (pt₂ ∈ [pt₂ … pts]) as H by now left.
  apply Hpts in H.
  rewrite <- Hh in H.
  destruct H as (d, Hd).
  exists (c - d)%nat.
  rewrite Nat.mul_sub_distr_r.
  rewrite <- Hc, <- Hd.
  rewrite Nat_sub_sub_distr; [ idtac | apply Nat.lt_le_incl; auto ].
  rewrite Nat.sub_add; auto with Arith.
  apply Nat.lt_le_incl.
  eapply Nat.lt_trans; eauto with Arith.
  revert Hsort Hh Hpt; clear; intros; subst h.
  revert pt₂ pt Hsort Hpt.
  induction pts as [| pt₃]; intros; [ contradiction | idtac ].
  destruct Hpt as [Hpt| Hpt]. {
    subst pt.
    apply Sorted_inv in Hsort.
    destruct Hsort as (_, Hrel).
    apply HdRel_inv in Hrel.
    assumption.
  }
  apply IHpts; auto with Arith.
  eapply Sorted_minus_2nd; eauto with Arith.
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
}
contradiction.
Qed.

Theorem phi_pseudo_degree_is_k_sub_j_div_q : ∀ f L j αj k αk q m,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → (j, αj) = ini_pt L
  → (k, αk) = fin_pt L
  → q = Pos.to_nat (q_of_m m (γ L))
  → poly_shrinkable q (Φq f L)
    ∧ pseudo_degree (Φs q f L) = ((k - j) / q)%nat.
Proof.
intros f L j αj k αk q m HL Hm Hj Hk Hq.
split. {
  apply shrinkable_if. {
    remember HL as H; clear HeqH.
    apply ini_oth_fin_pts_sorted in H.
    apply Sorted_fst_lt_nat_num_fst in H; auto with Arith.
  } {
    rewrite Hq; auto with Arith.
  } {
    apply List.Forall_forall.
    intros pt Hpt.
    rewrite <- Hj; simpl.
    apply List.in_app_or in Hpt.
    destruct Hpt as [Hpt| Hpt]. {
      destruct pt as (h, αh); cbn.
      eapply q_is_factor_of_h_minus_j; eauto with Arith.
      apply List.in_or_app; left; eauto with Arith.
    }
    destruct Hpt as [Hpt| ]; [ idtac | contradiction ].
    subst pt; simpl.
    rewrite <- Hk; simpl.
    eapply q_is_factor_of_h_minus_j; eauto with Arith.
    apply List.in_or_app.
    right; left; eauto with Arith.
  }
}
progress unfold pseudo_degree, Φs; simpl.
rewrite <- Hj; simpl.
rewrite Nat.sub_diag, list_pad_0.
progress unfold list_shrink.
rewrite list_length_shrink; simpl. {
  rewrite divmod_div.
  rewrite Nat.sub_0_r.
  f_equal. {
    rewrite List.map_app; simpl.
    rewrite length_char_pol_succ; [ now rewrite <- Hk | | ]. {
      remember (oth_pts L) as opts eqn:Hopts .
      symmetry in Hopts.
      destruct opts as [| (h, αh)]. {
        simpl.
        rewrite <- Hk; simpl.
        eapply j_lt_k; try eassumption. {
          now rewrite <- Hj; simpl.
        } {
          now rewrite <- Hk; simpl.
        }
      }
      simpl.
      assert ((h, αh) ∈ oth_pts L) as H. {
        rewrite Hopts; left; reflexivity.
      }
      eapply j_lt_h; try eassumption; try reflexivity.
    }
    rewrite list_map_app_at.
    apply Sorted_map.
    apply Sorted_fst_lt_nat_num_fst. {
      eapply Sorted_inv_1.
      eapply ini_oth_fin_pts_sorted; eassumption.
    }
  }
  subst q.
  rewrite <- Nat.sub_succ_l; [ apply Nat_sub_succ_1 | idtac ].
  now apply Nat.neq_0_lt_0.
}
apply -> Nat.succ_lt_mono.
clear Hj.
revert j.
induction (oth_pts L); intros; simpl. {
  rewrite list_length_pad; simpl.
  rewrite <- Hk; simpl.
  rewrite Nat.add_comm; simpl.
  apply Nat.lt_0_succ.
} {
  rewrite list_length_pad; simpl.
  eapply Nat.lt_le_trans. {
    apply IHl with (j := fst a).
  }
  rewrite Nat.add_succ_r, <- Nat.add_succ_l.
  apply Nat.le_add_l.
}
Qed.

Definition has_degree f d :=
  pseudo_degree f = d ∧ (List.nth d (al f) 0 ≠ 0)%K.

Theorem list_nth_shrink : ∀ n k l (d : α) cnt,
  List.nth n (list_shrink_aux cnt k l) d = List.nth (cnt + n * S k) l d.
Proof.
intros n k l d cnt.
revert n k cnt.
induction l as [| a]; intros; [ destruct n, cnt; reflexivity | idtac ].
destruct n; simpl. {
  destruct cnt; simpl; [ reflexivity | rewrite IHl; reflexivity ].
} {
  destruct cnt; simpl; rewrite IHl; reflexivity.
}
Qed.

Theorem ord_coeff_non_zero_in_newt_segm : ∀ f L h αh hps,
  newton_segments f = Some L
  → (h, αh) ∈ [ini_pt L … oth_pts L ++ [fin_pt L]]
  → hps = List.nth h (al f) 0%ps
  → (order_coeff hps ≠ 0)%K.
Proof.
intros f L h αh hps HL Hh Hhps.
progress unfold order_coeff.
remember (series_order (ps_terms hps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]. {
  apply series_order_iff in Hn.
  destruct Hn; assumption.
}
remember (points_of_ps_polynom f) as pts eqn:Hpts .
remember Hpts as H; clear HeqH.
eapply in_pts_in_pol in H; try eassumption. {
  destruct H as (Hhp, Hhhv).
  progress unfold order in Hhhv.
  rewrite Hn in Hhhv; discriminate Hhhv.
}
progress unfold newton_segments in HL.
rewrite <- Hpts in HL.
destruct Hh as [Hh| Hh]. {
  apply ini_fin_ns_in_init_pts in HL.
  rewrite Hh in HL.
  destruct HL; eassumption.
}
apply List.in_app_or in Hh.
destruct Hh as [Hh| [Hh| ]]; [ idtac | idtac | contradiction ]. {
  eapply oth_pts_in_init_pts in HL; eassumption.
}
apply ini_fin_ns_in_init_pts in HL.
rewrite Hh in HL.
destruct HL; eassumption.
Qed.

Theorem Sorted_fst_2nd_lt_last : ∀ j αj k αk t₁ t₂ t₃ tl,
  Sorted (λ pt₁ pt₂, (fst pt₁ < fst pt₂)%nat) [t₁; t₂; t₃ … tl]
  → (j, αj) = t₁
  → (S k, αk) = List.last [t₃ … tl] (0%nat, 0%Q)
  → (fst t₂ < S k)%nat.
Proof.
intros j αj k αk t₁ t₂ t₃ tl Hsort Hj Hk.
revert k αk t₃ Hsort Hk.
induction tl as [| t₄]; intros. {
  simpl in Hk.
  apply Sorted_inv in Hsort.
  destruct Hsort as (Hsort, Hrel).
  apply Sorted_inv in Hsort.
  destruct Hsort as (Hsort, Hrel₁).
  apply HdRel_inv in Hrel₁.
  rewrite <- Hk in Hrel₁; remember (S k) as x; simpl in Hrel₁; subst x.
  easy.
}
remember [t₄ … tl] as x; simpl in Hk; subst x.
eapply IHtl; try eassumption.
eapply Sorted_minus_3rd; [ idtac | eassumption ].
intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
Qed.

Theorem list_nth_coeff_last : ∀ f j αj k αk tl,
  (j, αj) = List.hd (0%nat, 0%Q) tl
  → (k, αk) = List.last tl (0%nat, 0%Q)
  → (j < k)%nat
  → Sorted (λ pt₁ pt₂, (fst pt₁ < fst pt₂)%nat) tl
  → List.nth (k - j)
      (make_char_pol R j
         (List.map (term_of_point f) tl)) 0%K =
      coeff (term_of_point f (List.last tl (0%nat, 0%Q))).
Proof.
intros f j αj k αk tl Hj Hk Hjk Hsort; simpl.
destruct tl as [| t₁]. {
  simpl in Hj, Hk.
  injection Hj; clear Hj; intros; subst αj.
  injection Hk; clear Hk; intros; subst αk.
  subst j k.
  exfalso; revert Hjk; apply Nat.lt_irrefl.
}
simpl in Hj; rewrite <- Hk, <- Hj; simpl.
rewrite Nat.sub_diag, list_pad_0.
destruct tl as [| t₂]. {
  simpl in Hk; subst t₁.
  injection Hk; clear Hk; intros; subst k.
  exfalso; revert Hjk; apply Nat.lt_irrefl.
}
simpl.
remember (k - j)%nat as kj eqn:Hkj .
symmetry in Hkj.
destruct kj; [ exfalso; fast_omega Hjk Hkj | idtac ].
destruct k; [ discriminate Hkj | idtac ].
rewrite Nat.sub_succ_l in Hkj; [ idtac | fast_omega Hjk ].
apply eq_add_S in Hkj; subst kj.
revert j αj k αk t₁ t₂ Hj Hk Hjk Hsort.
induction tl as [| t₃]; intros. {
  simpl in Hk; subst t₂; simpl.
  remember (S k) as x; simpl; subst x.
  rewrite list_nth_pad_sub; [ rewrite Nat.sub_diag | idtac ]; reflexivity.
}
simpl.
rewrite list_nth_pad_sub. {
  rewrite Nat_sub_sub_distr. {
    rewrite Nat.add_succ_r.
    rewrite Nat.sub_add; [ idtac | fast_omega Hjk ].
    rewrite Nat.sub_succ_l. {
      simpl.
      destruct t₂ as (h₁, αh₁).
      eapply IHtl with (αj := αh₁); try eassumption; try reflexivity. {
        eapply Sorted_fst_2nd_lt_last; eassumption.
      } {
        now apply Sorted_inv in Hsort.
      }
    }
    apply Nat.lt_succ_r.
    eapply Sorted_fst_2nd_lt_last; eassumption.
  }
  subst t₁.
  apply Sorted_inv in Hsort.
  destruct Hsort as (_, H).
  now apply HdRel_inv in H; simpl in H.
}
remember (fst t₂) as h₁ eqn:Hh₁ .
remember (h₁ - S j)%nat as x.
rewrite <- Nat.sub_succ; subst x.
apply Nat.sub_le_mono_r.
apply Nat.le_le_succ_r.
apply Nat.lt_succ_r.
subst h₁.
eapply Sorted_fst_2nd_lt_last; eassumption.
Qed.

Theorem Sorted_Qnat_Sorted_q_num : ∀ pts,
  Sorted fst_lt pts
  → Sorted (λ pt₁ pt₂, (fst pt₁ < fst pt₂)%nat) pts.
Proof.
intros pts Hsort.
apply Sorted_LocallySorted_iff in Hsort.
apply Sorted_LocallySorted_iff.
induction pts as [| pt]; [ constructor | idtac ].
destruct pts as [| pt₂]; constructor. {
  apply IHpts.
  inversion Hsort; assumption.
}
now inversion Hsort.
Qed.

(* [Walker, p. 100] « Therefore (3.4) has the form c^j Φ(c^q) = 0
   where Φ(z) is a polynomial, of degree (k - j)/q » *)
Theorem phi_degree_is_k_sub_j_div_q : ∀ f L j αj k αk q m,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → (j, αj) = ini_pt L
  → (k, αk) = fin_pt L
  → q = Pos.to_nat (q_of_m m (γ L))
  → poly_shrinkable q (Φq f L)
     ∧ has_degree (Φs q f L) ((k - j) / q).
Proof.
intros f L j αj k αk q m HL Hm Hj Hk Hq.
split. {
  apply shrinkable_if. {
    remember HL as H; clear HeqH.
    apply ini_oth_fin_pts_sorted in H.
    apply Sorted_fst_lt_nat_num_fst in H; auto with Arith.
  } {
    rewrite Hq; auto with Arith.
  }
  apply List.Forall_forall.
  intros pt Hpt.
  rewrite <- Hj; simpl.
  apply List.in_app_or in Hpt.
  destruct Hpt as [Hpt| Hpt]. {
    destruct pt as (h, αh); cbn.
    eapply q_is_factor_of_h_minus_j; eauto with Arith.
    apply List.in_or_app; left; eauto with Arith.
  }
  destruct Hpt as [Hpt| ]; [ idtac | contradiction ].
  subst pt; simpl.
  rewrite <- Hk; simpl.
  eapply q_is_factor_of_h_minus_j; eauto with Arith.
  apply List.in_or_app.
  right; left; eauto with Arith.
}
progress unfold has_degree.
progress unfold pseudo_degree.
remember (al (Φs q f L)) as l.
apply imp_or_tauto. {
  intros H.
  progress unfold Φs in Heql.
  rewrite Φq_f in Heql.
  remember [ini_pt L … oth_pts L ++ [fin_pt L]] as pl.
  rewrite <- Hj in Heql; simpl in Heql.
  subst l.
  progress unfold list_shrink.
  rewrite list_nth_shrink.
  rewrite Nat.add_0_l.
  rewrite <- Nat.sub_succ_l; [ | now subst q; apply Nat.neq_0_lt_0 ].
  rewrite Nat_sub_succ_1.
  rewrite Nat.mul_comm.
  rewrite <- Nat.Lcm0.divide_div_mul_exact. {
    rewrite Nat.mul_comm.
    rewrite Nat.div_mul; [ idtac | subst q; auto with Arith ].
    subst pl.
    erewrite list_nth_coeff_last; try eassumption. {
      rewrite list_last_cons_app; simpl.
      rewrite <- Hk; simpl.
      eapply ord_coeff_non_zero_in_newt_segm; [ apply HL | | easy ].
      rewrite <- Hk; right.
      apply List.in_or_app; right; left; reflexivity.
    } {
      rewrite list_last_cons_app; eassumption.
    } {
      eapply j_lt_k; try eassumption; [ now rewrite <- Hj | ].
      now rewrite <- Hk.
    } {
      constructor. {
        apply Sorted_app_at_r. {
          remember HL as Hsort; clear HeqHsort.
          apply ini_oth_fin_pts_sorted in Hsort.
          apply Sorted_inv_1 in Hsort.
          apply Sorted_app in Hsort.
          destruct Hsort as (Hsort, _).
          apply Sorted_Qnat_Sorted_q_num.
          apply ini_oth_fin_pts_sorted in HL.
          apply Sorted_inv_1 in HL.
          now apply Sorted_app in HL.
        }
        intros pt Hpt.
        remember HL as Hsort; clear HeqHsort.
        apply ini_oth_fin_pts_sorted in Hsort.
        apply Sorted_inv_1 in Hsort.
        apply Sorted_Qnat_Sorted_q_num in Hsort.
        eapply Sorted_trans_app in Hsort; try eassumption.
        intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.
      }
      apply HdRel_app; [ idtac | constructor ]. {
        remember (oth_pts L) as pts eqn:Hpts .
        symmetry in Hpts.
        destruct pts as [| pt]; constructor.
        rewrite <- Hj; simpl.
        destruct pt as (h, αh); simpl.
        eapply j_lt_h; try eassumption; try reflexivity.
        now rewrite Hpts; left.
      }
      rewrite <- Hj, <- Hk; simpl.
      eapply jz_lt_kz; try eassumption. {
        rewrite <- Hj; reflexivity.
      } {
        rewrite <- Hk; reflexivity.
      }
    }
  }
  eapply q_is_factor_of_h_minus_j; try eassumption.
  apply List.in_or_app; right; left; symmetry; eassumption.
}
subst l.
eapply phi_pseudo_degree_is_k_sub_j_div_q; eassumption.
Qed.

End theorems.
