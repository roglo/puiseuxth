(* CharactPolyn.v *)

Require Import Utf8 QArith Sorted NPeano.

Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Misc.
Require Import Nbar.
Require Import Qbar.
Require Import Newton.
Require Import PolyConvexHull.
Require Import Field.
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

Definition nat_num q := Z.to_nat (Qnum q).

Fixpoint make_char_pol α (R : ring α) pow tl :=
  match tl with
  | [] => []
  | [t₁ … tl₁] =>
      list_pad (power t₁ - pow) 0%K
        [coeff t₁ … make_char_pol R (S (power t₁)) tl₁]
    end.

Definition lap_term_of_point α {R : ring α} {K : field R} la (pt : (Q * Q)) :=
  let h := nat_num (fst pt) in
  let ps := List.nth h la 0%ps in
  let c := order_coeff ps in
  {| coeff := c; power := h |}.

Definition term_of_point α {R : ring α} {K : field R} pol (pt : (Q * Q)) :=
  lap_term_of_point (al pol) pt.

Definition Φq α {R : ring α} {K : field R} pol ns :=
  let pl := [ini_pt ns … oth_pts ns ++ [fin_pt ns]] in
  let tl := List.map (term_of_point pol) pl in
  let j := nat_num (fst (ini_pt ns)) in
  {| al := make_char_pol R j tl |}.

Definition ps_lap_com_polord α (psl : list (puiseux_series α)) :=
  List.fold_right (λ ps a, (a * ps_polord ps)%positive) 1%positive psl.

Definition ps_pol_com_polord {α} pol := @ps_lap_com_polord α (al pol).
Arguments ps_pol_com_polord _ pol%pol.

(* *)

Theorem nat_num_Qnat : ∀ i, nat_num (Qnat i) = i.
Proof.
intros i.
unfold nat_num, Qnat; simpl.
rewrite Nat2Z.id; reflexivity.
Qed.

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
  let p := (Qnum a * ' m)%Z in
  let q := Qden a in
  (p / Z.gcd p ('q))%Z.

Definition q_of_m m a :=
  let p := (Qnum a * ' m)%Z in
  let q := Qden a in
  Z.to_pos ('q / Z.gcd p ('q)).

Definition mh_of_m α m αh (hps : puiseux_series α) :=
  (Qnum αh * ' m / ' ps_polord hps)%Z.

(* express that some puiseux series ∈ K(1/m)* *)
Inductive in_K_1_m {α} {R : ring α} {K : field R} ps m :=
  InK1m : (∃ ps₁, (ps₁ = ps)%ps ∧ ps_polord ps₁ = m) → in_K_1_m ps m.

Arguments in_K_1_m _ _ _ ps%ps m%positive.

Definition pol_in_K_1_m {α} {R : ring α} {K : field R} pol m :=
  ps_lap_forall (λ a, in_K_1_m a m) (al pol).

Definition poly_shrinkable α (R : ring α) {K : field R} q pol :=
  ∀ n, n mod q ≠ O → List.nth n (al pol) 0%K = 0%K.

(* usable only if poly_shrinkable q (Φq pol ns) *)
Definition Φs α {R : ring α} {K : field R} q pol ns :=
  poly_shrink q (Φq pol ns).

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Theorem al_Φq : ∀ pol ns,
  al (Φq pol ns)
  = make_char_pol R (nat_num (fst (ini_pt ns)))
      (List.map (term_of_point pol) [ini_pt ns … oth_pts ns ++ [fin_pt ns]]).
Proof.
intros pol ns; reflexivity.
Qed.

Theorem Φq_pol : ∀ pol ns,
  Φq pol ns
  = POL
      (make_char_pol R (nat_num (fst (ini_pt ns)))
         (List.map (term_of_point pol)
            [ini_pt ns … oth_pts ns ++ [fin_pt ns]]))%pol.
Proof.
intros pol ns.
unfold Φq; simpl.
reflexivity.
Qed.

Theorem pt_absc_is_nat : ∀ pol pts pt,
  points_of_ps_polynom pol = pts
  → pt ∈ pts
    → fst pt = Qnat (Z.to_nat (Qnum (fst pt))).
Proof.
intros pol pts pt Hpts Hαh.
unfold points_of_ps_polynom, points_of_ps_lap in Hpts.
remember (al pol) as cl; clear Heqcl.
remember 0%nat as n in Hpts; clear Heqn.
unfold points_of_ps_lap_gen in Hpts.
unfold qpower_list in Hpts.
revert n pts Hpts Hαh.
induction cl as [| c]; intros; [ subst pts; contradiction | idtac ].
simpl in Hpts.
destruct cl as [| c₁].
 simpl in Hpts.
 destruct (order c); subst pts; [ idtac | contradiction ].
 simpl in Hαh.
 destruct Hαh as [Hαh| ]; [ idtac | contradiction ].
 subst pt; simpl.
 rewrite Nat2Z.id; reflexivity.

 simpl in Hpts.
 simpl in IHcl.
 destruct (order c).
  subst pts.
  destruct Hαh as [Hαh| Hαh].
   subst pt; simpl.
   rewrite Nat2Z.id; reflexivity.

   eapply IHcl; [ reflexivity | eassumption ].

  eapply IHcl; eassumption.
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
destruct c; simpl in Hpt.
 destruct Hpt as [Hpt| Hpt].
  subst pt; left; reflexivity.

  right; subst ms₃; apply IHpts; assumption.

 contradiction.

 right; subst ms₃; apply IHpts; assumption.
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

Theorem oth_pts_in_init_pts : ∀ pts ns pt,
  lower_convex_hull_points pts = Some ns
  → pt ∈ oth_pts ns
    → pt ∈ pts.
Proof.
intros pts ns pt Hns Hpt.
eapply hull_seg_edge_in_init_pts; try eassumption; reflexivity.
Qed.

Theorem ini_fin_ns_in_init_pts : ∀ pts ns,
  lower_convex_hull_points pts = Some ns
  → ini_pt ns ∈ pts ∧ fin_pt ns ∈ pts.
Proof.
intros pts ns Hns.
eapply hull_seg_vert_in_init_pts; try eassumption; reflexivity.
Qed.

Theorem ns_in_init_pts : ∀ pts ns pt,
  lower_convex_hull_points pts = Some ns
  → pt ∈ [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → pt ∈ pts.
Proof.
intros pts ns pt Hns Hpt.
destruct Hpt as [Hpt| Hpt].
 subst pt.
 apply ini_fin_ns_in_init_pts; assumption.

 apply List.in_app_or in Hpt.
 destruct Hpt as [Hpt| Hpt].
  eapply oth_pts_in_init_pts; eassumption.

  destruct Hpt as [Hpt| ]; [ idtac | contradiction ].
  subst pt.
  apply ini_fin_ns_in_init_pts; assumption.
Qed.

Theorem pt₁_bef_seg : ∀ pt₁ pt₂ pts pth,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → pth ∈ oth_pts (minimise_slope pt₁ pt₂ pts)
    → fst pt₁ < fst pth.
Proof.
intros pt₁ pt₂ pts pth Hsort Hh.
revert pt₁ pt₂ pth Hsort Hh.
induction pts as [| pt₃]; intros; [ contradiction | idtac ].
simpl in Hh.
remember (minimise_slope pt₁ pt₃ pts) as ms₃.
remember (slope_expr pt₁ pt₂ ?= slope ms₃) as c.
symmetry in Heqc.
destruct c.
 simpl in Hh.
 destruct Hh as [Hh| Hh].
  subst pth.
  eapply Sorted_hd; [ eassumption | left; reflexivity ].

  subst ms₃.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 contradiction.

 subst ms₃.
 eapply IHpts; [ idtac | eassumption ].
 eapply Sorted_minus_2nd; [ idtac | eassumption ].
 intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Theorem vert_bef_edge : ∀ pts hs j αj h αh,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some hs
    → (j, αj) = ini_pt hs
      → (h, αh) ∈ oth_pts hs
        → j < h.
Proof.
intros pts hs j αj h αh Hsort Hnp Hj Hh.
destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros Hhsl; subst hs.
simpl in Hj, Hh.
rewrite minimised_slope_beg_pt in Hj.
apply pt₁_bef_seg in Hh; [ subst pt₁; assumption | assumption ].
Qed.

Theorem jq_lt_hq : ∀ (pol : puis_ser_pol α) j αj h αh ns,
  newton_segments pol = Some ns
  → (j, αj) = ini_pt ns
    → (h, αh) ∈ oth_pts ns
      → j < h.
Proof.
intros pol j αj h αh ns Hns Hjαj Hhαh.
unfold newton_segments in Hns.
remember (points_of_ps_polynom pol) as pts.
apply points_of_polyn_sorted in Heqpts.
eapply vert_bef_edge; eassumption.
Qed.

Theorem j_lt_h : ∀ (pol : puis_ser_pol α) j αj jq h αh hq ns,
  newton_segments pol = Some ns
  → (jq, αj) = ini_pt ns
    → (hq, αh) ∈ oth_pts ns
      → jq = Qnat j
        → hq = Qnat h
          → (j < h)%nat.
Proof.
intros pol j αj jq h αh hq ns Hns Hj Hh Hjq Hhq.
eapply jq_lt_hq in Hh; try eassumption.
rewrite Hjq, Hhq in Hh.
apply Qnat_lt; assumption.
Qed.

Theorem seg_bef_end_pt : ∀ pt₁ pt₂ pts ms₁ hq αh kq αk,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → (hq, αh) ∈ oth_pts ms₁
      → (kq, αk) = fin_pt ms₁
        → hq < kq.
Proof.
fix IHpts 3.
intros pt₁ pt₂ pts ms₁ hq αh kq αk Hsort Hms₁ Hseg Hend.
destruct pts as [| pt₃]; [ subst ms₁; contradiction | idtac ].
simpl in Hms₁.
remember (minimise_slope pt₁ pt₃ pts) as ms₂.
symmetry in Heqms₂.
remember (slope_expr pt₁ pt₂ ?= slope ms₂) as c.
symmetry in Heqc.
destruct c.
 subst ms₁; simpl in Hseg, Hend.
 destruct Hseg as [Hseg| Hseg].
  apply Sorted_inv_1 in Hsort.
  apply Sorted_hd with (pt₂ := (kq, αk)) in Hsort.
   subst pt₂; assumption.

   rewrite Hend.
   eapply end_pt_in; eassumption.

  eapply IHpts with (pts := pts); try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 subst ms₁; simpl in Hseg, Hend; contradiction.

 subst ms₁; simpl in Hseg, Hend.
 eapply IHpts with (pts := pts); try eassumption.
 eapply Sorted_minus_2nd; [ idtac | eassumption ].
 intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Theorem hq_lt_kq : ∀ (pol : puis_ser_pol α) hq αh kq αk ns,
  newton_segments pol = Some ns
  → (hq, αh) ∈ oth_pts ns
    → (kq, αk) = fin_pt ns
      → hq < kq.
Proof.
intros pol hq αh kq αk ns Hns Hoth Hfin.
unfold newton_segments in Hns.
remember (points_of_ps_polynom pol) as pts.
apply points_of_polyn_sorted in Heqpts.
unfold lower_convex_hull_points in Hns.
destruct pts as [| pt₁]; [ discriminate Hns | idtac ].
destruct pts as [| pt₂]; [ discriminate Hns | idtac ].
injection Hns; clear Hns; intros Hns; subst ns.
simpl in Hoth, Hfin.
eapply seg_bef_end_pt; try eassumption; reflexivity.
Qed.

Theorem j_lt_k : ∀ (pol : puis_ser_pol α) j k ns,
  newton_segments pol = Some ns
  → j = nat_num (fst (ini_pt ns))
    → k = nat_num (fst (fin_pt ns))
      → (j < k)%nat.
Proof.
intros pol j k ns Hns Hj Hk.
unfold newton_segments in Hns.
remember (points_of_ps_polynom pol) as pts.
remember Heqpts as Hj₁; clear HeqHj₁; symmetry in Hj₁.
eapply pt_absc_is_nat with (pt := ini_pt ns) in Hj₁.
 remember Heqpts as Hk₁; clear HeqHk₁; symmetry in Hk₁.
 eapply pt_absc_is_nat with (pt := fin_pt ns) in Hk₁.
  apply points_of_polyn_sorted in Heqpts.
  assert (fst (ini_pt ns) < fst (fin_pt ns)).
   eapply ini_lt_fin_pt; eassumption.

   rewrite Hj₁, Hk₁ in H.
   apply Qnat_lt in H.
   subst j k; assumption.

  apply ini_fin_ns_in_init_pts; assumption.

 apply ini_fin_ns_in_init_pts; assumption.
Qed.

Theorem jz_lt_kz : ∀ (pol : puis_ser_pol α) jz kz ns,
  newton_segments pol = Some ns
  → jz = Qnum (fst (ini_pt ns))
    → kz = Qnum (fst (fin_pt ns))
      → (jz < kz)%Z.
Proof.
intros pol jz kz ns Hns Hjz Hkz.
remember Hns as H; clear HeqH.
eapply j_lt_k in H; try reflexivity.
remember (ini_pt ns) as jaj.
destruct jaj as (j, aj).
remember (fin_pt ns) as kak.
destruct kak as (k, ak).
simpl in Hjz, Hkz, H.
subst jz kz.
unfold nat_num in Hns.
apply Z2Nat.inj_lt; [ idtac | idtac | assumption ].
 unfold newton_segments in Hns.
 remember (points_of_ps_polynom pol) as pts.
 symmetry in Heqpts.
 remember Heqpts as Hpts; clear HeqHpts.
 apply pt_absc_is_nat with (pt := (j, aj)) in Hpts.
  simpl in Hpts; rewrite Hpts.
  apply Zle_0_nat.

  rewrite Heqjaj.
  apply ini_fin_ns_in_init_pts; assumption.

 unfold newton_segments in Hns.
 remember (points_of_ps_polynom pol) as pts.
 symmetry in Heqpts.
 remember Heqpts as Hpts; clear HeqHpts.
 apply pt_absc_is_nat with (pt := (k, ak)) in Hpts.
  simpl in Hpts; rewrite Hpts.
  apply Zle_0_nat.

  rewrite Heqkak.
  apply ini_fin_ns_in_init_pts; assumption.
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
Theorem gamma_value_jk : ∀ ns j k αj αk,
  (j, αj) = ini_pt ns
  → (k, αk) = fin_pt ns
  → γ ns = (αj - αk) / (k - j).
Proof.
intros ns j k αj αk Hjαj Hkαk.
unfold γ; simpl.
rewrite <- Hjαj, <- Hkαk; reflexivity.
Qed.

Theorem first_power_le : ∀ pow cl h hv,
  (h, hv) ∈ filter_finite_ord (qpower_list pow cl)
  → pow ≤ Z.to_nat (Qnum h).
Proof.
intros pow cl h hv Hhhv.
unfold qpower_list in Hhhv.
revert pow Hhhv.
induction cl as [| c]; intros; [ contradiction | idtac ].
simpl in Hhhv.
destruct cl as [| c₁].
 simpl in Hhhv.
 destruct (order c); [ idtac | contradiction ].
 destruct Hhhv as [Hhhv| ]; [ idtac | contradiction ].
 injection Hhhv; clear Hhhv; intros; subst h hv.
 simpl.
 rewrite Nat2Z.id; reflexivity.

 simpl in Hhhv.
 simpl in IHcl.
 destruct (order c).
  destruct Hhhv as [Hhhv| Hhhv].
   injection Hhhv; clear Hhhv; intros; subst h hv.
   simpl; rewrite Nat2Z.id; reflexivity.

   apply IHcl in Hhhv.
   transitivity (S pow); [ apply Nat.le_succ_r | assumption ].
   left; reflexivity.

  apply IHcl in Hhhv.
  transitivity (S pow); [ apply Nat.le_succ_r | assumption ].
  left; reflexivity.
Qed.

Theorem in_pts_in_ppl : ∀ pow cl ppl pts h hv hps def,
  ppl = qpower_list pow cl
  → pts = filter_finite_ord ppl
    → (h, hv) ∈ pts
      → hps = List.nth (Z.to_nat (Qnum h) - pow) cl def
        → (h, hps) ∈ ppl ∧ order hps = qfin hv.
Proof.
intros pow cl ppl pts h hv hps def Hppl Hpts Hhhv Hhps.
subst ppl pts.
destruct cl as [| c₁]; intros; [ contradiction | idtac ].
revert pow c₁ h hv hps Hhps Hhhv.
induction cl as [| c]; intros.
 simpl in Hhhv.
 remember (order c₁) as v.
 symmetry in Heqv.
 destruct v as [v| ]; [ idtac | contradiction ].
 destruct Hhhv as [Hhhv| ]; [ idtac | contradiction ].
 injection Hhhv; clear Hhhv; intros; subst v h.
 remember (Qnum (Qnat pow)) as x; simpl in Heqx; subst x.
 rewrite Nat2Z.id, minus_diag in Hhps.
 simpl in Hhps; subst hps.
 split; [ left; reflexivity | assumption ].

 remember [c … cl] as ccl; simpl in Hhhv; subst ccl.
 remember (order c₁) as v.
 symmetry in Heqv.
 destruct v as [v| ].
  destruct Hhhv as [Hhhv| Hhhv].
   injection Hhhv; clear Hhhv; intros; subst v h.
   remember (Qnum (Qnat pow)) as x; simpl in Heqx; subst x.
   rewrite Nat2Z.id, minus_diag in Hhps.
   simpl in Hhps; subst hps.
   split; [ left; reflexivity | assumption ].

   destruct (le_dec (S pow) (Z.to_nat (Qnum h))) as [Hle| Hgt].
    eapply IHcl in Hhhv.
     rewrite <- Nat.sub_succ in Hhps.
     rewrite <- minus_Sn_m in Hhps; [ idtac | assumption ].
     simpl in Hhps.
     destruct Hhhv as (Hhhv, Hhv).
     split; [ right; eassumption | assumption ].

     rewrite <- Nat.sub_succ in Hhps.
     rewrite <- minus_Sn_m in Hhps; [ idtac | assumption ].
     simpl in Hhps; eassumption.

    apply first_power_le in Hhhv; contradiction.

  destruct (le_dec (S pow) (Z.to_nat (Qnum h))) as [Hle| Hgt].
   eapply IHcl in Hhhv.
    rewrite <- Nat.sub_succ in Hhps.
    rewrite <- minus_Sn_m in Hhps; [ idtac | assumption ].
    simpl in Hhps.
    destruct Hhhv as (Hhhv, Hhv).
    split; [ right; eassumption | assumption ].

    rewrite <- Nat.sub_succ in Hhps.
    rewrite <- minus_Sn_m in Hhps; [ idtac | assumption ].
    simpl in Hhps; eassumption.

   apply first_power_le in Hhhv; contradiction.
Qed.

Theorem in_pts_in_psl : ∀ pow pts psl h hv hps def,
  pts = filter_finite_ord (qpower_list pow psl)
  → (h, hv) ∈ pts
    → hps = List.nth (Z.to_nat (Qnum h) - pow) psl def
      → hps ∈ psl ∧ order hps = qfin hv.
Proof.
intros pow pts psl h hv hps def Hpts Hhv Hhps.
remember (power_list pow psl) as ppl.
assert (pow ≤ Z.to_nat (Qnum h)) as H.
 subst pts ppl.
 eapply first_power_le; eassumption.

 eapply in_pts_in_ppl in Hhv; try eassumption; [ idtac | reflexivity ].
 destruct Hhv as (Hhps₁, Hv).
 split; [ idtac | assumption ].
 subst ppl.
 destruct psl as [| ps₁]; [ contradiction | idtac ].
 revert pow pts ps₁ h hv hps Hhps Hv Hhps₁ Hpts H.
 induction psl as [| ps]; intros.
  destruct Hhps₁ as [Hhps₁| ]; [ idtac | contradiction ].
  injection Hhps₁; clear Hhps₁; intros; subst h hps.
  now left.

  destruct Hhps₁ as [Hhps₁| Hhps₁].
   injection Hhps₁; clear Hhps₁; intros; subst h hps.
   now left.

   destruct (eq_nat_dec (Z.to_nat (Qnum h)) pow) as [Heq| Hne].
    rewrite Heq, minus_diag in Hhps.
    subst hps; left; reflexivity.

    right.
    eapply IHpsl; try eassumption; try reflexivity.
     rewrite <- Nat.sub_succ in Hhps.
     rewrite <- minus_Sn_m in Hhps; [ assumption | idtac ].
     apply not_eq_sym in Hne.
     apply Nat_le_neq_lt; assumption.

     apply not_eq_sym in Hne.
     apply Nat_le_neq_lt; assumption.
Qed.

Theorem in_pts_in_pol : ∀ pol pts h hv hps def,
  pts = points_of_ps_polynom pol
  → (Qnat h, hv) ∈ pts
    → hps = List.nth h (al pol) def
      → hps ∈ al pol ∧ order hps = qfin hv.
Proof.
intros pol pts h hv hps def Hpts Hhhv Hhps.
eapply in_pts_in_psl; try eassumption.
simpl; rewrite Nat.sub_0_r, Nat2Z.id; eassumption.
Qed.

Theorem in_ppl_in_pts : ∀ pow cl ppl pts h hv hps,
  ppl = qpower_list pow cl
  → pts = filter_finite_ord ppl
    → pow ≤ h
      → hps = List.nth (h - pow) cl 0%ps
        → order hps = qfin hv
          → (Qnat h, hv) ∈ pts.
Proof.
(* peut-être améliorable, simplifiable ; voir pourquoi cas cl=[] est à part ;
   et voir les deux cas de h - pow plus bas *)
intros pow cl ppl pts h hv hps Hppl Hpts Hph Hhhv Hhps.
subst ppl pts.
destruct cl as [| c₁]; intros; simpl.
 rewrite list_nth_nil in Hhhv.
 assert (order hps = qinf) as H.
  apply order_inf.
  subst hps; reflexivity.

  rewrite Hhps in H; discriminate H.

 unfold qpower_list.
 revert pow c₁ h hv hps Hhps Hhhv Hph.
 induction cl as [| c]; intros.
  simpl in Hhhv.
  remember (h - pow)%nat as hp eqn:Hhp .
  symmetry in Hhp.
  destruct hp.
   subst c₁; simpl.
   rewrite Hhps.
   apply Nat.sub_0_le in Hhp.
   apply Nat.le_antisymm in Hhp; [ idtac | assumption ].
   subst pow; left; reflexivity.

   rewrite match_id in Hhhv.
   assert (order hps = qinf) as H.
    apply order_inf.
    subst hps; reflexivity.

    rewrite Hhps in H; discriminate H.

  remember [c … cl] as x; simpl; subst x.
  remember [c … cl] as x; simpl; subst x.
  remember (order c₁) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ].
   simpl in Hhhv.
   remember (h - pow)%nat as hp eqn:Hhp .
   symmetry in Hhp.
   destruct hp.
    subst c₁.
    apply Nat.sub_0_le in Hhp.
    apply Nat.le_antisymm in Hph; [ idtac | assumption ].
    subst pow.
    rewrite Hhps in Hn; injection Hn; intros; subst n.
    left; reflexivity.

    right.
    destruct hp.
     subst hps.
     apply Nat.add_sub_eq_nz in Hhp; [ idtac | intros H; discriminate H ].
     rewrite Nat.add_1_r in Hhp.
     eapply IHcl; try eassumption.
      rewrite Hhp, Nat.sub_diag; reflexivity.

      rewrite Hhp; reflexivity.

     apply Nat.add_sub_eq_nz in Hhp; [ idtac | intros H; discriminate H ].
     rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hhp.
     eapply IHcl; try eassumption.
      erewrite <- Hhp.
      rewrite Nat.add_comm, Nat.add_sub; assumption.

      rewrite <- Hhp.
      apply le_plus_l.

   destruct (eq_nat_dec h pow) as [Hhp| Hhp].
    subst pow.
    rewrite Nat.sub_diag in Hhhv.
    simpl in Hhhv.
    subst c₁.
    rewrite Hhps in Hn; discriminate Hn.

    eapply IHcl; try eassumption.
     destruct h.
      simpl in Hhhv; simpl.
      subst hps.
      rewrite Hhps in Hn; discriminate Hn.

      rewrite Nat.sub_succ_l in Hhhv.
       rewrite Nat.sub_succ; assumption.

       apply Nat.neq_sym in Hhp.
       apply Nat_le_neq_lt in Hhp; [ idtac | assumption ].
       apply le_S_n; assumption.

     apply Nat.neq_sym in Hhp.
     apply Nat_le_neq_lt in Hhp; [ idtac | assumption ].
     assumption.
Qed.

Theorem in_pol_in_pts : ∀ pol pts h hv hps,
  pts = points_of_ps_polynom pol
  → hps = List.nth h (al pol) 0%ps
    → order hps = qfin hv
      → (Qnat h, hv) ∈ pts.
Proof.
intros pol pts h hv hps Hpts Hhps Hv.
eapply in_ppl_in_pts; try eassumption; try reflexivity.
 apply Nat.le_0_l.

 rewrite Nat.sub_0_r; assumption.
Qed.

Theorem exists_ini_pt_nat : ∀ pol ns,
  newton_segments pol = Some ns
  → ∃ i αi, ini_pt ns = (Qnat i, αi).
Proof.
intros pol ns Hns.
remember (ini_pt ns) as ii.
destruct ii as ((inum, iden), αi).
exists (Z.to_nat inum), αi.
unfold newton_segments in Hns.
remember (points_of_ps_polynom pol) as pts.
symmetry in Heqpts.
apply ini_fin_ns_in_init_pts in Hns.
destruct Hns as (Hns, _).
eapply pt_absc_is_nat in Heqpts; [ idtac | eassumption ].
rewrite <- Heqii in Heqpts; simpl in Heqpts.
rewrite Heqpts; reflexivity.
Qed.

Theorem exists_fin_pt_nat : ∀ pol ns,
  newton_segments pol = Some ns
  → ∃ i αi, fin_pt ns = (Qnat i, αi).
Proof.
intros pol ns Hns.
remember (fin_pt ns) as ii.
destruct ii as ((inum, iden), αi).
exists (Z.to_nat inum), αi.
unfold newton_segments in Hns.
remember (points_of_ps_polynom pol) as pts.
symmetry in Heqpts.
apply ini_fin_ns_in_init_pts in Hns.
destruct Hns as (_, Hns).
eapply pt_absc_is_nat in Heqpts; [ idtac | eassumption ].
rewrite <- Heqii in Heqpts; simpl in Heqpts.
rewrite Heqpts; reflexivity.
Qed.

Theorem exists_oth_pt_nat : ∀ pol ns pt,
  newton_segments pol = Some ns
  → pt ∈ oth_pts ns
    → ∃ h αh, pt = (Qnat h, αh).
Proof.
intros pol ns pt Hns Hpt.
destruct pt as ((inum, iden), αi).
exists (Z.to_nat inum), αi.
unfold newton_segments in Hns.
remember (points_of_ps_polynom pol) as pts.
symmetry in Heqpts.
eapply oth_pts_in_init_pts in Hns; [ idtac | eassumption ].
eapply pt_absc_is_nat in Heqpts; [ idtac | eassumption ].
simpl in Heqpts.
rewrite Heqpts; reflexivity.
Qed.

Theorem points_in_newton_segment_have_nat_abscissa : ∀ pol ns,
  newton_segments pol = Some ns
  → ∀ pt, pt ∈ [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → ∃ h αh, pt = (Qnat h, αh).
Proof.
intros pol ns Hns pt Hpt.
destruct Hpt as [H| H].
 rewrite <- H.
 eapply exists_ini_pt_nat; eassumption.

 apply List.in_app_or in H.
 destruct H as [H| H].
  eapply exists_oth_pt_nat; eassumption.

  destruct H as [H| ]; [ idtac | contradiction ].
  rewrite <- H.
  eapply exists_fin_pt_nat; eassumption.
Qed.

(* [Walker, p. 100]: «
                        p
          γ₁ = [...] = ---
                       m q
  » *)
Theorem any_is_p_mq : ∀ a m p q,
  p = p_of_m m a
  → q = q_of_m m a
  → a == p # (m * q) ∧ Z.gcd p ('q) = 1%Z.
Proof.
intros a m p q Hp Hq.
unfold Qeq; simpl.
subst p q; simpl.
unfold p_of_m, q_of_m; simpl.
remember (Qnum a * ' m)%Z as p.
remember (Qden a) as q.
remember (Z.gcd p (' q)) as g.
rewrite Pos2Z.inj_mul.
rewrite Z.mul_assoc.
rewrite <- Heqp.
pose proof (Z.gcd_divide_l p (' q)).
rewrite <- Heqg in H.
destruct H as (gp, Hgp).
rewrite Hgp.
assert (g ≠ 0)%Z as Hg0.
 intros H.
 rewrite Heqg in H.
 apply Z.gcd_eq_0_r in H; revert H; apply Pos2Z_ne_0.

 rewrite Z.div_mul; auto.
 pose proof (Z.gcd_divide_r p (' q)).
 rewrite <- Heqg in H.
 destruct H as (gq, Hgq).
 rewrite Hgq.
 rewrite Z.div_mul; auto.
 rewrite Z.mul_shuffle0, Z.mul_assoc.
 rewrite Z2Pos.id.
  split; [ reflexivity | idtac ].
  apply Z.gcd_div_gcd in Heqg; auto.
  rewrite Hgp, Hgq in Heqg.
  rewrite Z.div_mul in Heqg; auto.
  rewrite Z.div_mul in Heqg; auto.

  apply Z.mul_lt_mono_pos_r with (p := g).
   symmetry in Heqg.
   destruct g as [| g| g].
    rewrite Z.mul_0_r in Hgq.
    exfalso; revert Hgq; apply Pos2Z_ne_0.

    apply Pos2Z.is_pos.

    pose proof (Z.gcd_nonneg p (' q)).
    rewrite Heqg in H.
    apply Z.nlt_ge in H.
    exfalso; apply H.
    apply Pos2Z.neg_is_neg.

   simpl.
   rewrite <- Hgq; apply Pos2Z.is_pos.
Qed.

(* [Walker, p. 100]: « [...] where q > 0 and p and q are integers having
   no common factor. » *)
Theorem p_and_q_have_no_common_factors : ∀ a m p q,
  p = p_of_m m a
  → q = q_of_m m a
  → Z.gcd p (' q) = 1%Z.
Proof.
intros a m p q Hp Hq.
eapply any_is_p_mq; eauto .
Qed.

(* [Walker, p. 100]: « If Ph is on L, then also
                   αj - αh
      [...] = γ₁ = ------- = [...]
                    h - j
   » *)
Theorem gamma_value_jh : ∀ pol ns j αj,
  newton_segments pol = Some ns
  → (j, αj) = ini_pt ns
    → ∀ h αh, (h, αh) ∈ oth_pts ns
      → γ ns == (αj - αh) / (h - j).
Proof.
intros pol ns j αj Hns Hjαj h αh Hhαh.
remember Hns as Hh; clear HeqHh.
apply points_in_any_newton_segment with (h := h) (αh := αh) in Hh.
 apply Qeq_plus_minus_eq_r in Hh.
 remember Hns as Haj; clear HeqHaj.
 apply points_in_any_newton_segment with (h := j) (αh := αj) in Haj.
  rewrite <- Hh, Haj.
  field.
  apply Qlt_not_0.
  eapply jq_lt_hq; try eassumption.

  left; rewrite Hjαj; reflexivity.

 right; right; assumption.
Qed.

Open Scope Z_scope.

Theorem pmq_qmpm : ∀ m p q j k jz kz mj mk,
  (j < k)%nat
  → jz = Z.of_nat j
    → kz = Z.of_nat k
      → p # m * q == (mj - mk # m) / (kz - jz # 1)
        → ' q * (mj - mk) = p * (kz - jz).
Proof.
intros m p q j k jz kz mj mk Hjk Hjz Hkz Hpq.
subst jz kz.
unfold Qeq in Hpq; simpl in Hpq.
do 2 rewrite Pos2Z.inj_mul in Hpq.
rewrite Zmult_comm in Hpq; symmetry in Hpq.
rewrite Zmult_comm in Hpq; symmetry in Hpq.
do 2 rewrite <- Zmult_assoc in Hpq.
apply Z.mul_cancel_l in Hpq; [ idtac | apply Pos2Z_ne_0 ].
rewrite Zmult_assoc, Zmult_comm in Hpq.
rewrite Qden_inv in Hpq.
 rewrite Qnum_inv in Hpq.
  symmetry in Hpq.
  rewrite Zmult_comm in Hpq.
  symmetry in Hpq.
  apply Z.div_unique_exact in Hpq; [ idtac | apply Pos2Z_ne_0 ].
  rewrite Hpq.
  rewrite Znumtheory.Zdivide_Zdiv_eq_2.
   rewrite Zdiv_1_r; reflexivity.

   apply Pos2Z.is_pos.

   apply Z.divide_1_l.

  apply Z.lt_0_sub, inj_lt; assumption.

 apply Z.lt_0_sub, inj_lt; assumption.
Qed.

Theorem order_in_newton_segment : ∀ pol ns pl h αh,
  newton_segments pol = Some ns
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → (Qnat h, αh) ∈ pl
      → order (ps_poly_nth h pol) = qfin αh.
Proof.
intros pol ns pl h αh Hns Hpl Hαh.
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
unfold ps_poly_nth, ps_lap_nth; simpl.
edestruct in_pts_in_pol; try reflexivity; try eassumption.
subst pl.
simpl in Hαh.
destruct Hαh as [Hαh| Hαh].
 rewrite Hini in Hαh.
 injection Hαh; clear Hαh; intros HH H; subst αh.
 apply Nat2Z.inj in H; subst h.
 rewrite <- Hini.
 apply ini_fin_ns_in_init_pts; assumption.

 apply List.in_app_or in Hαh.
 destruct Hαh as [Hαh| Hαh].
  eapply oth_pts_in_init_pts; try reflexivity; try eassumption.

  destruct Hαh as [Hαh| Hαh]; [ idtac | contradiction ].
  rewrite Hfin in Hαh.
  injection Hαh; clear Hαh; intros HH H; subst αh.
  apply Nat2Z.inj in H; subst h.
  rewrite <- Hfin.
  apply ini_fin_ns_in_init_pts; assumption.
Qed.

Theorem qden_αj_is_ps_polord : ∀ pol ns j αj,
  newton_segments pol = Some ns
  → (Qnat j, αj) = ini_pt ns
  → Qden αj = ps_polord (ps_poly_nth j pol).
Proof.
intros pol ns j αj Hns Hini.
remember Hns as H; clear HeqH.
eapply order_in_newton_segment in H; eauto ; [ idtac | left; eauto  ].
unfold order in H.
remember (ps_poly_nth j pol) as ps.
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
unfold order in Ho.
remember (series_order (ps_terms ps) 0) as x.
symmetry in Heqx.
destruct x as [x| ]; [ idtac | discriminate Ho ].
injection Ho; clear Ho; intros Ho.
inversion_clear Hin.
destruct H as (ps₁, (Hps, Hm)).
subst v m.
unfold Qeq; simpl.
inversion_clear Hps.
inversion_clear H.
clear H2.
unfold normalise_ps in H0, H1; simpl in H0, H1.
rewrite Heqx in H0, H1; simpl in H0, H1.
remember (series_order (ps_terms ps₁) 0) as y.
symmetry in Heqy.
destruct y as [y| ]; simpl in H0, H1.
 remember (greatest_series_x_power K (ps_terms ps₁) y) as z₁.
 remember (greatest_series_x_power K (ps_terms ps) x) as z.
 remember (gcd_ps x z ps) as g.
 remember (gcd_ps y z₁ ps₁) as g₁.
 remember (ps_ordnum ps₁ + Z.of_nat y)%Z as p₁.
 remember (ps_ordnum ps + Z.of_nat x)%Z as p.
 remember (' ps_polord ps₁)%Z as o₁.
 remember (' ps_polord ps)%Z as o.
 exists p₁.
 pose proof (gcd_ps_is_pos x z ps) as Hgp.
 pose proof (gcd_ps_is_pos y z₁ ps₁) as Hgp₁.
 unfold gcd_ps in Heqg, Heqg₁, Hgp, Hgp₁.
 rewrite <- Heqp, <- Heqo in Heqg, Hgp.
 rewrite <- Heqp₁, <- Heqo₁ in Heqg₁, Hgp₁.
 subst g g₁.
 rewrite <- Z.gcd_assoc in H0.
 remember (Z.of_nat z₁) as t₁.
 remember (Z.of_nat z) as t.
 pose proof (Z.gcd_divide_l p₁ (Z.gcd o₁ t₁)) as H₁.
 destruct H₁ as (c₁, Hc₁).
 rewrite Hc₁ in H0 at 1.
 rewrite Z.div_mul in H0.
  rewrite <- Z.gcd_assoc in H0.
  pose proof (Z.gcd_divide_l p (Z.gcd o t)) as H.
  destruct H as (c, Hc).
  rewrite Hc in H0 at 1.
  rewrite Z.div_mul in H0.
   subst c₁.
   rewrite Z.gcd_comm, Z.gcd_assoc in H1.
   pose proof (Z.gcd_divide_r (Z.gcd t₁ p₁) o₁) as H₁.
   destruct H₁ as (d₁, Hd₁).
   rewrite Hd₁ in H1 at 1.
   rewrite Z.div_mul in H1.
    rewrite Z.gcd_comm, Z.gcd_assoc in H1.
    pose proof (Z.gcd_divide_r (Z.gcd t p) o) as H.
    destruct H as (d, Hd).
    rewrite Hd in H1 at 1.
    rewrite Z.div_mul in H1.
     apply Z2Pos.inj in H1.
      subst d₁.
      rewrite <- Z.gcd_assoc, Z.gcd_comm, <- Z.gcd_assoc in Hd.
      rewrite <- Z.gcd_assoc, Z.gcd_comm, <- Z.gcd_assoc in Hd₁.
      remember (Z.gcd p (Z.gcd o t)) as g.
      remember (Z.gcd p₁ (Z.gcd o₁ t₁)) as g₁.
      rewrite Hc, Hc₁, Hd, Hd₁.
      ring.

      apply Zmult_gt_0_lt_0_reg_r with (n := Z.gcd (Z.gcd t₁ p₁) o₁).
       rewrite <- Z.gcd_assoc, Z.gcd_comm.
       apply Z.lt_gt; assumption.

       rewrite <- Hd₁, Heqo₁; apply Pos2Z.is_pos.

      apply Zmult_gt_0_lt_0_reg_r with (n := Z.gcd (Z.gcd t p) o).
       rewrite <- Z.gcd_assoc, Z.gcd_comm.
       apply Z.lt_gt; assumption.

       rewrite <- Hd, Heqo; apply Pos2Z.is_pos.

     apply Z.neq_sym.
     apply Z.lt_neq.
     rewrite <- Z.gcd_assoc, Z.gcd_comm.
     assumption.

    apply Z.neq_sym.
    apply Z.lt_neq.
    rewrite <- Z.gcd_assoc, Z.gcd_comm.
    assumption.

   apply Z.neq_sym.
   apply Z.lt_neq.
   rewrite Z.gcd_assoc.
   assumption.

  apply Z.neq_sym.
  apply Z.lt_neq.
  rewrite Z.gcd_assoc.
  assumption.

 remember (greatest_series_x_power K (ps_terms ps) x) as z.
 pose proof (gcd_ps_is_pos x z ps) as Hgp.
 unfold gcd_ps in H0.
 remember (ps_ordnum ps + Z.of_nat x)%Z as p.
 remember (' ps_polord ps)%Z as o.
 remember (Z.of_nat z) as t.
 pose proof (Z.gcd_divide_l p (Z.gcd o t)) as H.
 destruct H as (c, Hc).
 rewrite <- Z.gcd_assoc in H0.
 rewrite Hc in H0 at 1.
 rewrite Z.div_mul in H0.
  subst c; simpl in Hc.
  move Hc at top; subst p.
  exists 0%Z; reflexivity.

  unfold gcd_ps in Hgp.
  rewrite <- Heqp, <- Heqo, <- Heqt in Hgp.
  apply Z.neq_sym.
  apply Z.lt_neq.
  rewrite Z.gcd_assoc.
  assumption.
Qed.

Theorem any_in_K_1_m : ∀ la m h αh,
  ps_lap_forall (λ a, in_K_1_m a m) la
  → (Qnat h, αh) ∈ points_of_ps_lap la
  → ∃ mh, αh == mh # m.
Proof.
intros la m h αh HinK Hin.
unfold points_of_ps_lap in Hin.
unfold points_of_ps_lap_gen in Hin.
unfold qpower_list in Hin.
remember O as pow; clear Heqpow.
revert pow Hin.
induction la as [| a]; intros; [ contradiction | idtac ].
simpl in Hin.
inversion_clear HinK.
 apply lap_eq_cons_nil_inv in H.
 destruct H as (Ha, Hla); simpl in Ha.
 apply order_inf in Ha.
 rewrite Ha in Hin.
 eapply IHla; eauto .
 constructor; assumption.

 remember (order a) as v eqn:Hv .
 symmetry in Hv.
 destruct v as [v| ].
  simpl in Hin.
  destruct Hin as [Hin| Hin].
   injection Hin; clear Hin; intros; subst v.
   eapply in_K_1_m_order_eq; eauto .

   eapply IHla; eauto .

  eapply IHla; eauto .
Qed.

Theorem den_αj_divides_num_αj_m : ∀ pol ns j αj m,
  newton_segments pol = Some ns
  → ini_pt ns = (Qnat j, αj)
  → pol_in_K_1_m pol m
  → (' Qden αj | Qnum αj * ' m)%Z.
Proof.
intros pol ns j αj m Hns Hini HinK.
apply any_in_K_1_m with (h := j) (αh := αj) in HinK.
 destruct HinK as (mh, Hmh).
 exists mh; assumption.

 unfold newton_segments in Hns.
 unfold points_of_ps_polynom in Hns.
 apply ini_fin_ns_in_init_pts in Hns.
 destruct Hns; rewrite <- Hini; assumption.
Qed.

Theorem pol_ord_of_ini_pt : ∀ pol ns m j αj mj,
  newton_segments pol = Some ns
  → pol_in_K_1_m pol m
  → (Qnat j, αj) = ini_pt ns
  → mj = mh_of_m m αj (ps_poly_nth j pol)
  → αj == mj # m.
Proof.
intros pol ns m j αj mj Hns Hm Hini Hmj.
subst mj; simpl.
unfold mh_of_m; simpl.
unfold Qeq; simpl.
rewrite Z_div_mul_swap.
 erewrite qden_αj_is_ps_polord; eauto .
 rewrite Z.div_mul; eauto .

 erewrite <- qden_αj_is_ps_polord; eauto .
 eapply den_αj_divides_num_αj_m; eauto .
Qed.

Theorem qden_αk_is_ps_polord : ∀ pol ns k αk,
  newton_segments pol = Some ns
  → (Qnat k, αk) = fin_pt ns
  → Qden αk = ps_polord (ps_poly_nth k pol).
Proof.
intros pol ns k αk Hns Hfin.
remember Hns as H; clear HeqH.
eapply order_in_newton_segment with (h := k) (αh := αk) in H; eauto .
 unfold order in H.
 remember (ps_poly_nth k pol) as ps.
 remember (series_order (ps_terms ps) 0) as v eqn:Hv .
 symmetry in Hv.
 destruct v; [ idtac | discriminate H ].
 injection H; clear H; intros H.
 rewrite <- H; reflexivity.

 rewrite Hfin.
 rewrite List.app_comm_cons.
 apply List.in_or_app.
 right; left; reflexivity.
Qed.

Theorem den_αk_divides_num_αk_m : ∀ pol ns k αk m,
  newton_segments pol = Some ns
  → pol_in_K_1_m pol m
  → fin_pt ns = (Qnat k, αk)
  → (' Qden αk | Qnum αk * ' m)%Z.
Proof.
intros pol ns k αk m Hns HinK Hini.
apply any_in_K_1_m with (h := k) (αh := αk) in HinK.
 destruct HinK as (mh, Hmh).
 exists mh; assumption.

 unfold newton_segments in Hns.
 unfold points_of_ps_polynom in Hns.
 apply ini_fin_ns_in_init_pts in Hns.
 destruct Hns; rewrite <- Hini; assumption.
Qed.

Theorem pol_ord_of_fin_pt : ∀ pol ns m k αk mk,
  newton_segments pol = Some ns
  → pol_in_K_1_m pol m
  → (Qnat k, αk) = fin_pt ns
  → mk = mh_of_m m αk (ps_poly_nth k pol)
  → αk == mk # m.
Proof.
intros pol ns m k αk mk Hns Hm Hini Hmk.
subst mk; simpl.
unfold mh_of_m; simpl.
unfold Qeq; simpl.
rewrite Z_div_mul_swap.
 erewrite qden_αk_is_ps_polord; eauto .
 rewrite Z.div_mul; eauto .

 erewrite <- qden_αk_is_ps_polord; eauto .
 eapply den_αk_divides_num_αk_m; eauto .
Qed.

Theorem qden_αh_is_ps_polord : ∀ pol ns h αh,
  newton_segments pol = Some ns
  → (Qnat h, αh) ∈ oth_pts ns
  → Qden αh = ps_polord (ps_poly_nth h pol).
Proof.
intros pol ns h αh Hns Hoth.
remember Hns as H; clear HeqH.
eapply order_in_newton_segment with (h := h) (αh := αh) in H; eauto .
 unfold order in H.
 remember (ps_poly_nth h pol) as ps.
 remember (series_order (ps_terms ps) 0) as v eqn:Hv .
 symmetry in Hv.
 destruct v; [ idtac | discriminate H ].
 injection H; clear H; intros H.
 rewrite <- H; reflexivity.

 right.
 apply List.in_or_app.
 left; assumption.
Qed.

Theorem den_αh_divides_num_αh_m : ∀ pol ns h αh m,
  newton_segments pol = Some ns
  → pol_in_K_1_m pol m
  → (Qnat h, αh) ∈ oth_pts ns
  → (' Qden αh | Qnum αh * ' m)%Z.
Proof.
intros pol ns h αh m Hns HinK Hoth.
apply any_in_K_1_m with (h := h) (αh := αh) in HinK.
 destruct HinK as (mh, Hmh).
 exists mh; assumption.

 unfold newton_segments in Hns.
 unfold points_of_ps_polynom in Hns.
 eapply oth_pts_in_init_pts in Hns; eauto .
Qed.

Theorem pol_ord_of_oth_pt : ∀ pol ns m h αh mh,
  newton_segments pol = Some ns
  → pol_in_K_1_m pol m
  → (Qnat h, αh) ∈ oth_pts ns
  → mh = mh_of_m m αh (ps_poly_nth h pol)
  → αh == mh # m.
Proof.
intros pol ns m h αh mh Hns Hm Hfin Hmh.
subst mh; simpl.
unfold mh_of_m; simpl.
unfold Qeq; simpl.
rewrite Z_div_mul_swap.
 erewrite qden_αh_is_ps_polord; eauto .
 rewrite Z.div_mul; eauto .

 erewrite <- qden_αh_is_ps_polord; eauto .
 eapply den_αh_divides_num_αh_m; eauto .
Qed.

(* [Walker, p. 100]: « In the first place, we note that [...]

         q (mj - mh) = p (h - j)
   » *)
Theorem q_mj_mk_eq_p_h_j : ∀ pol ns j αj m mj p q,
  newton_segments pol = Some ns
  → pol_in_K_1_m pol m
  → (Qnat j, αj) = ini_pt ns
  → mj = mh_of_m m αj (ps_poly_nth j pol)
  → p = p_of_m m (γ ns)
  → q = Pos.to_nat (q_of_m m (γ ns))
  → ∀ h αh mh, (Qnat h, αh) ∈ oth_pts ns ++ [fin_pt ns]
  → mh = mh_of_m m αh (ps_poly_nth h pol)
  → αh == mh # m
    ∧ (Z.of_nat q * (mj - mh) = p * Z.of_nat (h - j))%Z.
Proof.
intros pol ns j αj m mj p q Hns Hm Hj Hmj Hp Hq h αh mh Hh Hmh.
remember (points_of_ps_polynom pol) as pts eqn:Hpts .
remember (ps_poly_nth h pol) as hps.
apply List.in_app_or in Hh.
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hfin)).
split.
 rewrite Hmh; simpl.
 unfold Qeq; simpl.
 unfold mh_of_m; simpl.
 subst hps.
 destruct Hh as [Hh| [Hk| ]]; [ idtac | idtac | contradiction ].
  erewrite <- qden_αh_is_ps_polord; eauto .
  rewrite Z_div_mul_swap.
   rewrite Z.div_mul; auto.

   eapply den_αh_divides_num_αh_m; eauto .

  erewrite <- qden_αk_is_ps_polord; eauto .
  rewrite Z_div_mul_swap.
   rewrite Z.div_mul; auto.

   eapply den_αk_divides_num_αk_m; eauto .

 destruct Hh as [Hh| [Hh| ]]; [ idtac | idtac | contradiction ].
  remember Hns as Hgh; clear HeqHgh.
  eapply gamma_value_jh in Hgh; try eassumption.
  remember (q_of_m m (γ ns)) as pq eqn:Hpq .
  pose proof (any_is_p_mq (γ ns) m Hp Hpq) as H.
  destruct H as (Hgamma, Hg).
  rewrite Hgamma in Hgh.
  unfold Qnat in Hgh.
  rewrite <- Qnum_minus_distr_r in Hgh.
  rewrite Nat2Z.inj_sub.
   rewrite Hq.
   rewrite positive_nat_Z.
   eapply pmq_qmpm; try reflexivity.
    eapply j_lt_h; try eassumption; reflexivity.

    rewrite Hgh.
    remember Heqhps as Hhps; clear HeqHhps.
    eapply in_pts_in_pol in Hhps; try eassumption.
     destruct Hhps as (Hhps, Hαh).
     do 2 rewrite Qnum_minus_distr_r.
     eapply pol_ord_of_ini_pt in Hj; try eassumption; rewrite Hj.
     eapply pol_ord_of_oth_pt in Hh; try eassumption.
      rewrite Hh; reflexivity.

      subst hps; assumption.

     eapply oth_pts_in_init_pts; try eassumption.
     unfold newton_segments in Hns.
     rewrite <- Hpts in Hns; assumption.

   apply Nat.lt_le_incl.
   eapply j_lt_h; try eassumption; reflexivity.

  remember Hj as Hgh; clear HeqHgh.
  symmetry in Hh.
  eapply gamma_value_jk in Hgh; [ idtac | eassumption ].
  remember (q_of_m m (γ ns)) as pq eqn:Hpq .
  pose proof (any_is_p_mq (γ ns) m Hp Hpq) as H.
  destruct H as (Hgamma, Hg).
  rewrite Hgh in Hgamma.
  unfold Qnat in Hgamma.
  rewrite <- Qnum_minus_distr_r in Hgamma.
  rewrite Nat2Z.inj_sub.
   rewrite Hq.
   rewrite positive_nat_Z.
   eapply pmq_qmpm; try reflexivity.
    eapply j_lt_k; try eassumption.
     rewrite <- Hj; simpl; rewrite nat_num_Qnat; reflexivity.

     rewrite <- Hh; simpl; rewrite nat_num_Qnat; reflexivity.

    rewrite <- Hgamma.
    remember Heqhps as Hhps; clear HeqHhps.
    eapply in_pts_in_pol with (hv := αh) in Hhps; try eassumption.
     destruct Hhps as (Hhps, Hαh).
     do 2 rewrite Qnum_minus_distr_r.
     eapply pol_ord_of_ini_pt in Hj; try eassumption; rewrite Hj.
     eapply pol_ord_of_fin_pt in Hh; try eassumption.
      rewrite Hh; reflexivity.

      subst hps; assumption.

     rewrite Hh.
     eapply ini_fin_ns_in_init_pts; try eassumption.
     unfold newton_segments in Hns.
     rewrite <- Hpts in Hns; assumption.

   apply Nat.lt_le_incl.
   eapply j_lt_k; try eassumption.
    rewrite <- Hj; simpl; rewrite nat_num_Qnat; reflexivity.

    rewrite <- Hh; simpl; rewrite nat_num_Qnat; reflexivity.
Qed.

Theorem mul_pos_nonneg : ∀ j k c d,
  (j < k)%nat
  → Z.of_nat (k - j) = c * Z.of_nat d
    → 0 <= c.
Proof.
intros j k c d Hjk Hc.
apply Z.mul_le_mono_pos_r with (p := Z.of_nat d).
 destruct d.
  rewrite Z.mul_comm in Hc; simpl in Hc.
  rewrite <- Nat2Z.inj_0 in Hc.
  apply Nat2Z.inj in Hc.
  apply Nat.sub_0_le in Hc.
  apply Nat.nlt_ge in Hc.
  exfalso; apply Hc.
  contradiction.

  apply Pos2Z.is_pos.

 rewrite <- Hc; simpl.
 apply Nat2Z.is_nonneg.
Qed.

(* [Walker, p. 100]: « In the first place, we note that [...]
   and since p and q have no common factors, q is a factor
   of h - j. » *)
Theorem q_is_factor_of_h_minus_j : ∀ pol ns j αj m q,
  newton_segments pol = Some ns
  → pol_in_K_1_m pol m
  → (Qnat j, αj) = ini_pt ns
  → q = Pos.to_nat (q_of_m m (γ ns))
  → ∀ h αh, (Qnat h, αh) ∈ oth_pts ns ++ [fin_pt ns]
  → (q | h - j)%nat.
Proof.
intros pol ns j αj m q Hns Hm Hj Hq h αh Hh.
remember (p_of_m m (γ ns)) as p eqn:Hp .
remember Hns as H; clear HeqH.
eapply q_mj_mk_eq_p_h_j in H; try eassumption; try reflexivity.
destruct H as (Hαh, Hqjh).
apply List.in_app_or in Hh.
remember (q_of_m m (γ ns)) as pq eqn:Hpq ; subst q.
rename pq into q; rename Hpq into Hq.
remember Hp as Hgcd; clear HeqHgcd.
eapply p_and_q_have_no_common_factors in Hgcd; eauto .
rewrite Z.gcd_comm in Hgcd.
rewrite <- positive_nat_Z in Hgcd.
rewrite Z.gcd_comm in Hgcd.
rewrite Z.gcd_comm in Hgcd.
apply Z.gauss with (p := Z.of_nat (h - j)) in Hgcd.
 destruct Hgcd as (c, Hc).
 exists (Z.to_nat c).
 apply Nat2Z.inj.
 rewrite Nat2Z.inj_mul.
 rewrite Z2Nat.id; [ assumption | idtac ].
 eapply mul_pos_nonneg; try eassumption.
 destruct Hh as [Hh| [Hk| ]]; [ idtac | idtac | contradiction ].
  eapply j_lt_h; try eassumption; reflexivity.

  eapply j_lt_k; try eassumption.
   rewrite <- Hj; simpl; rewrite nat_num_Qnat; reflexivity.

   rewrite Hk; simpl; rewrite nat_num_Qnat; reflexivity.

 rewrite <- Hqjh.
 apply Z.divide_factor_l.
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
induction pts as [| pt₄]; intros.
 subst ms₂; constructor.

 simpl in Hms₂.
 remember (minimise_slope pt₁ pt₄ pts) as ms₄.
 symmetry in Heqms₄.
 remember (slope_expr pt₁ pt₃ ?= slope ms₄)%Q as c.
 symmetry in Heqc.
 destruct c.
  subst ms₂; simpl.
  constructor.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort as (_, Hsort).
  apply Sorted_inv_2 in Hsort.
  destruct Hsort; assumption.

  subst ms₂; constructor.

  move Hms₂ at top; subst ms₄.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_3rd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Theorem minimise_slope_seg_sorted : ∀ pt₁ pt₂ pts ms₁,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → Sorted fst_lt (oth_pts ms₁).
Proof.
intros pt₁ pt₂ pts ms₁ Hsort Hms₁.
revert pt₁ pt₂ ms₁ Hsort Hms₁.
induction pts as [| pt₃]; intros.
 subst ms₁; constructor.

 simpl in Hms₁.
 remember (minimise_slope pt₁ pt₃ pts) as ms₂.
 symmetry in Heqms₂.
 remember (slope_expr pt₁ pt₂ ?= slope ms₂)%Q as c.
 destruct c.
  subst ms₁; simpl.
  constructor.
   eapply IHpts; [ idtac | eassumption ].
   eapply Sorted_minus_2nd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

   eapply minimise_slope_lt_seg; eassumption.

  subst ms₁; constructor.

  subst ms₂.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Theorem edge_pts_sorted : ∀ pts hs,
  Sorted fst_lt pts
  → lower_convex_hull_points pts = Some hs
    → Sorted fst_lt (oth_pts hs).
Proof.
intros pts hs Hsort Hhs.
destruct pts as [| pt₁]; [ easy | idtac ].
destruct pts as [| pt₂]; [ easy | idtac ].
unfold lower_convex_hull_points in Hhs.
injection Hhs; clear Hhs; intros Hhs; subst hs; simpl.
eapply minimise_slope_seg_sorted; [ eassumption | reflexivity ].
Qed.

Theorem ini_oth_fin_pts_sorted : ∀ pol ns,
  newton_segments pol = Some ns
  → Sorted fst_lt [ini_pt ns … oth_pts ns ++ [fin_pt ns]].
Proof.
intros pol ns Hns.
constructor.
 remember Hns as Hns_v; clear HeqHns_v.
 unfold newton_segments in Hns.
 remember (points_of_ps_polynom pol) as pts.
 apply points_of_polyn_sorted in Heqpts.
 apply Sorted_app_at_r.
  eapply edge_pts_sorted; eassumption.

  intros (hq, αh) Hh.
  eapply hq_lt_kq; try eassumption.
  symmetry; apply surjective_pairing.

 remember Hns as Hini; clear HeqHini.
 apply exists_ini_pt_nat in Hini.
 destruct Hini as (j, (aj, Hini)).
 remember Hns as Hfin; clear HeqHfin.
 apply exists_fin_pt_nat in Hfin.
 destruct Hfin as (k, (ak, Hfin)).
 symmetry in Hini, Hfin.
 apply HdRel_app.
  remember (oth_pts ns) as pts eqn:Hpts .
  symmetry in Hpts.
  destruct pts as [| (h, ah)]; constructor.
  rewrite <- Hini; unfold fst_lt; simpl.
  eapply jq_lt_hq; try eassumption.
  rewrite Hpts; left; reflexivity.

  constructor.
  rewrite <- Hini, <- Hfin; unfold fst_lt; simpl.
  unfold Qlt; simpl.
  do 2 rewrite Z.mul_1_r.
  eapply jz_lt_kz; try eassumption.
   rewrite <- Hini; reflexivity.

   rewrite <- Hfin; reflexivity.
Qed.

Close Scope nat_scope.

(* not real degree, since last coefficient can be null *)
Definition pseudo_degree (p : polynomial α) := pred (List.length (al p)).

Theorem list_shrink_skipn : ∀ cnt k (l : list α),
  list_shrink_aux cnt k l = list_shrink_aux 0 k (List.skipn cnt l).
Proof.
intros cnt k l.
revert cnt.
induction l as [| x]; intros; [ idtac | simpl ].
 destruct cnt; reflexivity.

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
destruct k.
 exfalso; revert Hk; apply Nat.nlt_0_r.

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
destruct k.
 destruct l; [ reflexivity | discriminate Hk ].

 simpl; apply IHl; assumption.
Qed.

Theorem list_length_shrink : ∀ cnt k (l : list α),
  (S cnt < length l)%nat
  → List.length (list_shrink_aux cnt k l) = S ((List.length l - S cnt) / S k).
Proof.
intros cnt k l Hcl.
revert cnt k Hcl.
induction l; intros.
 exfalso; revert Hcl; apply Nat.nlt_0_r.

 remember (S k) as k'; simpl; subst k'.
 remember (S k) as k'; destruct cnt; simpl; subst k'.
  rewrite Nat.sub_0_r.
  apply Nat.succ_inj_wd.
  destruct (lt_eq_lt_dec (S k) (length l)) as [[H₁| H₁]| H₁].
   rewrite IHl; [ idtac | assumption ].
   simpl in Hcl.
   assert (length l = length l - S k + 1 * S k)%nat as H.
    rewrite Nat.mul_1_l.
    rewrite Nat.sub_add; auto.
    apply Nat.lt_le_incl; auto.

    rewrite H in |- * at 2; clear H.
    rewrite Nat.div_add; [ idtac | intros H; discriminate H ].
    rewrite Nat.add_1_r; reflexivity.

   rewrite <- H₁.
   rewrite Nat.div_same; auto.
   rewrite list_shrink_skipn.
   apply length_shrink_skipn_eq; symmetry; assumption.

   rewrite Nat.div_small; [ idtac | assumption ].
   rewrite list_shrink_skipn.
   apply length_shrink_skipn_lt; assumption.

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
induction l as [| a]; intros; simpl.
 rewrite list_length_pad; simpl.
 simpl in Hjpx.
 rewrite <- Nat.add_sub_swap; auto.
 rewrite Nat.add_1_r; reflexivity.

 rewrite list_length_pad; simpl.
 simpl in Hjpx.
 rewrite IHl.
  eapply Sorted_trans_app in Hsort; [ idtac | idtac | left; eauto  ].
   rewrite <- Nat.add_sub_swap; auto.
   rewrite <- Nat.sub_succ_l; [ idtac | apply Nat.lt_le_incl; auto ].
   rewrite Nat.add_sub_assoc; [ idtac | apply Nat.lt_le_incl; auto ].
   rewrite Nat.add_sub_swap; auto.
   rewrite Nat.sub_diag; reflexivity.

   clear x Hsort.
   intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

  simpl in Hsort.
  destruct l as [| b]; simpl in Hsort; simpl.
   apply Sorted_inv_2 in Hsort.
   destruct Hsort; assumption.

   apply Sorted_inv_2 in Hsort.
   destruct Hsort; assumption.

  simpl in Hsort.
  apply Sorted_inv in Hsort.
  destruct Hsort; assumption.
Qed.

Theorem length_char_pol : ∀ pol ns pl tl j αj k αk,
  newton_segments pol = Some ns
  → ini_pt ns = (Qnat j, αj)
    → fin_pt ns = (Qnat k, αk)
      → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
        → tl = List.map (term_of_point pol) pl
          → length (make_char_pol R j tl) = S (k - j).
Proof.
intros pol ns pl tl j αj k αk Hns Hini Hfin Hpl Htl.
rewrite Htl, Hpl, Hini; simpl.
rewrite nat_num_Qnat, Nat.sub_diag; simpl.
rewrite List.map_app; simpl.
rewrite length_char_pol_succ; simpl.
 rewrite Hfin; simpl.
 rewrite nat_num_Qnat.
 reflexivity.

 remember (List.map (term_of_point pol) (oth_pts ns)) as tl₂ eqn:Htl₂ .
 remember (term_of_point pol (Z.of_nat k # 1, αk)) as tk eqn:Htk .
 unfold term_of_point, lap_term_of_point in Htk; simpl in Htk.
 unfold nat_num in Htk; simpl in Htk.
 rewrite Nat2Z.id in Htk.
 subst tk; simpl.
 remember (oth_pts ns) as pts eqn:Hpts .
 symmetry in Hpts.
 destruct pts as [| (h, αh)].
  subst tl₂; simpl.
  rewrite Hfin; simpl; rewrite nat_num_Qnat;
  eapply j_lt_k; try eassumption.
   rewrite Hini; simpl; rewrite nat_num_Qnat; reflexivity.

   rewrite Hfin; simpl; rewrite nat_num_Qnat; reflexivity.

  subst tl₂; simpl.
  assert ((h, αh) ∈ oth_pts ns) as Hh by (rewrite Hpts; left; reflexivity).
  remember Hh as H; clear HeqH.
  eapply exists_oth_pt_nat in H; [ idtac | eassumption ].
  destruct H as (i, (ai, Hi)).
  injection Hi; clear Hi; intros; subst h ai; rename i into h.
  rewrite nat_num_Qnat.
  symmetry in Hini.
  eapply j_lt_h; try eassumption; reflexivity.

 remember Hns as Hsort; clear HeqHsort.
 apply ini_oth_fin_pts_sorted in Hsort.
 apply Sorted_inv_1 in Hsort.
 remember (oth_pts ns ++ [fin_pt ns]) as pts eqn:Hpts .
 remember (List.map (term_of_point pol) pts) as li eqn:Hli .
 remember Hli as H; clear HeqH.
 rewrite Hpts in Hli.
 rewrite List.map_app in Hli; simpl in Hli.
 rewrite <- Hli, H.
 assert (∀ pt, pt ∈ pts → ∃ (h : nat) (αh : Q), pt = (Qnat h, αh)) as Hnat.
  intros pt Hpt.
  eapply points_in_newton_segment_have_nat_abscissa; try eassumption.
  right; rewrite <- Hpts; assumption.

  revert Hsort Hnat; clear; intros.
  induction pts as [| pt]; [ constructor | simpl ].
  constructor.
   apply IHpts.
    eapply Sorted_inv_1; eassumption.

    intros pt₁ Hpt₁.
    apply Hnat.
    right; assumption.

   apply Sorted_inv in Hsort.
   destruct Hsort as (_, Hrel).
   unfold fst_lt in Hrel.
   revert Hrel Hnat; clear; intros.
   destruct pts as [| pt₁]; constructor; simpl.
   apply HdRel_inv in Hrel.
   assert (pt ∈ [pt; pt₁ … pts]) as H₁ by (left; reflexivity).
   assert (pt₁ ∈ [pt; pt₁ … pts]) as H₂ by (right; left; reflexivity).
   apply Hnat in H₁.
   apply Hnat in H₂.
   destruct H₁ as (h₁, (ah₁, Hh₁)).
   destruct H₂ as (h₂, (ah₂, Hh₂)).
   subst pt pt₁; simpl in Hrel; simpl.
   do 2 rewrite nat_num_Qnat.
   apply Qnat_lt; assumption.
Qed.

Theorem Sorted_fst_lt_nat_num_fst : ∀ l,
  (∀ a, a ∈ l → fst a = Qnat (Z.to_nat (Qnum (fst a))))
  → Sorted fst_lt l
    → Sorted (λ x y, (nat_num (fst x) < nat_num (fst y))%nat) l.
Proof.
intros l Hnat Hsort.
apply Sorted_LocallySorted_iff in Hsort.
apply Sorted_LocallySorted_iff.
induction l as [| a]; [ constructor | idtac ].
destruct l as [| b]; constructor.
 apply IHl.
  intros c Hc.
  apply Hnat; right; assumption.

  inversion Hsort; assumption.

 inversion Hsort; subst.
 rewrite Hnat; [ idtac | left; reflexivity ].
 apply Nat.nle_gt.
 rewrite Hnat; [ idtac | right; left; reflexivity ].
 apply Nat.nle_gt.
 do 2 rewrite nat_num_Qnat.
 unfold fst_lt in H3.
 rewrite Hnat in H3; [ idtac | left; reflexivity ].
 apply Qlt_not_le in H3.
 rewrite Hnat in H3; [ idtac | right; left; reflexivity ].
 apply Qnot_le_lt in H3.
 apply Qnat_lt; assumption.
Qed.

Theorem fold_char_pol : ∀ pol j αj tl,
  [order_coeff (List.nth j (al pol) 0%ps)
   … make_char_pol R (S j) (List.map (term_of_point pol) tl)] =
  make_char_pol R j
    (List.map (term_of_point pol) [(Qnat j, αj) … tl]).
Proof.
intros pol j αj tl; simpl.
rewrite nat_num_Qnat, Nat.sub_diag; simpl.
reflexivity.
Qed.

Definition nat_fst_lt (x y : Q * Q) :=
  (nat_num (fst x) < nat_num (fst y))%nat.

Theorem shrinkable_if : ∀ pol q pt₁ pts,
  Sorted nat_fst_lt [pt₁ … pts]
  → q ≠ O
  → List.Forall (λ pt, (q | nat_num (fst pt) - nat_num (fst pt₁))%nat) pts
  → poly_shrinkable q
      POL (make_char_pol R (nat_num (fst pt₁))
            (List.map (term_of_point pol) [pt₁ … pts]))%pol.
Proof.
intros pol q pt₁ pts Hsort Hq Hpts; simpl.
rewrite Nat.sub_diag, list_pad_0.
rewrite List.Forall_forall in Hpts.
unfold poly_shrinkable; intros n Hn; simpl.
destruct n.
 rewrite Nat.mod_0_l in Hn; auto.
 exfalso; apply Hn; reflexivity.

 revert n pt₁ Hsort Hpts Hn.
 induction pts as [| pt₂]; intros; [ destruct n; reflexivity | simpl ].
 apply Sorted_inv in Hsort.
 destruct Hsort as (Hsort, Hrel).
 apply HdRel_inv in Hrel.
 unfold nat_fst_lt in Hrel; simpl in Hrel.
 destruct (lt_dec (nat_num (fst pt₁)) (nat_num (fst pt₂))) as [H₁| H₁].
  unfold lt in H₁.
  remember (nat_num (fst pt₁)) as j eqn:Hj .
  remember (nat_num (fst pt₂)) as h eqn:Hh .
  destruct (eq_nat_dec (S j) h) as [H₂| H₂].
   assert (pt₂ ∈ [pt₂ … pts]) as H by (left; auto).
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

   destruct (lt_dec n (h - S j)) as [H₃| H₃].
    rewrite list_nth_pad_lt; auto.

    apply Nat.nlt_ge in H₃.
    rewrite list_nth_pad_sub; auto.
    destruct (eq_nat_dec (h - S j) n) as [H₄| H₄].
     exfalso.
     assert (pt₂ ∈ [pt₂ … pts]) as H by (left; auto).
     apply Hpts in H.
     rewrite <- Hh in H.
     destruct H as (c, Hc).
     rewrite <- H₄ in Hn.
     simpl in Hsort; simpl.
     rewrite <- Nat.sub_succ_l in Hn; auto.
     rewrite Nat.sub_succ in Hn.
     rewrite Hc in Hn.
     apply Hn, Nat.mod_mul; auto.

     remember (n - (h - S j))%nat as nhj eqn:Hnhj .
     symmetry in Hnhj.
     destruct nhj.
      apply Nat.sub_0_le in Hnhj.
      apply Nat_le_neq_lt in H₃; auto.
      apply Nat.nle_gt in H₃.
      contradiction.

      destruct (eq_nat_dec (S nhj mod q) 0) as [H₅| H₅].
       apply Nat.mod_divides in H₅; auto.
       destruct H₅ as (c, Hc).
       apply Nat.add_sub_eq_nz in Hnhj; [ idtac | intros H; discriminate H ].
       exfalso; apply Hn.
       rewrite <- Hnhj.
       rewrite Hc.
       rewrite <- Nat.add_succ_l.
       rewrite <- Nat.sub_succ_l; auto.
       rewrite Nat.sub_succ.
       assert (pt₂ ∈ [pt₂ … pts]) as H by (left; auto).
       apply Hpts in H.
       rewrite <- Hh in H.
       destruct H as (d, Hd).
       rewrite Nat.mul_comm.
       rewrite Hd, <- Nat.mul_add_distr_r.
       apply Nat.mod_mul; auto.

       rewrite Hh.
       apply IHpts; auto.
       intros pt Hpt.
       assert (pt ∈ [pt₂ … pts]) as H by (right; auto).
       apply Hpts in H.
       destruct H as (c, Hc).
       rewrite <- Hh.
       unfold divide.
       assert (pt₂ ∈ [pt₂ … pts]) as H by (left; auto).
       apply Hpts in H.
       rewrite <- Hh in H.
       destruct H as (d, Hd).
       exists (c - d)%nat.
       rewrite Nat.mul_sub_distr_r.
       rewrite <- Hc, <- Hd.
       rewrite Nat_sub_sub_distr; [ idtac | apply Nat.lt_le_incl; auto ].
       rewrite Nat.sub_add; auto.
       apply Nat.lt_le_incl.
       eapply Nat.lt_trans; eauto .
       revert Hsort Hh Hpt; clear; intros; subst h.
       revert pt₂ pt Hsort Hpt.
       induction pts as [| pt₃]; intros; [ contradiction | idtac ].
       destruct Hpt as [Hpt| Hpt].
        subst pt.
        apply Sorted_inv in Hsort.
        destruct Hsort as (_, Hrel).
        apply HdRel_inv in Hrel.
        assumption.

        apply IHpts; auto.
        eapply Sorted_minus_2nd; eauto .
        intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

  contradiction.
Qed.

Theorem phi_pseudo_degree_is_k_sub_j_div_q : ∀ pol ns j αj k αk q m,
  newton_segments pol = Some ns
  → pol_in_K_1_m pol m
  → (Qnat j, αj) = ini_pt ns
  → (Qnat k, αk) = fin_pt ns
  → q = Pos.to_nat (q_of_m m (γ ns))
  → poly_shrinkable q (Φq pol ns)
    ∧ pseudo_degree (Φs q pol ns) = ((k - j) / q)%nat.
Proof.
intros pol ns j αj k αk q m Hns Hm Hj Hk Hq.
split.
 apply shrinkable_if.
  remember Hns as H; clear HeqH.
  apply ini_oth_fin_pts_sorted in H.
  apply Sorted_fst_lt_nat_num_fst in H; auto.
  intros pt Hpt.
  unfold Qnat.
  eapply points_in_newton_segment_have_nat_abscissa in Hpt; eauto .
  destruct Hpt as (h, (ah, Hpt)).
  subst pt; simpl.
  rewrite Nat2Z.id; reflexivity.

  rewrite Hq; auto.

  apply List.Forall_forall.
  intros pt Hpt.
  rewrite <- Hj; simpl.
  rewrite nat_num_Qnat.
  apply List.in_app_or in Hpt.
  destruct Hpt as [Hpt| Hpt].
   remember Hpt as H; clear HeqH.
   eapply exists_oth_pt_nat in H; eauto .
   destruct H as (h, (ah, Hoth)).
   subst pt; simpl.
   rewrite nat_num_Qnat.
   eapply q_is_factor_of_h_minus_j; eauto .
   apply List.in_or_app; left; eauto .

   destruct Hpt as [Hpt| ]; [ idtac | contradiction ].
   subst pt; simpl.
   rewrite <- Hk; simpl.
   rewrite nat_num_Qnat.
   eapply q_is_factor_of_h_minus_j; eauto .
   apply List.in_or_app.
   right; left; eauto .

 unfold pseudo_degree, Φs; simpl.
 rewrite <- Hj; simpl.
 rewrite Nat.sub_diag, list_pad_0.
 rewrite nat_num_Qnat.
 unfold list_shrink.
 rewrite list_length_shrink; simpl.
  rewrite divmod_div.
  rewrite Nat.sub_0_r.
  f_equal.
   rewrite List.map_app; simpl.
   rewrite length_char_pol_succ.
    rewrite <- Hk; simpl.
    rewrite nat_num_Qnat; reflexivity.

    remember (oth_pts ns) as opts eqn:Hopts .
    symmetry in Hopts.
    destruct opts as [| (h, αh)].
     simpl.
     rewrite <- Hk; simpl.
     rewrite nat_num_Qnat.
     eapply j_lt_k; try eassumption.
      rewrite <- Hj; simpl.
      rewrite nat_num_Qnat; reflexivity.

      rewrite <- Hk; simpl.
      rewrite nat_num_Qnat; reflexivity.

     simpl.
     assert ((h, αh) ∈ oth_pts ns) as H.
      rewrite Hopts; left; reflexivity.

      eapply j_lt_h; try eassumption; try reflexivity.
      unfold newton_segments in Hns.
      eapply oth_pts_in_init_pts in H; try eassumption.
      eapply pt_absc_is_nat in H; [ idtac | reflexivity ].
      simpl in H; assumption.

    rewrite list_map_app_at.
    apply Sorted_map.
    apply Sorted_fst_lt_nat_num_fst.
     intros a Ha.
     remember (points_of_ps_polynom pol) as pts.
     symmetry in Heqpts.
     eapply pt_absc_is_nat; [ eassumption | idtac ].
     apply List.in_app_or in Ha.
     unfold newton_segments in Hns.
     rewrite Heqpts in Hns.
     destruct Ha as [Ha| [Ha| ]]; [ idtac | idtac | contradiction ].
      eapply oth_pts_in_init_pts; eassumption.

      subst a.
      apply ini_fin_ns_in_init_pts; eassumption.

     eapply Sorted_inv_1.
     eapply ini_oth_fin_pts_sorted; eassumption.

   subst q.
   rewrite <- Nat.sub_succ_l; [ apply Nat_sub_succ_1 | idtac ].
   apply Pos2Nat.is_pos.

  apply lt_n_S.
  clear Hj.
  revert j.
  induction (oth_pts ns); intros; simpl.
   rewrite list_length_pad; simpl.
   rewrite <- Hk; simpl.
   rewrite nat_num_Qnat.
   rewrite Nat.add_comm; simpl.
   apply Nat.lt_0_succ.

   rewrite list_length_pad; simpl.
   eapply lt_le_trans.
    apply IHl with (j := nat_num (fst a)).

    rewrite Nat.add_succ_r, <- Nat.add_succ_l.
    apply le_plus_r.
Qed.

Definition has_degree pol d :=
  pseudo_degree pol = d ∧ (List.nth d (al pol) 0 ≠ 0)%K.

Theorem list_nth_shrink : ∀ n k l (d : α) cnt,
  List.nth n (list_shrink_aux cnt k l) d = List.nth (cnt + n * S k) l d.
Proof.
intros n k l d cnt.
revert n k cnt.
induction l as [| a]; intros; [ destruct n, cnt; reflexivity | idtac ].
destruct n; simpl.
 destruct cnt; simpl; [ reflexivity | rewrite IHl; reflexivity ].

 destruct cnt; simpl; rewrite IHl; reflexivity.
Qed.

Theorem ord_coeff_non_zero_in_newt_segm : ∀ pol ns h αh hps,
  newton_segments pol = Some ns
  → (Qnat h, αh) ∈ [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → hps = List.nth h (al pol) 0%ps
      → (order_coeff hps ≠ 0)%K.
Proof.
intros pol ns h αh hps Hns Hh Hhps.
unfold order_coeff.
remember (series_order (ps_terms hps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 apply series_order_iff in Hn.
 destruct Hn; assumption.

 remember (points_of_ps_polynom pol) as pts eqn:Hpts .
 remember Hpts as H; clear HeqH.
 eapply in_pts_in_pol in H; try eassumption.
  destruct H as (Hhp, Hhhv).
  unfold order in Hhhv.
  rewrite Hn in Hhhv; discriminate Hhhv.

  unfold newton_segments in Hns.
  rewrite <- Hpts in Hns.
  destruct Hh as [Hh| Hh].
   apply ini_fin_ns_in_init_pts in Hns.
   rewrite Hh in Hns.
   destruct Hns; eassumption.

   apply List.in_app_or in Hh.
   destruct Hh as [Hh| [Hh| ]]; [ idtac | idtac | contradiction ].
    eapply oth_pts_in_init_pts in Hns; eassumption.

    apply ini_fin_ns_in_init_pts in Hns.
    rewrite Hh in Hns.
    destruct Hns; eassumption.
Qed.

Theorem Sorted_fst_2nd_lt_last : ∀ j αj k αk t₁ t₂ t₃ tl,
  Sorted (λ pt₁ pt₂, Qnum (fst pt₁) < Qnum (fst pt₂)) [t₁; t₂; t₃ … tl]
  → (Qnat j, αj) = t₁
    → (Qnat (S k), αk) = List.last [t₃ … tl] (0, 0)%Q
      → (nat_num (fst t₂) < S k)%nat.
Proof.
intros j αj k αk t₁ t₂ t₃ tl Hsort Hj Hk.
revert k αk t₃ Hsort Hk.
induction tl as [| t₄]; intros.
 simpl in Hk.
 apply Sorted_inv in Hsort.
 destruct Hsort as (Hsort, Hrel).
 apply Sorted_inv in Hsort.
 destruct Hsort as (Hsort, Hrel₁).
 apply HdRel_inv in Hrel₁.
 rewrite <- Hk in Hrel₁; remember (S k) as x; simpl in Hrel₁; subst x.
 apply Z2Nat.inj_lt in Hrel₁.
  rewrite Nat2Z.id in Hrel₁.
  assumption.

  apply Z.lt_le_incl.
  apply HdRel_inv in Hrel.
  subst t₁.
  simpl in Hrel.
  eapply Z.le_lt_trans; [ apply Nat2Z.is_nonneg | eassumption ].

  apply Nat2Z.is_nonneg.

 remember [t₄ … tl] as x; simpl in Hk; subst x.
 eapply IHtl; try eassumption.
 eapply Sorted_minus_3rd; [ idtac | eassumption ].
 intros x y z H₁ H₂; eapply Z.lt_trans; eassumption.
Qed.

Theorem list_nth_coeff_last : ∀ pol j αj k αk tl,
  (Qnat j, αj) = List.hd (0, 0)%Q tl
  → (Qnat k, αk) = List.last tl (0, 0)%Q
    → (j < k)%nat
      → Sorted (λ pt₁ pt₂, Qnum (fst pt₁) < Qnum (fst pt₂)) tl
        → List.Forall (λ pt, Qden (fst pt) = xH) tl
          → List.nth (k - j)
              (make_char_pol R j
                 (List.map (term_of_point pol) tl)) 0%K =
            coeff (term_of_point pol (List.last tl (0, 0)%Q)).
Proof.
intros pol j αj k αk tl Hj Hk Hjk Hsort Hden; simpl.
destruct tl as [| t₁].
 simpl in Hj, Hk.
 injection Hj; clear Hj; intros; subst αj.
 injection Hk; clear Hk; intros; subst αk.
 rewrite <- Nat2Z.inj_0 in H0.
 rewrite <- Nat2Z.inj_0 in H1.
 apply Nat2Z.inj in H0.
 apply Nat2Z.inj in H1.
 subst j k.
 exfalso; revert Hjk; apply Nat.lt_irrefl.

 simpl in Hj; rewrite <- Hk, <- Hj; simpl.
 rewrite nat_num_Qnat, Nat.sub_diag, list_pad_0.
 destruct tl as [| t₂].
  simpl in Hk; subst t₁.
  injection Hk; clear Hk; intros.
  apply Nat2Z.inj in H0; subst k.
  exfalso; revert Hjk; apply Nat.lt_irrefl.

  simpl.
  remember (k - j)%nat as kj eqn:Hkj .
  symmetry in Hkj.
  destruct kj; [ exfalso; fast_omega Hjk Hkj | idtac ].
  destruct k; [ discriminate Hkj | idtac ].
  rewrite Nat.sub_succ_l in Hkj; [ idtac | fast_omega Hjk ].
  apply eq_add_S in Hkj; subst kj.
  revert j αj k αk t₁ t₂ Hj Hk Hjk Hsort Hden.
  induction tl as [| t₃]; intros.
   simpl in Hk; subst t₂; simpl.
   rewrite nat_num_Qnat.
   remember (S k) as x; simpl; subst x.
   rewrite Nat.sub_succ.
   rewrite list_nth_pad_sub; [ rewrite Nat.sub_diag | idtac ]; reflexivity.

   simpl.
   rewrite list_nth_pad_sub.
    rewrite Nat_sub_sub_distr.
     rewrite Nat.add_succ_r.
     rewrite Nat.sub_add; [ idtac | fast_omega Hjk ].
     rewrite Nat.sub_succ_l.
      simpl.
      destruct t₂ as (h₁, αh₁).
      eapply IHtl with (αj := αh₁); try eassumption; try reflexivity.
       eapply Sorted_fst_2nd_lt_last; eassumption.

       unfold Qnat, nat_num; simpl.
       rewrite Z2Nat.id.
        apply Sorted_inv in Hsort.
        destruct Hsort as (Hsort, Hrel).
        simpl.
        apply list_Forall_inv in Hden.
        destruct Hden as (_, Hden).
        apply list_Forall_inv in Hden.
        destruct Hden as (Hden, _).
        simpl in Hden.
        rewrite <- Hden.
        destruct h₁; assumption.

        rewrite <- Hj in Hsort.
        apply Sorted_inv in Hsort.
        destruct Hsort as (_, H).
        apply HdRel_inv in H.
        unfold Qnat in H; simpl in H.
        apply Z.lt_le_incl.
        eapply Z.le_lt_trans; [ apply Nat2Z.is_nonneg | eassumption ].

       unfold Qnat, nat_num; simpl; rewrite Z2Nat.id.
        constructor; [ reflexivity | idtac ].
        apply list_Forall_inv in Hden.
        destruct Hden as (_, H).
        apply list_Forall_inv in H.
        destruct H as (_, H); assumption.

        rewrite <- Hj in Hsort.
        apply Sorted_inv in Hsort.
        destruct Hsort as (_, H).
        apply HdRel_inv in H.
        unfold Qnat in H; simpl in H.
        apply Z.lt_le_incl.
        eapply Z.le_lt_trans; [ apply Nat2Z.is_nonneg | eassumption ].

      apply Nat.lt_succ_r.
      eapply Sorted_fst_2nd_lt_last; eassumption.

     subst t₁.
     apply Sorted_inv in Hsort.
     destruct Hsort as (_, H).
     apply HdRel_inv in H; simpl in H.
     apply Z2Nat.inj_lt in H.
      rewrite Nat2Z.id in H.
      assumption.

      apply Nat2Z.is_nonneg.

      apply Z.lt_le_incl.
      eapply Z.le_lt_trans; [ apply Nat2Z.is_nonneg | eassumption ].

    remember (nat_num (fst t₂)) as h₁ eqn:Hh₁ .
    remember (h₁ - S j)%nat as x.
    rewrite <- Nat.sub_succ; subst x.
    apply Nat.sub_le_mono_r.
    apply Nat.le_le_succ_r.
    apply Nat.lt_succ_r.
    subst h₁.
    eapply Sorted_fst_2nd_lt_last; eassumption.
Qed.

Theorem oth_pts_den_1 : ∀ pol ns,
  newton_segments pol = Some ns
  → List.Forall (λ pt, Qden (fst pt) = 1%positive) (oth_pts ns).
Proof.
intros pol ns Hns.
apply List.Forall_forall.
intros pt Hpt.
eapply exists_oth_pt_nat in Hpt; [ idtac | eassumption ].
destruct Hpt as (h, (αh, Hpt)).
subst pt; reflexivity.
Qed.

Theorem Sorted_Qnat_Sorted_Qnum : ∀ pts,
  Sorted fst_lt pts
  → List.Forall (λ pt, Qden (fst pt) = 1%positive) pts
    → Sorted (λ pt₁ pt₂, Qnum (fst pt₁) < Qnum (fst pt₂)) pts.
Proof.
intros pts Hsort Hden1.
apply Sorted_LocallySorted_iff in Hsort.
apply Sorted_LocallySorted_iff.
induction pts as [| pt]; [ constructor | idtac ].
destruct pts as [| pt₂]; constructor.
 apply IHpts.
  inversion Hsort; assumption.

  eapply list_Forall_inv; eassumption.

 inversion Hsort; subst.
 apply list_Forall_inv in Hden1.
 destruct Hden1 as (Hden1, H).
 apply list_Forall_inv in H.
 destruct H as (Hden₂, _).
 unfold fst_lt in H3.
 unfold Qlt in H3.
 rewrite Hden1, Hden₂ in H3.
 do 2 rewrite Z.mul_1_r in H3; assumption.
Qed.

(* [Walker, p. 100] « Therefore (3.4) has the form c^j Φ(c^q) = 0
   where Φ(z) is a polynomial, of degree (k - j)/q » *)
Theorem phi_degree_is_k_sub_j_div_q : ∀ pol ns j αj k αk q m,
  newton_segments pol = Some ns
  → pol_in_K_1_m pol m
  → (Qnat j, αj) = ini_pt ns
  → (Qnat k, αk) = fin_pt ns
  → q = Pos.to_nat (q_of_m m (γ ns))
  → poly_shrinkable q (Φq pol ns)
     ∧ has_degree (Φs q pol ns) ((k - j) / q).
Proof.
intros pol ns j αj k αk q m Hns Hm Hj Hk Hq.
split.
 apply shrinkable_if.
  remember Hns as H; clear HeqH.
  apply ini_oth_fin_pts_sorted in H.
  apply Sorted_fst_lt_nat_num_fst in H; auto.
  intros pt Hpt.
  unfold Qnat.
  eapply points_in_newton_segment_have_nat_abscissa in Hpt; eauto .
  destruct Hpt as (h, (ah, Hpt)).
  subst pt; simpl.
  rewrite Nat2Z.id; reflexivity.

  rewrite Hq; auto.

  apply List.Forall_forall.
  intros pt Hpt.
  rewrite <- Hj; simpl.
  rewrite nat_num_Qnat.
  apply List.in_app_or in Hpt.
  destruct Hpt as [Hpt| Hpt].
   remember Hpt as H; clear HeqH.
   eapply exists_oth_pt_nat in H; eauto .
   destruct H as (h, (ah, Hoth)).
   subst pt; simpl.
   rewrite nat_num_Qnat.
   eapply q_is_factor_of_h_minus_j; eauto .
   apply List.in_or_app; left; eauto .

   destruct Hpt as [Hpt| ]; [ idtac | contradiction ].
   subst pt; simpl.
   rewrite <- Hk; simpl.
   rewrite nat_num_Qnat.
   eapply q_is_factor_of_h_minus_j; eauto .
   apply List.in_or_app.
   right; left; eauto .

 unfold has_degree.
 unfold pseudo_degree.
 remember (al (Φs q pol ns)) as l.
 apply imp_or_tauto.
  intros H.
  unfold Φs in Heql.
  rewrite Φq_pol in Heql.
  remember [ini_pt ns … oth_pts ns ++ [fin_pt ns]] as pl.
  rewrite <- Hj in Heql; simpl in Heql.
  rewrite nat_num_Qnat in Heql.
  subst l.
  unfold list_shrink.
  rewrite list_nth_shrink.
  rewrite Nat.add_0_l.
  rewrite <- Nat.sub_succ_l; [ idtac | subst q; apply Pos2Nat.is_pos ].
  rewrite Nat_sub_succ_1.
  rewrite Nat.mul_comm.
  rewrite <- Nat.divide_div_mul_exact; [ idtac | subst q; auto | idtac ].
   rewrite Nat.mul_comm.
   rewrite Nat.div_mul; [ idtac | subst q; auto ].
   subst pl.
   erewrite list_nth_coeff_last; try eassumption.
    rewrite list_last_cons_app; simpl.
    rewrite <- Hk; simpl.
    rewrite nat_num_Qnat; simpl.
    eapply ord_coeff_non_zero_in_newt_segm; try eassumption; try reflexivity.
    rewrite <- Hk; right.
    apply List.in_or_app; right; left; reflexivity.

    rewrite list_last_cons_app; eassumption.

    eapply j_lt_k; try eassumption.
     rewrite <- Hj; simpl; rewrite nat_num_Qnat; reflexivity.

     rewrite <- Hk; simpl; rewrite nat_num_Qnat; reflexivity.

    constructor.
     apply Sorted_app_at_r.
      remember Hns as Hsort; clear HeqHsort.
      apply ini_oth_fin_pts_sorted in Hsort.
      apply Sorted_inv_1 in Hsort.
      apply Sorted_app in Hsort.
      destruct Hsort as (Hsort, _).
      apply Sorted_Qnat_Sorted_Qnum.
       apply ini_oth_fin_pts_sorted in Hns.
       apply Sorted_inv_1 in Hns.
       apply Sorted_app in Hns.
       destruct Hns; assumption.

       eapply oth_pts_den_1; eassumption.

      intros pt Hpt.
      remember Hns as Hsort; clear HeqHsort.
      apply ini_oth_fin_pts_sorted in Hsort.
      apply Sorted_inv_1 in Hsort.
      apply Sorted_Qnat_Sorted_Qnum in Hsort.
       eapply Sorted_trans_app in Hsort; try eassumption.
       intros x y z H₁ H₂; eapply Z.lt_trans; eassumption.

       apply List.Forall_forall; intros x Hx.
       apply List.in_app_or in Hx.
       destruct Hx as [Hx| Hx].
        revert x Hx.
        apply List.Forall_forall.
        eapply oth_pts_den_1; eassumption.

        destruct Hx as [Hx| ]; [ idtac | contradiction ].
        rewrite <- Hx, <- Hk; reflexivity.

     apply HdRel_app; [ idtac | constructor ].
      remember (oth_pts ns) as pts eqn:Hpts .
      symmetry in Hpts.
      destruct pts as [| pt]; constructor.
      rewrite <- Hj; simpl.
      apply Z2Nat.inj_lt.
       apply Nat2Z.is_nonneg.

       apply oth_pts_in_init_pts with (pt := pt) in Hns.
        eapply pt_absc_is_nat in Hns; [ idtac | reflexivity ].
        rewrite Hns; simpl.
        apply Nat2Z.is_nonneg.

        rewrite Hpts; left; reflexivity.

       rewrite Nat2Z.id.
       destruct pt as (h, αh); simpl.
       eapply j_lt_h; try eassumption; try reflexivity.
       rewrite Hpts; left.
       unfold Qnat; simpl.
       remember Hns as Hpt; clear HeqHpt.
       apply oth_pts_in_init_pts with (pt := (h, αh)) in Hpt.
        eapply pt_absc_is_nat in Hpt; [ idtac | reflexivity ].
        simpl in Hpt; rewrite Hpt.
        unfold Qnat; simpl.
        rewrite Nat2Z.id; reflexivity.

        rewrite Hpts; left; reflexivity.

      rewrite <- Hj, <- Hk; simpl.
      eapply jz_lt_kz; try eassumption.
       rewrite <- Hj; reflexivity.

       rewrite <- Hk; reflexivity.

    constructor.
     rewrite <- Hj; reflexivity.

     apply List.Forall_forall; intros pt Hpt.
     apply List.in_app_or in Hpt.
     destruct Hpt as [Hpt| Hpt].
      revert pt Hpt.
      apply List.Forall_forall.
      eapply oth_pts_den_1; eassumption.

      destruct Hpt as [Hpt| ]; [ idtac | contradiction ].
      rewrite <- Hpt, <- Hk; reflexivity.

   eapply q_is_factor_of_h_minus_j; try eassumption.
   apply List.in_or_app; right; left; symmetry; eassumption.

  subst l.
  eapply phi_pseudo_degree_is_k_sub_j_div_q; eassumption.
Qed.

End theorems.
