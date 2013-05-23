(* $Id: Puiseux.v,v 1.540 2013-05-23 13:27:26 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Sorted.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Puiseux_base.
Require Import Misc.

Set Implicit Arguments.

Definition degree α (pol : polynomial α) := List.length (al pol).

(* Horner's algorithm *)
Definition apply_poly {α} {β} {γ}
    (zero_plus_v : β → α) (add_v_coeff : α → β → α) (mul_v_x : α → γ → α)
    (pol : polynomial β) (x : γ) :=
  List.fold_right (λ c accu, add_v_coeff (mul_v_x accu x) c)
    (zero_plus_v (an pol)) (al pol).

Definition pol_add α (add_coeff : α → α → α) pol₁ pol₂ :=
  let fix loop al₁ al₂ :=
    match (al₁, al₂) with
    | ([], []) => mkpol [] (add_coeff (an pol₁) (an pol₂))
    | ([], [a₂ … bl₂]) =>
        mkpol [add_coeff (an pol₁) a₂ … bl₂] (an pol₂)
    | ([a₁ … bl₁], []) =>
        mkpol [add_coeff a₁ (an pol₂) … bl₁] (an pol₁)
    | ([a₁ … bl₁], [a₂ … bl₂]) =>
        let r := loop bl₁ bl₂ in
        mkpol [add_coeff a₁ a₂ … al r] (an r)
    end
  in
  loop (al pol₁) (al pol₂).

Definition ps_add α (add_coeff : α → α → α) (is_null_coeff : α → bool)
     (ps₁ : puiseux_series α) (ps₂ : puiseux_series α) :=
  let cofix loop ms₁ ms₂ :=
    match ms₁ with
    | Cons c₁ s₁ =>
        let cofix loop₁ ms₂ :=
          match ms₂ with
          | Cons c₂ s₂ =>
              match Qcompare (power c₁) (power c₂) with
              | Eq =>
                  let c := add_coeff (coeff c₁) (coeff c₂) in
                  let m := {| coeff := c; power := power c₁ |} in
                  Cons m (loop s₁ s₂)
              | Lt =>
                  Cons c₁ (loop s₁ ms₂)
              | Gt =>
                  Cons c₂ (loop₁ s₂)
              end
          | End => ms₁
          end
        in
        loop₁ ms₂
    | End => ms₂
    end
  in
  {| ps_monoms := loop (ps_monoms ps₁) (ps_monoms ps₂) |}.

(*
Definition apply_poly_with_ps {α} fld pol (x : α) := ...
value apply_poly_with_ps :
  field α β →
  polynomial (puiseux_series α) → puiseux_series α → puiseux_series α
value apply_poly_with_ps k pol =
  apply_poly {ps_monoms = []}
    (fun ps → ps_add (norm k.add k) (k.eq k.zero) ps)
    (ps_mul (norm k.add k) (norm k.mul k) (k.eq k.zero)) pol
*)

(*
Definition apply_poly_with_ps_poly {α} (fld : field α)
    (pol : polynomial (puiseux_series α)) :=
  apply_poly (λ x, x)
    (λ pol ps,
       pol_add (ps_add (add fld) (eq_zero_dec fld)) pol (mkpol [] ps)).
*)
(*
value apply_poly_with_ps_poly :
  field α β →
  polynomial (puiseux_series α) → polynomial (puiseux_series α) →
  polynomial (puiseux_series α)
value apply_poly_with_ps_poly k pol =
  apply_poly
    {ml = []}    
    (fun pol ps →
       pol_add (ps_add k.add (k.eq k.zero)) pol {ml = [ps]})
    (pol_mul
       {ps_monoms = []}
       (ps_add k.add (k.eq k.zero))
       (ps_mul k.add (norm k.mul k) (k.eq k.zero))
       (fun ps → ps.ps_monoms = []))
    pol
*)

Definition apply_polynomial {α} fld pol (x : α) :=
  List.fold_right (λ coeff accu, add fld (mul fld accu x) coeff) (an pol)
    (al pol).

Record algebraically_closed_field {α} :=
  { ac_field : field α;
    ac_prop : ∀ pol, degree pol ≥ 1
      → ∃ r, apply_polynomial ac_field pol r = zero ac_field }.

Definition nofq q := Z.to_nat (Qnum q).

Fixpoint make_char_pol α (fld : field α) cdeg dcl n :=
  match n with
  | O => []
  | S n₁ =>
      match dcl with
      | [] =>
          [zero fld … make_char_pol fld (S cdeg) [] n₁]
      | [(deg, coeff) … dcl₁] =>
          if eq_nat_dec deg cdeg then
            [coeff … make_char_pol fld (S cdeg) dcl₁ n₁]
          else
            [zero fld … make_char_pol fld (S cdeg) dcl n₁]
      end
    end.

Definition deg_coeff_of_point α (fld : field α) pol (pt : (Q * Q)) :=
  let h := nofq (fst pt) in
  let ps := List.nth h (al pol) (an pol) in
  let c := valuation_coeff fld ps in
  (h, c).

Definition characteristic_polynomial α (fld : field α) pol ns :=
  let dcl := List.map (deg_coeff_of_point fld pol) [ini_pt ns … oth_pts ns] in
  let j := nofq (fst (ini_pt ns)) in
  let k := nofq (fst (fin_pt ns)) in
  let cl := make_char_pol fld j dcl (k - j) in
  let kps := List.nth k (al pol) (an pol) in
  {| al := cl; an := valuation_coeff fld kps |}.

(* *)

Section field.

Variable α : Type.
Variable fld : field (puiseux_series α).

Lemma pt_absc_is_nat : ∀ pol pts pt,
  points_of_ps_polynom fld pol = pts
  → pt ∈ pts
    → ∃ n, fst pt = Qnat n.
Proof.
intros pol pts pt Hpts Hαh.
unfold points_of_ps_polynom in Hpts.
remember (al pol) as cl; clear Heqcl.
remember (an pol) as cn; clear Heqcn.
remember 0%nat as n in Hpts; clear Heqn.
unfold points_of_ps_polynom_gen in Hpts.
revert n pts Hpts Hαh.
induction cl as [| c]; intros.
 simpl in Hpts.
 destruct (is_zero_dec fld cn) as [Hz| Hnz].
  subst pts; contradiction.

  subst pts.
  destruct Hαh as [Hαh| ]; [ subst pt; simpl | contradiction ].
  exists n; reflexivity.

 simpl in Hpts.
 destruct (is_zero_dec fld c) as [Hz| Hnz].
  eapply IHcl; eassumption.

  subst pts.
  destruct Hαh as [Hαh| Hαh]; [ subst pt; simpl | idtac ].
   exists n; reflexivity.

   eapply IHcl in Hαh; [ assumption | reflexivity ].
Qed.

Lemma hull_seg_vert_in_init_pts : ∀ n pts hs hsl,
  next_ch_points n pts = hsl
  → hs ∈ hsl
    → pt hs ∈ pts.
Proof.
intros n pts hs hsl Hnp Hhs.
revert n pts hs Hnp Hhs.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct Hhs as [Hhs| Hhs].
 subst hs₁.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂].
  injection Hnp; intros; subst hs; left; reflexivity.

  injection Hnp; clear Hnp; intros Hnp Hhs.
  subst hs; left; reflexivity.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂].
  injection Hnp; intros; subst hsl; contradiction.

  injection Hnp; clear Hnp; intros Hnp Hs₁; subst hs₁.
  eapply IHhsl in Hhs; [ idtac | eassumption ].
  remember (minimise_slope pt₁ pt₂ pts) as ms₁.
  symmetry in Heqms₁.
  destruct Hhs as [Hhs| Hhs].
   rewrite <- Hhs.
   right; eapply end_pt_in; eassumption.

   right; right; eapply rem_pts_in; eassumption.
Qed.

Lemma ini_fin_ns_in_init_pts : ∀ pts ns,
  ns ∈ list_map_pairs newton_segment_of_pair (lower_convex_hull_points pts)
  → ini_pt ns ∈ pts ∧ fin_pt ns ∈ pts.
Proof.
intros pts ns Hns.
remember (lower_convex_hull_points pts) as hsl.
unfold lower_convex_hull_points in Heqhsl.
remember (length pts) as n; clear Heqn.
rename Heqhsl into Hnp; symmetry in Hnp.
revert pts ns n Hnp Hns.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct hsl as [| hs₂]; [ contradiction | idtac ].
destruct Hns as [Hns| Hns].
 subst ns; simpl.
 split.
  eapply hull_seg_vert_in_init_pts; [ eassumption | idtac ].
  left; reflexivity.

  eapply hull_seg_vert_in_init_pts; [ eassumption | idtac ].
  right; left; reflexivity.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
 eapply IHhsl in Hnp; [ idtac | eassumption ].
 remember (minimise_slope pt₁ pt₂ pts) as ms₁.
 symmetry in Heqms₁.
 destruct Hnp as (Hini, Hfin).
 split.
  destruct Hini as [Hini| Hini].
   rewrite <- Hini.
   right; eapply end_pt_in; eassumption.

   right; right; eapply rem_pts_in; eassumption.

  destruct Hfin as [Hfin| Hfin].
   rewrite <- Hfin.
   right; eapply end_pt_in; eassumption.

   right; right; eapply rem_pts_in; eassumption.
Qed.

Lemma j_lt_k : ∀ pol j k ns,
  ns ∈ newton_segments fld pol
  → j = nofq (fst (ini_pt ns))
    → k = nofq (fst (fin_pt ns))
      → (j < k)%nat.
Proof.
intros pol j k ns Hns Hj Hk.
unfold newton_segments in Hns.
remember (points_of_ps_polynom fld pol) as pts.
remember Heqpts as Hj₁; clear HeqHj₁; symmetry in Hj₁.
eapply pt_absc_is_nat with (pt := ini_pt ns) in Hj₁.
 remember Heqpts as Hk₁; clear HeqHk₁; symmetry in Hk₁.
 eapply pt_absc_is_nat with (pt := fin_pt ns) in Hk₁.
  apply points_of_polyn_sorted in Heqpts.
  rename Heqpts into Hsort.
  remember (lower_convex_hull_points pts) as hsl.
  unfold lower_convex_hull_points in Heqhsl.
  rename Heqhsl into Hnp.
  symmetry in Hnp.
  remember (length pts) as n; clear Heqn.
  remember (list_map_pairs newton_segment_of_pair hsl) as nsl.
  symmetry in Heqnsl.
  revert n pts ns nsl j k Hsort Hnp Hns Hj Hk Hj₁ Hk₁ Heqnsl.
  induction hsl as [| hs₁]; intros; [ subst nsl; contradiction | idtac ].
  destruct nsl as [| ns₁]; [ contradiction | idtac ].
  destruct Hns as [Hns| Hns].
   subst ns₁.
   simpl in Heqnsl.
   destruct hsl as [| hs₂]; [ discriminate Heqnsl | idtac ].
   injection Heqnsl; clear Heqnsl; intros Hnsl Hns.
   unfold newton_segment_of_pair in Hns.
   subst ns.
   simpl in Hj, Hk, Hj₁, Hk₁.
   apply next_points_sorted in Hnp; [ idtac | assumption ].
   apply Sorted_inv_2 in Hnp; destruct Hnp as (Hlt, Hnp).
   unfold hs_x_lt in Hlt; simpl in Hlt.
   unfold Qlt in Hlt.
   destruct Hj₁ as (jn, Hjn).
   destruct Hk₁ as (kn, Hkn).
   rewrite Hjn in Hj, Hlt.
   rewrite Hkn in Hk, Hlt.
   unfold nofq, Qnat in Hj, Hk.
   simpl in Hj, Hk.
   rewrite Nat2Z.id in Hj, Hk.
   subst jn kn.
   unfold Qnat in Hlt; simpl in Hlt.
   do 2 rewrite Zmult_1_r in Hlt.
   apply Nat2Z.inj_lt; assumption.

   destruct n; [ discriminate Hnp | simpl in Hnp ].
   destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
   destruct pts as [| pt₂].
    injection Hnp; clear Hnp; intros; subst hs₁ hsl.
    discriminate Heqnsl.

    injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
    simpl in Heqnsl.
    destruct hsl as [| hs₁]; [ discriminate Heqnsl | idtac ].
    remember [hs₁ … hsl] as x.
    injection Heqnsl; clear Heqnsl; intros Hnsl Hns₁; subst x.
    remember (minimise_slope pt₁ pt₂ pts) as ms.
    symmetry in Heqms.
    eapply IHhsl with (pts := [end_pt ms … rem_pts ms]); try eassumption.
    eapply minimise_slope_sorted; eassumption.

  apply ini_fin_ns_in_init_pts; eassumption.

 apply ini_fin_ns_in_init_pts; eassumption.
Qed.

Lemma cpol_degree : ∀ acf pol cpol ns,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial (ac_field acf) pol ns
    → degree cpol ≥ 1.
Proof.
intros acf pol cpol ns Hns Hpol.
subst cpol.
unfold characteristic_polynomial, degree; simpl.
remember (nofq (fst (ini_pt ns))) as j.
remember (nofq (fst (fin_pt ns))) as k.
remember (k - j)%nat as kj.
destruct kj; simpl.
 eapply j_lt_k with (j := j) in Hns; try eassumption.
 apply NPeano.Nat.sub_gt in Hns.
 symmetry in Heqkj; contradiction.

 rewrite <- Heqj.
 destruct (eq_nat_dec j j) as [| H]; [ apply le_n_S, le_0_n | idtac ].
 exfalso; apply H; reflexivity.
Qed.

Lemma exists_root : ∀ acf pol cpol ns,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial (ac_field acf) pol ns
    → ∃ c, apply_polynomial (ac_field acf) cpol c = zero (ac_field acf).
Proof.
intros acf pol cpol ns Hdeg Hpol.
eapply cpol_degree in Hdeg; [ idtac | eassumption ].
apply (ac_prop acf cpol Hdeg).
Qed.

End field.
