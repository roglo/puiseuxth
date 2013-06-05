(* $Id: Puiseux.v,v 1.581 2013-06-05 16:32:33 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Sorted.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Puiseux_base.
Require Import Misc.
Require Import Lcm.
Require Import Series.

Set Implicit Arguments.

Definition degree α (pol : polynomial α) := List.length (al pol).

(* Horner's algorithm *)
Definition apply_poly α β γ
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

Definition ps_add α (add_coeff : α → α → α) (ps₁ : puiseux_series α)
    (ps₂ : puiseux_series α) :=
  let cofix loop ms₁ ms₂ :=
    match ms₁ with
    | Term c₁ s₁ =>
        let cofix loop₁ ms₂ :=
          match ms₂ with
          | Term c₂ s₂ =>
              match Qcompare (power c₁) (power c₂) with
              | Eq =>
                  let c := add_coeff (coeff c₁) (coeff c₂) in
                  let m := {| coeff := c; power := power c₁ |} in
                  Term m (loop s₁ s₂)
              | Lt =>
                  Term c₁ (loop s₁ ms₂)
              | Gt =>
                  Term c₂ (loop₁ s₂)
              end
          | End => ms₁
          end
        in
        loop₁ ms₂
    | End => ms₂
    end
  in
  {| ps_terms := loop (ps_terms ps₁) (ps_terms ps₂);
     ps_comden := lcm (ps_comden ps₁) (ps_comden ps₂) |}.

Record fifo_elem α :=
  { fe_i : nat; fe_j : nat; fe_c : α; fe_p : Q;
    fe_s₁ : series (term α); fe_s₂ : series (term α) }.

Fixpoint insert_ij α (fe : fifo_elem α) fel :=
  match fel with
  | [] => [fe]
  | [fe₁ … fel₁] =>
      if lt_dec (fe_i fe) (fe_i fe₁) then [fe … fel]
      else if gt_dec (fe_i fe) (fe_i fe₁) then [fe₁ … insert_ij fe fel₁]
      else if lt_dec (fe_j fe) (fe_j fe₁) then [fe … fel]
      else if gt_dec (fe_j fe) (fe_j fe₁) then [fe₁ … insert_ij fe fel₁]
      else fel
  end.

Definition bnat_compare := nat_compare.

Fixpoint insert_sum α sum (fe : fifo_elem α) sl :=
  match sl with
  | [] => [(sum, [fe])]
  | [(sum₁, fel₁) … l] =>
      match bnat_compare sum sum₁ with
      | Eq => [(sum₁, insert_ij fe fel₁) … l]
      | Lt => [(sum, [fe]) … sl]
      | Gt => [(sum₁, fel₁) … insert_sum sum fe l]
      end
  end.

Definition sum_int_powers α comden (m₁ m₂ : term α) :=
  let q := Qred (Qmult (Qplus (power m₁) (power m₂)) (Qnat comden)) in
  Z.to_nat (Qnum q).

Definition insert_term α (mul_coeff : α → α → α) comden i j s₁ s₂ sl :=
  match (s₁, s₂) with
  | (Term m₁ _, Term m₂ _) =>
      let c := mul_coeff (coeff m₁) (coeff m₂) in
      let p := Qplus (power m₁) (power m₂) in
      insert_sum (sum_int_powers comden m₁ m₂)
        {| fe_i := i; fe_j := j; fe_c := c; fe_p := p;
           fe_s₁ := s₁; fe_s₂ := s₂ |}
        sl
  | _ => sl
  end.

Fixpoint add_coeff_list α (add_coeff : α → α → α) c₁ fel₁ :=
  match fel₁ with
  | [] => c₁
  | [fe … fel] => add_coeff c₁ (add_coeff_list add_coeff (fe_c fe) fel)
  end.

CoFixpoint series_mul α add_coeff mul_coeff comden sum_fifo :
    series (term α) :=
  match sum_fifo with
  | [] => End _
  | [(sum, []) … sl] => End _
  | [(sum, [fe₁ … fel₁]) … sl] =>
      let m :=
        let c := add_coeff_list add_coeff (fe_c fe₁) fel₁ in
        {| coeff := c; power := fe_p fe₁ |}
      in
      let sl₁ :=
        List.fold_left
          (λ sl₁ fe,
             match fe_s₁ fe with
             | Term _ ls₁ =>
                 insert_term mul_coeff comden (S (fe_i fe)) (fe_j fe)
                   ls₁ (fe_s₂ fe) sl₁
             | End => sl₁
             end)
          [fe₁ … fel₁] sl
      in
      let sl₂ :=
        List.fold_left
          (λ sl₂ fe,
             match fe_s₂ fe with
             | Term _ ls₂ =>
                 insert_term mul_coeff comden (fe_i fe) (S (fe_j fe))
                   (fe_s₁ fe) ls₂ sl₂
             | End => sl₂
             end)
          [fe₁ … fel₁] sl₁
      in
      Term m (series_mul α add_coeff mul_coeff comden sl₂)
  end.

Definition ps_mul α add_coeff mul_coeff (ps₁ ps₂ : puiseux_series α) :=
  let s₁ := ps_terms ps₁ in
  let s₂ := ps_terms ps₂ in
  let comden := mult (ps_comden ps₁) (ps_comden ps₂) in
  let t :=
    match s₁ with
    | Term m₁ _ =>
        match s₂ with
        | Term m₂ _ =>
            let c := mul_coeff (coeff m₁) (coeff m₂) in
            let p := Qred (Qplus (power m₁) (power m₂)) in
            let fe :=
              {| fe_i := 0; fe_j := 0; fe_c := c; fe_p := p;
                 fe_s₁ := s₁; fe_s₂ := s₂ |}
            in
            series_mul add_coeff mul_coeff comden
              [(sum_int_powers comden m₁ m₂, [fe])]
        | End => End _
        end
    | End => End _
    end
  in
  {| ps_terms := t; ps_comden := comden |}.

Fixpoint insert_pol_term α (add_coeff : α → α → α) c₁ p₁ ml :=
  match ml with
  | [] => [(c₁, p₁)]
  | [(c₂, p₂) … ml₂] =>
      match nat_compare p₁ p₂ with
      | Eq => [(add_coeff c₁ c₂, p₂) … ml₂]
      | Lt => [(c₁, p₁) … ml]
      | Gt => [(c₂, p₂) … insert_pol_term add_coeff c₁ p₁ ml₂]
      end
  end.

Fixpoint combine_pol α add_coeff (mul_coeff : α → α → α) c₁ pow₁ pow₂ ml
    cn cl :=
  let p := (pow₁ + pow₂)%nat in
  match cl with
  | [] =>
      let c := mul_coeff c₁ cn in
      insert_pol_term add_coeff c p ml
  | [c₂ … cl₂] =>
      let c := mul_coeff c₁ c₂ in
      let ml := insert_pol_term add_coeff c p ml in
      combine_pol add_coeff mul_coeff c₁ pow₁ (S pow₂) ml cn cl₂
  end.

Fixpoint mul_loop α (add_coeff : α → α → α) mul_coeff ml pow₁ cn₂ cl₂
    cn₁ cl₁ :=
  match cl₁ with
  | [] => combine_pol add_coeff mul_coeff cn₁ pow₁ 0 ml cn₂ cl₂
  | [c … cl] =>
      let ml := combine_pol add_coeff mul_coeff c pow₁ 0 ml cn₂ cl₂ in
      mul_loop add_coeff mul_coeff ml (S pow₁) cn₂ cl₂ cn₁ cl
  end.

Fixpoint make_pol α (zero_coeff : α) pow ml n :=
  match n with
  | O => ([], zero_coeff)
  | S n₁ =>
      match ml with
      | [] => ([], zero_coeff)
      | [(c, p)] =>
          if eq_nat_dec p pow then ([], c)
          else
            let (cl, cn) := make_pol zero_coeff (S pow) [(c, p)] n₁ in
            ([zero_coeff … cl], cn)
      | [(c, p) … ml₁] =>
          if eq_nat_dec p pow then
            let (cl, cn) := make_pol zero_coeff (S pow) ml₁ n₁ in
            ([c … cl], cn)
          else
            let (cl, cn) := make_pol zero_coeff (S pow) ml n₁ in
            ([zero_coeff … cl], cn)
      end
  end.

Definition pol_mul α (zero_coeff : α) add_coeff mul_coeff pol₁ pol₂ :=
  let ml :=
    mul_loop add_coeff mul_coeff [] 0 (an pol₂) (al pol₂) (an pol₁) (al pol₁)
  in
  let (cl, cn) := make_pol zero_coeff 0 ml (List.length ml) in
  {| al := cl; an := cn |}.

Definition apply_poly_with_ps_poly α (fld : field α) pol :=
  apply_poly
    (λ ps, {| al := []; an := ps |})
    (λ pol ps, pol_add (ps_add (add fld)) pol {| al := []; an := ps |})
    (pol_mul
       {| ps_terms := End _; ps_comden := 1 |}
       (ps_add (add fld))
       (ps_mul (add fld) (mul fld)))
    pol.

Definition mul_x_power_minus α p (ps : puiseux_series α) :=
  let t :=
    series_map
      (λ m, {| coeff := coeff m; power := Qred (Qminus (power m) p) |})
      (ps_terms ps)
  in
  {| ps_terms := t; ps_comden := ps_comden ps |}.

Definition pol_mul_x_power_minus α p (pol : polynomial (puiseux_series α)) :=
  let cl := List.map (mul_x_power_minus p) (al pol) in
  let cn := mul_x_power_minus p (an pol) in
  {| al := cl; an := cn |}.

Definition pos_to_nat := Pos.to_nat.

Definition f₁ α (fld : field α) (f : polynomial (puiseux_series α)) β γ c :=
  let y :=
    {| al :=
         [{| ps_terms := Term {| coeff := c; power := γ |} (End _);
             ps_comden := pos_to_nat (Qden γ) |}];
       an :=
         {| ps_terms := Term {| coeff := one fld; power := γ |} (End _);
            ps_comden := pos_to_nat (Qden γ) |} |}
  in
  let pol := apply_poly_with_ps_poly fld f y in
  pol_mul_x_power_minus β pol.

(* *)

Definition apply_polynomial α (fld : field α) :=
  apply_poly (λ x, x) (add fld) (mul fld).

Record algeb_closed_field α :=
  { ac_field : field α;
    ac_root : polynomial α → α;
    ac_prop : ∀ pol, degree pol ≥ 1
      → apply_polynomial ac_field pol (ac_root pol) = zero ac_field }.

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

Definition zero_is_root α (pol : polynomial (puiseux_series α)) :=
  match al pol with
  | [] => false
  | [ps … _] =>
      match series_head (ps_terms ps) with
      | Term _ _ => false
      | End => true
      end
  end.

CoFixpoint puiseux_loop α psumo acf (pol : polynomial (puiseux_series α)) :=
  let nsl₁ := newton_segments pol in
  let (nsl, psum) :=
    match psumo with
    | Some psum => (List.filter (λ ns, negb (Qle_bool (γ ns) 0)) nsl₁, psum)
    | None => (nsl₁, 0)
    end
  in
  match nsl with
  | [] => End _
  | [ns … _] =>
      let fld := ac_field acf in
      let cpol := characteristic_polynomial fld pol ns in
      let c := ac_root acf cpol in
      let pol₁ := f₁ fld pol (β ns) (γ ns) c in
      let p := Qplus psum (γ ns) in
      Term {| coeff := c; power := p |}
        (if zero_is_root pol₁ then End _ else puiseux_loop (Some p) acf pol₁)
  end.

Definition puiseux_root α := @puiseux_loop α None.

(* *)

Section field.

Variable α : Type.
Variable fld : field (puiseux_series α).

Lemma pt_absc_is_nat : ∀ (pol : puis_ser_pol α) pts pt,
  points_of_ps_polynom pol = pts
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
 destruct (valuation cn) as [v| ].
  subst pts.
  destruct Hαh as [Hαh| ]; [ subst pt; simpl | contradiction ].
  exists n; reflexivity.

  subst pts; contradiction.

 simpl in Hpts.
 destruct (valuation c) as [v| ].
  subst pts.
  destruct Hαh as [Hαh| Hαh]; [ subst pt; simpl | idtac ].
   exists n; reflexivity.

   eapply IHcl in Hαh; [ assumption | reflexivity ].

  eapply IHcl; eassumption.
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

Lemma j_lt_k : ∀ (pol : puis_ser_pol α) j k ns,
  ns ∈ newton_segments pol
  → j = nofq (fst (ini_pt ns))
    → k = nofq (fst (fin_pt ns))
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

Lemma cpol_degree : ∀ acf (pol : puis_ser_pol α) cpol ns,
  ns ∈ newton_segments pol
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

Lemma exists_root : ∀ acf (pol : puis_ser_pol α) cpol ns,
  ns ∈ newton_segments pol
  → cpol = characteristic_polynomial (ac_field acf) pol ns
    → ∃ c, apply_polynomial (ac_field acf) cpol c = zero (ac_field acf).
Proof.
intros acf pol cpol ns Hdeg Hpol.
eapply cpol_degree in Hdeg; [ idtac | eassumption ].
remember (ac_root acf cpol) as r.
exists r; subst r.
apply (ac_prop acf cpol Hdeg).
Qed.

End field.
