(* $Id: Puiseux.v,v 1.554 2013-05-30 14:03:12 deraugla Exp $ *)

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

Inductive monom_search α :=
  | Found : ps_monomial α → monom_search α
  | Remaining : monom_search α
  | Ended : monom_search α.

Fixpoint find_monom α p (s : series (ps_monomial α)) n :=
  match n with
  | O => Ended _
  | S n₁ =>
      match s with
      | Term t s₁ =>
          match Qcompare (power t) p with
          | Eq => Found t
          | Lt => find_monom p s₁ n₁
          | Gt => Remaining _
          end
      | End =>
         Ended _
      end
  end.

Definition scan_diag α (add_coeff : α → α → α) (mul_coeff : α → α → α)
    minp₁c minp₂c comden s₁ s₂ :=
  let fix loop_ij i j :=
    let p₁ := (minp₁c + Z.of_nat i)%Z in
    let p₂ := (minp₂c + Z.of_nat j)%Z in
    let m₁o := find_monom (p₁ # Pos.of_nat comden) s₁ (S i) in
    let m₂o := find_monom (p₂ # Pos.of_nat comden) s₂ (S j) in
    let ms₁ :=
      match m₁o with
      | Found m₁ =>
          match m₂o with
          | Found m₂ =>
              let c := mul_coeff (coeff m₁) (coeff m₂) in
              let p := Qplus (power m₁) (power m₂) in
              Found {| coeff := c; power := p |}
          | Remaining => Remaining _
          | Ended => Ended _
          end
      | Remaining =>
          match m₂o with
          | Found _ => Remaining _
          | Remaining => Remaining _
          | Ended => Ended _
          end
      | Ended => Ended _
      end
    in
    match j with
    | O => ms₁
    | S j₁ =>
        let ms₂ := loop_ij (S i) j₁ in
        match ms₁ with
        | Found m₁ =>
            match ms₂ with
            | Found m₂ =>
                let c := add_coeff (coeff m₁) (coeff m₂) in
                Found {| coeff := c; power := power m₁ |}
            | Remaining => ms₁
            | Ended => ms₁
            end
        | Remaining =>
            match ms₂ with
            | Found _ => ms₂
            | Remaining => Remaining _
            | Ended => Remaining _
            end
        | Ended => ms₂
        end
    end
  in
  loop_ij.

Record fifo_elem α :=
  { fe_i : nat; fe_j : nat; fe_c : α; fe_p : Q;
    fe_s₁ : series (ps_monomial α); fe_s₂ : series (ps_monomial α) }.

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

Fixpoint insert_sum α sum (fe : fifo_elem α) sl :=
  match sl with
  | [] => [(sum, [fe])]
  | [(sum₁, fel₁) … l] =>
      match nat_compare sum sum₁ with
      | Eq => [(sum₁, insert_ij fe fel₁) … l]
      | Lt => [(sum, [fe]) … sl]
      | Gt => [(sum₁, fel₁) … insert_sum sum fe l]
      end
  end.

Definition insert_point mul_coeff comden i j s₁ s₂ sl :=
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

Definition map_option {α β} (n : β) (s : α → β) v :=
  match v with
  | None => n
  | Some x => s x
  end.

Definition new_ps_mul α add_coeff mul_coeff (ps₁ ps₂ : puiseux_series α) :=
  let s₁ := ps_terms ps₁ in
  let s₂ := ps_terms ps₂ in
  let comden := (ps_comden ps₁ * ps_comden ps₂)%nat in
  let minp₁ := map_option 0 (λ ps, power ps) (ser_nth 0 s₁) in
  let minp₂ := map_option 0 (λ ps, power ps) (ser_nth 0 s₂) in
  let p₁c := Qnum (minp₁ * Qnat comden) in
  let p₂c := Qnum (minp₂ * Qnat comden) in
  let t :=
    let cofix loop_sum psum :=
      let cp_o := scan_diag add_coeff mul_coeff p₁c p₂c comden s₁ s₂ 0 psum in
      match cp_o with
      | Ended => End _
      | Remaining => End _ (* loop_sum (S psum) *)
      | Found m => Term m (loop_sum (S psum))
      end
    in
    loop_sum O
  in
  {| ps_terms := t; ps_comden := comden |}.

(*
Definition apply_poly_with_ps {α} fld pol (x : α) := ...
value apply_poly_with_ps :
  field α β →
  pps α → puiseux_series α → puiseux_series α
value apply_poly_with_ps k pol =
  apply_poly {ps_terms = []}
    (fun ps → ps_add (norm k.add k) (k.eq k.zero) ps)
    (ps_mul (norm k.add k) (norm k.mul k) (k.eq k.zero)) pol
*)

(*
Definition apply_poly_with_ps_poly {α} (fld : field α)
    (pol : pps α) :=
  apply_poly (λ x, x)
    (λ (pol : pps α) (ps : puiseux_series α),
       pol_add (ps_add (add fld) (is_zero fld)) pol (mkpol [] ps)).
*)
(*
value apply_poly_with_ps_poly :
  field α β →
  pps α → pps α →
  pps α
value apply_poly_with_ps_poly k pol =
  apply_poly
    {ml = []}    
    (fun pol ps →
       pol_add (ps_add k.add (k.eq k.zero)) pol {ml = [ps]})
    (pol_mul
       {ps_terms = []}
       (ps_add k.add (k.eq k.zero))
       (ps_mul k.add (norm k.mul k) (k.eq k.zero))
       (fun ps → ps.ps_terms = []))
    pol
*)

Definition apply_polynomial {α} fld pol (x : α) :=
  List.fold_right (λ coeff accu, add fld (mul fld accu x) coeff) (an pol)
    (al pol).

Record alg_closed_field {α} :=
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

Lemma pt_absc_is_nat : ∀ (pol : pps α) pts pt,
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
 destruct (Qeq_bool (valuation cn) qinf) as [Hz| Hnz].
  subst pts; contradiction.

  subst pts.
  destruct Hαh as [Hαh| ]; [ subst pt; simpl | contradiction ].
  exists n; reflexivity.

 simpl in Hpts.
 destruct (Qeq_bool (valuation c) qinf) as [Hz| Hnz].
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

Lemma j_lt_k : ∀ (pol : pps α) j k ns,
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

Lemma cpol_degree : ∀ acf (pol : pps α) cpol ns,
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

Lemma exists_root : ∀ acf (pol : pps α) cpol ns,
  ns ∈ newton_segments pol
  → cpol = characteristic_polynomial (ac_field acf) pol ns
    → ∃ c, apply_polynomial (ac_field acf) cpol c = zero (ac_field acf).
Proof.
intros acf pol cpol ns Hdeg Hpol.
eapply cpol_degree in Hdeg; [ idtac | eassumption ].
apply (ac_prop acf cpol Hdeg).
Qed.

End field.
