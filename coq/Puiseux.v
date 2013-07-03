(* $Id: Puiseux.v,v 1.809 2013-07-03 14:30:40 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Sorted.
Require Import NPeano.

Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Field.
Require Import Misc.
Require Import Newton.
Require Import Polynomial.
Require Import Puiseux_base.
Require Import Puiseux_series.
Require Import Series.

Set Implicit Arguments.

Definition degree α (pol : polynomial α) := List.length (al pol).
Record term α := { coeff : α; power : Q }.

(* *)

Definition apply_poly_with_ps_poly α (fld : field α) pol :=
  apply_poly
    (λ ps, {| al := []; an := ps |})
    (λ pol ps, pol_add (ps_add fld) pol {| al := []; an := ps |})
    (pol_mul
       {| ps_terms := End _; ps_valnum := 0; ps_comden := 1 |}
       (ps_add fld) (ps_mul fld))
    pol.

Definition mul_x_power_minus α p (ps : puiseux_series α) :=
  {| ps_terms :=
       ps_terms ps;
     ps_valnum :=
       Z.sub (ps_valnum ps) (Qnum (Qmult p (inject_Z (Zpos (ps_comden ps)))));
     ps_comden :=
       ps_comden ps |}.

Definition pol_mul_x_power_minus α p (pol : polynomial (puiseux_series α)) :=
  let cl := List.map (mul_x_power_minus p) (al pol) in
  let cn := mul_x_power_minus p (an pol) in
  {| al := cl; an := cn |}.

Definition zero_is_root α fld (pol : polynomial (puiseux_series α)) :=
  match al pol with
  | [] => false
  | [ps … _] =>
      match series_head (is_zero fld) 0 (ps_terms ps) with
      | Some _ => false
      | None => true
      end
  end.

Definition f₁ α (fld : field α) f β γ c :=
  let y :=
    {| al :=
         [{| ps_terms := Term c (End _);
             ps_valnum := Qnum γ;
             ps_comden := Qden γ |}];
       an :=
         {| ps_terms := Term (one fld) (End _);
            ps_valnum := Qnum γ;
            ps_comden := Qden γ |} |}
  in
  let pol := apply_poly_with_ps_poly fld f y in
  pol_mul_x_power_minus β pol.

(* *)

Definition apply_polynomial α (fld : field α) :=
  apply_poly (λ x, x) (add fld) (mul fld).

Record algeb_closed_field α :=
  { ac_field : field α;
    ac_root : polynomial α → (α * nat);
    ac_prop : ∀ pol, degree pol ≥ 1
      → apply_polynomial ac_field pol (fst (ac_root pol)) = zero ac_field }.

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

Definition puiseux_step α psumo acf (pol : polynomial (puiseux_series α)) :=
  let nsl₁ := newton_segments (ac_field acf) pol in
  let (nsl, psum) :=
    match psumo with
    | Some psum => (List.filter (λ ns, negb (Qle_bool (γ ns) 0)) nsl₁, psum)
    | None => (nsl₁, 0)
    end
  in
  match nsl with
  | [] => None
  | [ns … _] =>
      let fld := ac_field acf in
      let cpol := characteristic_polynomial fld pol ns in
      let (c, r) := ac_root acf cpol in
      let pol₁ := f₁ fld pol (β ns) (γ ns) c in
      let p := Qplus psum (γ ns) in
      Some ({| coeff := c; power := p |}, pol₁)
  end.

CoFixpoint puiseux_loop α psumo acf (pol : polynomial (puiseux_series α)) :=
  match puiseux_step psumo acf pol with
  | Some (t, pol₁) =>
      Term t
        (if zero_is_root (ac_field acf) pol₁ then End _
         else puiseux_loop (Some (power t)) acf pol₁)
  | None =>
      End _
  end.

Fixpoint puiseux_comden α n cd (s : series (term α)) :=
  match n with
  | O => cd
  | S n₁ =>
      match s with
      | Term t ss => puiseux_comden n₁ (Plcm cd (Qden (Qred (power t)))) ss
      | End => cd
      end
  end.

CoFixpoint complete α (zero : α) cd p s :=
  match s with
  | Term t ns =>
      let p₁ := Qplus p (Qmake 1 cd) in
      if Qlt_le_dec p₁ (power t) then
        Term {| coeff := zero; power := p₁ |} (complete zero cd p₁ s)
      else
        Term t ns
  | End =>
      End _
  end.

CoFixpoint term_series_to_coeff_series α zero cd s : series α :=
  match s with
  | Term t ns =>
      Term (coeff t)
        (term_series_to_coeff_series α zero cd
           (complete zero cd (power t) ns))
  | End =>
      End _
  end.

Definition puiseux_root α acf niter (pol : polynomial (puiseux_series α)) :
    puiseux_series α :=
  let s := puiseux_loop None acf pol in
  let cd := puiseux_comden niter 1 s in
  {| ps_terms := term_series_to_coeff_series (zero (ac_field acf)) cd s;
     ps_valnum :=
       match s with
       | Term t _ => Qnum (Qred (Qmult (power t) (Qmake (Zpos cd) 1)))
       | End => 0
       end;
     ps_comden := cd |}.

(*
Definition ps_inv α (add_coeff : α → α → α) mul_coeff x :=
  ...

Definition ps_div α (add_coeff : α → α → α) mul_coeff x y :=
  ps_mul add_coeff mul_coeff x (ps_inv y).
*)

(*
Definition ps_zero α := {| ps_terms := End (term α); ps_comden := 1 |}.
Definition ps_one α fld :=
  {| ps_terms := Term {| coeff := one fld; power := 0 |} (End (term α));
     ps_comden := 1 |}.
Definition ps_add_fld α (fld : field α) x y := ps_add (add fld) x y.
Definition ps_mul_fld α (fld : field α) x y := ps_mul (add fld) (mul fld) x y.

Definition ps_fld α (fld : field α) :=
  {| zero := ps_zero _;
     one := ps_one fld;
     add := ps_add_fld fld;
     mul := ps_mul_fld fld |}.
*)

(* *)

CoFixpoint series_series_take α n (s : series α) :=
  match n with
  | O => End _
  | S n₁ =>
      match s with
      | Term a t => Term a (series_series_take n₁ t)
      | End => End _
      end
  end.

(*
Theorem zzz : ∀ α acf (pol : polynomial (puiseux_series α)) r,
  degree pol ≥ 1
  → r = puiseux_root acf pol
    → apply_polynomial (ps_fld (ac_field acf)) pol r =
      zero (ps_fld (ac_field acf)).
Proof.
intros α acf pol r Hdeg Hr.
subst r.
remember (puiseux_root acf pol) as pr.
remember (ps_terms pr) as sr.
remember (series_hd sr) as shd.
remember (series_tl sr) as stl.
unfold puiseux_root in Heqpr.
rewrite Heqpr in Heqsr.
subst sr; simpl in Heqshd, Heqstl.
remember (puiseux_step None acf pol) as pso.
unfold puiseux_step in Heqpso.
remember (newton_segments pol) as nsl.
destruct nsl.
 subst pso; simpl in Heqshd, Heqstl.
 unfold newton_segments in Heqnsl.
 symmetry in Heqnsl.
 apply list_map_pairs_length in Heqnsl.
 simpl in Heqnsl.
 unfold lower_convex_hull_points in Heqnsl.
bbb.

 Focus 2.
 remember (ac_field acf) as fld.
 remember (characteristic_polynomial fld pol n) as cpol.
 remember (ac_root acf cpol) as cr.
 destruct cr as (c, r).
 subst pso; simpl in Heqshd, Heqstl.
 rewrite surjective_pairing in Heqcr.
 injection Heqcr; clear Heqcr; intros Heqr Heqc.
 destruct r.
  Focus 2.
  subst fld.
  revert pol pr shd stl n nsl cpol c Hdeg Heqpr Heqnsl Heqshd Heqr Heqc
   Heqcpol Heqstl.
  induction r; intros.
   Focus 2.
bbb.
*)

Section field.

Variable α : Type.
Variable acf : algeb_closed_field α.
Variable ps_fld : field (puiseux_series α).
Let fld := ac_field acf.

(* *)

Lemma pt_absc_is_nat : ∀ (pol : puis_ser_pol α) pts pt,
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
 destruct (valuation fld cn) as [v| ].
  subst pts.
  destruct Hαh as [Hαh| ]; [ subst pt; simpl | contradiction ].
  exists n; reflexivity.

  subst pts; contradiction.

 simpl in Hpts.
 destruct (valuation fld c) as [v| ].
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

Lemma cpol_degree : ∀ (pol : puis_ser_pol α) cpol ns,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial fld pol ns
    → degree cpol ≥ 1.
Proof.
intros pol cpol ns Hns Hpol.
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

Lemma exists_root : ∀ (pol : puis_ser_pol α) cpol ns,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial fld pol ns
    → ∃ c, apply_polynomial fld cpol c = zero fld.
Proof.
intros pol cpol ns Hdeg Hpol.
eapply cpol_degree in Hdeg; [ idtac | eassumption ].
remember (ac_root acf cpol) as r.
destruct r as (c, r).
exists c.
rewrite surjective_pairing in Heqr.
injection Heqr; clear Heqr; intros; subst c.
apply (ac_prop acf cpol Hdeg).
Qed.

(* *)

Definition comden_prod α (psl : list (puiseux_series α)) :=
  List.fold_right (λ ps a, Pos.mul a (ps_comden ps)) 1%positive psl.

Lemma common_denominator_of_series_list :
  ∀ (psl : list (puiseux_series α)),
  ∃ m, ∀ ps αi, ps ∈ psl
  → valuation fld ps = Some αi
    → ∃ mi, αi == mi # m.
Proof.
intros psl.
remember (comden_prod psl) as m.
exists m.
intros ps αi Hps Hv.
apply List.in_split in Hps.
destruct Hps as (l₁, (l₂, Hpsl)).
remember (comden_prod (l₁ ++ l₂)) as m₁.
exists (Qnum αi * Zpos m₁)%Z.
subst m m₁ psl.
induction l₁ as [| ps₁]; simpl.
 unfold Qeq; simpl.
 rewrite Pos2Z.inj_mul.
 rewrite Zmult_assoc.
 unfold valuation in Hv.
 destruct (series_head (is_zero fld) 0 (ps_terms ps)) as [(n, _)| ].
  injection Hv; clear Hv; intros Hαi.
  subst αi; reflexivity.

  discriminate Hv.

 rewrite Pos2Z.inj_mul, Zmult_assoc.
 unfold Qeq; simpl.
 rewrite Pos2Z.inj_mul.
 rewrite Zmult_assoc, Zmult_comm, <- Zmult_assoc.
 symmetry; rewrite Zmult_comm, <- Zmult_assoc.
 apply Z.mul_cancel_l; [ apply Zpos_ne_0 | idtac ].
 rewrite Zmult_comm; symmetry; assumption.
Qed.

Lemma gamma_value : ∀ hsl ns j k αj αk,
  ns ∈ list_map_pairs newton_segment_of_pair hsl
  → j = fst (ini_pt ns)
    → k = fst (fin_pt ns)
      → αj = snd (ini_pt ns)
        → αk = snd (fin_pt ns)
          → γ ns = (αj - αk) / (k - j).
Proof.
intros hsl ns j k αj αk Hns Hj Hk Hαj Hαk.
induction hsl as [| ((x₁, y₁), seg)]; [ contradiction | idtac ].
destruct hsl as [| ((x₂, y₂), seg₂)]; [ contradiction | idtac ].
rewrite list_map_pairs_cons_cons in Hns.
destruct Hns as [Hns| Hns].
 subst ns.
 simpl in Hj, Hk, Hαj, Hαk |- *.
 subst x₁ y₁ x₂ y₂.
 reflexivity.

 apply IHhsl; assumption.
Qed.

Lemma xxx : ∀ pow cl cn pts psl h hps def,
  pts = filter_non_zero_ps fld (all_points_of_ps_polynom pow cl cn)
  → psl = cl ++ [cn]
    → (h, hps) ∈ pts
      → List.nth (Z.to_nat (Qnum h) - pow) psl def ∈ psl.
Proof.
fix IH 2.
intros pow cl cn pts psl h hps def Hpts Hpsl Hhps.
destruct cl as [| c].
 destruct pow.
  simpl in Hpts.
  subst pts.
  destruct (valuation fld cn) as [v| ].
   destruct Hhps as [Hhps| ]; [ idtac | contradiction ].
   injection Hhps; clear Hhps; intros; subst h v.
   subst psl; left; reflexivity.

   contradiction.

  simpl in Hpts.
  destruct (valuation fld cn) as [v| ].
   subst pts.
   destruct Hhps as [Hhps| ]; [ idtac | contradiction ].
   injection Hhps; clear Hhps; intros; subst h v.
   simpl.
   rewrite SuccNat2Pos.id_succ, minus_diag.
   subst psl; left; reflexivity.

   subst pts; contradiction.

 simpl in Hpts.
 destruct (valuation fld c) as [v| ].
  subst pts.
  destruct Hhps as [Hhps| Hhps].
   injection Hhps; clear Hhps; intros; subst h v.
   simpl.
   rewrite Nat2Z.id, minus_diag.
   subst psl; left; reflexivity.

   simpl in Hpsl.
   remember (cl ++ [cn]) as psl₁.
   subst psl.
   destruct cl as [| c₁].
    simpl in Hhps.
    destruct (valuation fld cn) as [u| ]; [ idtac | contradiction ].
    destruct Hhps as [Hhps| ]; [ idtac | contradiction ].
    injection Hhps; clear Hhps; intros; subst h u.
    remember [c … psl₁] as x; simpl; subst x.
    rewrite SuccNat2Pos.id_succ, minus_Sn_n.
    subst psl₁; right; left; reflexivity.

    simpl in Hhps.
    destruct (valuation fld c₁) as [u| ].
     destruct Hhps as [Hhps| Hhps].
      injection Hhps; clear Hhps; intros; subst h u.
      remember [c … psl₁] as x; simpl; subst x.
      rewrite SuccNat2Pos.id_succ, minus_Sn_n.
      subst psl₁; right; left; reflexivity.

      destruct cl as [| c₂].
       simpl in Hhps.
       destruct (valuation fld cn) as [u₂| ]; [ idtac | contradiction ].
       destruct Hhps as [Hhps| ]; [ idtac | contradiction ].
       injection Hhps; clear Hhps; intros; subst h u₂.
       remember [c … psl₁] as x; simpl; subst x.
       rewrite <- SuccNat2Pos.inj_succ, SuccNat2Pos.id_succ.
       rewrite <- minus_Sn_m; [ rewrite minus_Sn_n | apply le_n_Sn ].
       subst psl₁; right; right; left; reflexivity.

       simpl in Hhps.
       destruct (valuation fld c₂) as [u₂| ].
        destruct Hhps as [Hhps| Hhps].
         injection Hhps; clear Hhps; intros; subst h u₂.
         remember [c … psl₁] as x; simpl; subst x.
         rewrite <- SuccNat2Pos.inj_succ, SuccNat2Pos.id_succ.
         rewrite <- minus_Sn_m; [ rewrite minus_Sn_n | apply le_n_Sn ].
         subst psl₁; right; right; left; reflexivity.

         destruct cl as [| c₃].
          simpl in Hhps.
          destruct (valuation fld cn) as [u₃| ]; [ idtac | contradiction ].
          destruct Hhps as [Hhps| ]; [ idtac | contradiction ].
          injection Hhps; clear Hhps; intros; subst h u₃.
          remember [c … psl₁] as x; simpl; subst x.
          do 2 rewrite <- SuccNat2Pos.inj_succ.
          rewrite SuccNat2Pos.id_succ.
          rewrite <- minus_Sn_m; [ idtac | eapply le_trans; eapply le_n_Sn ].
          rewrite <- minus_Sn_m; [ rewrite minus_Sn_n | apply le_n_Sn ].
          subst psl₁; right; right; right; left; reflexivity.

          simpl in Hhps.
          destruct (valuation fld c₃) as [u₃| ].
           destruct Hhps as [Hhps| Hhps].
            injection Hhps; clear Hhps; intros; subst h u₃.
            remember [c … psl₁] as x; simpl; subst x.
            do 2 rewrite <- SuccNat2Pos.inj_succ.
            rewrite SuccNat2Pos.id_succ.
            rewrite <- minus_Sn_m;
             [ idtac | eapply le_trans; eapply le_n_Sn ].
            rewrite <- minus_Sn_m; [ rewrite minus_Sn_n | apply le_n_Sn ].
            subst psl₁; right; right; right; left; reflexivity.
bbb.

Lemma yyy : ∀ pol pts psl h hps def,
  pts = points_of_ps_polynom fld pol
  → psl = al pol ++ [an pol]
    → (h, hps) ∈ pts
      → List.nth (Z.to_nat (Qnum h)) psl def ∈ psl.
Proof.
intros pol pts psl h hps def Hpts Hpsl Hhps.
unfold points_of_ps_polynom in Hpts.
unfold points_of_ps_polynom_gen in Hpts.
bbb.
fix IHpsl 3.
intros pol pts psl h hps def Hpts Hpsl Hhps.
destruct psl as [| ps].
 symmetry in Hpsl.
 apply List.app_eq_nil in Hpsl.
 destruct Hpsl as (_, H); discriminate H.
bbb.

Lemma zzz : ∀ pol ns,
  ns ∈ newton_segments fld pol
  → ∃ m p q,
    γ ns == p # (m * q) ∧ Z.gcd p (' q) = 1%Z.
Proof.
intros pol ns Hns.
unfold newton_segments in Hns.
remember (points_of_ps_polynom fld pol) as pts.
remember (lower_convex_hull_points pts) as hsl.
remember (fst (ini_pt ns)) as j.
remember (fst (fin_pt ns)) as k.
remember (snd (ini_pt ns)) as αj.
remember (snd (fin_pt ns)) as αk.
remember Hns as Hg; clear HeqHg.
eapply gamma_value in Hg; try eassumption.
remember (al pol ++ [an pol]) as psl.
pose proof (common_denominator_of_series_list psl) as Hi.
destruct Hi as (m, Hi).
exists m.
remember (List.nth (Z.to_nat (Qnum j)) psl (an pol)) as psj.
assert (psj ∈ psl) as Hpsj.
 subst psj.
 remember Hns as Hpts; clear HeqHpts.
 rewrite Heqhsl in Hpts.
 apply ini_fin_ns_in_init_pts in Hpts.
 destruct Hpts as (Hini, Hfin).
 subst j.
bbb.

Theorem has_neg_slope : ∀ pol ns cpol (c : α) r pol₁,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial fld pol ns
    → (c, r) = ac_root acf cpol
      → pol₁ = f₁ fld pol (β ns) (γ ns) c
        → ∃ ns₁, ns₁ ∈ newton_segments fld pol₁ → γ ns₁ > 0.
Proof.
bbb.

End field.
