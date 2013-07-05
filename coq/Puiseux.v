(* $Id: Puiseux.v,v 1.842 2013-07-05 19:18:50 deraugla Exp $ *)

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

Lemma first_power_le : ∀ pow cl cn h hv,
  (h, hv) ∈ filter_finite_val fld (power_list pow cl cn)
  → pow ≤ Z.to_nat (Qnum h).
Proof.
intros pow cl cn h hv Hhhv.
revert pow Hhhv.
induction cl as [| c]; intros.
 simpl in Hhhv.
 remember (valuation fld cn) as v.
 symmetry in Heqv.
 destruct v as [v| ]; [ idtac | contradiction ].
 destruct Hhhv as [Hhhv| ]; [ idtac | contradiction ].
 injection Hhhv; clear Hhhv; intros; subst h v.
 simpl; rewrite Nat2Z.id; constructor.

 simpl in Hhhv.
 remember (valuation fld c) as v.
 symmetry in Heqv.
 destruct v as [v| ].
  destruct Hhhv as [Hhhv| Hhhv].
   injection Hhhv; clear Hhhv; intros; subst h v.
   simpl; rewrite Nat2Z.id; constructor.

   apply IHcl in Hhhv.
   eapply le_trans; [ apply le_n_Sn | eassumption ].

  apply IHcl in Hhhv.
  eapply le_trans; [ apply le_n_Sn | eassumption ].
Qed.

Lemma in_pts_in_ppl : ∀ pow cl cn ppl pts h hv hps def,
  ppl = power_list pow cl cn
  → pts = filter_finite_val fld ppl
    → (h, hv) ∈ pts
      → hps = List.nth (Z.to_nat (Qnum h) - pow) (cl ++ [cn]) def
        → (h, hps) ∈ ppl ∧ valuation fld hps = Some hv.
Proof.
intros pow cl cn ppl pts h hv hps def Hppl Hpts Hhhv Hhps.
subst ppl pts.
revert pow cn h hv hps Hhps Hhhv.
induction cl as [| c]; intros.
 simpl in Hhhv.
 remember (valuation fld cn) as v.
 symmetry in Heqv.
 destruct v as [v| ]; [ idtac | contradiction ].
 destruct Hhhv as [Hhhv| ]; [ idtac | contradiction ].
 injection Hhhv; clear Hhhv; intros; subst v h.
 remember (Qnum (Qnat pow)) as x; simpl in Heqx; subst x.
 rewrite Nat2Z.id, minus_diag in Hhps.
 simpl in Hhps; subst hps.
 split; [ left; reflexivity | assumption ].

 simpl in Hhhv.
 remember (valuation fld c) as v.
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

Lemma in_pts_in_psl : ∀ pow cl cn pts psl h hv hps def,
  pts = filter_finite_val fld (power_list pow cl cn)
  → psl = cl ++ [cn]
    → (h, hv) ∈ pts
      → hps = List.nth (Z.to_nat (Qnum h) - pow) psl def
        → hps ∈ psl ∧ valuation fld hps = Some hv.
Proof.
intros pow cl cn pts psl h hv hps def Hpts Hpsl Hhv Hhps.
remember (power_list pow cl cn) as ppl.
subst psl.
assert (pow ≤ Z.to_nat (Qnum h)) as H.
 subst pts ppl.
 eapply first_power_le; eassumption.

 eapply in_pts_in_ppl in Hhv; try eassumption.
 destruct Hhv as (Hhps₁, Hv).
 split; [ idtac | assumption ].
 subst ppl.
 revert pow cn pts h hv hps Hhps Hv Hhps₁ Hpts H.
 induction cl as [| c]; intros.
  destruct Hhps₁ as [Hhps₁| ]; [ idtac | contradiction ].
  injection Hhps₁; clear Hhps₁; intros; subst h hps.
  left; reflexivity.

  destruct Hhps₁ as [Hhps₁| Hhps₁].
   injection Hhps₁; clear Hhps₁; intros; subst h hps.
   left; reflexivity.

   destruct (eq_nat_dec (Z.to_nat (Qnum h)) pow) as [Heq| Hne].
    rewrite Heq, minus_diag in Hhps.
    subst hps; left; reflexivity.

    right.
    eapply IHcl; try eassumption; try reflexivity.
     rewrite <- Nat.sub_succ in Hhps.
     rewrite <- minus_Sn_m in Hhps; [ assumption | idtac ].
     apply not_eq_sym in Hne.
     apply le_neq_lt; assumption.

     apply not_eq_sym in Hne.
     apply le_neq_lt; assumption.
Qed.

Lemma in_pts_in_pol : ∀ pol pts psl h hv hps def,
  pts = points_of_ps_polynom fld pol
  → psl = al pol ++ [an pol]
    → (h, hv) ∈ pts
      → hps = List.nth (Z.to_nat (Qnum h)) psl def
        → hps ∈ psl ∧ valuation fld hps = Some hv.
Proof.
intros pol pts psl h hv hps def Hpts Hpsl Hhhv Hhps.
eapply in_pts_in_psl; try eassumption.
rewrite <- minus_n_O; eassumption.
Qed.

Lemma Qnum_inv : ∀ a, (0 < Qnum a)%Z → Qnum (/ a) = Zpos (Qden a).
Proof.
intros (a, b) Ha; simpl in Ha |- *.
unfold Qinv; simpl.
destruct a as [| a| a]; simpl.
 apply Zlt_irrefl in Ha; contradiction.

 reflexivity.

 apply Zlt_not_le in Ha.
 exfalso; apply Ha, Zlt_le_weak, Zlt_neg_0.
Qed.

Lemma Qden_inv : ∀ a, (0 < Qnum a)%Z → Zpos (Qden (/ a)) = Qnum a.
Proof.
intros (a, b) Ha; simpl in Ha |- *.
unfold Qinv; simpl.
destruct a as [| a| a]; simpl.
 apply Zlt_irrefl in Ha; contradiction.

 reflexivity.

 apply Zlt_not_le in Ha.
 exfalso; apply Ha, Zlt_le_weak, Zlt_neg_0.
Qed.

Lemma Qdiv_mul : ∀ a b c d,
  a ≠ 0%Z
  → (0 < c)%Z
    → (a # b) / (c # d) == a * Zpos d # b * Z.to_pos c.
Proof.
intros a b c d Ha Hc.
unfold Qeq; simpl.
do 2 rewrite Pos2Z.inj_mul.
rewrite Z.mul_shuffle1; symmetry.
rewrite Z.mul_shuffle1.
apply Z.mul_cancel_l.
 apply Z.neq_mul_0.
 split; [ assumption | apply Zpos_ne_0 ].

 rewrite Qden_inv; [ idtac | assumption ].
 rewrite Qnum_inv; [ idtac | assumption ].
 remember Zmult as f; simpl; subst f.
 apply Z.mul_cancel_l; [ apply Zpos_ne_0 | idtac ].
 symmetry; apply Z2Pos.id; assumption.
Qed.

Lemma yyy : ∀ m j k mj mk g,
  (0 < k - j)%Z
  → g = Z.gcd (mj - mk) (k - j)
    → ((mj # m) - (mk # m)) / ((k # 1) - (j # 1)) ==
       (mj - mk) / g # m * Z.to_pos ((k - j) / g).
Proof.
intros m j k mj mk g Hkj Hg.
setoid_replace ((mj # m) - (mk # m)) with (mj - mk # m).
 Focus 2.
 unfold Qeq; simpl.
 rewrite Zmult_minus_distr_r.
 rewrite Zmult_plus_distr_l.
 rewrite Pos2Z.inj_mul.
 do 2 rewrite Zmult_assoc.
 do 2 rewrite Z.mul_opp_l.
 reflexivity.

 setoid_replace ((k # 1) - (j # 1)) with (k - j # 1).
  Focus 2.
  unfold Qeq; simpl.
  do 4 rewrite Zmult_1_r.
  reflexivity.

  destruct (Z.eq_dec (mj - mk) 0)%Z as [Hz| Hnz].
   rewrite Hz; simpl.
   reflexivity.

   rewrite Qdiv_mul; [ idtac | assumption | assumption ].
   unfold Qeq.
   simpl.
   do 2 rewrite Pos2Z.inj_mul.
   rewrite Z.mul_comm; symmetry.
   rewrite Z.mul_comm; symmetry.
   do 2 rewrite <- Z.mul_assoc.
   apply Z.mul_cancel_l; [ apply Zpos_ne_0 | idtac ].
   rewrite Zmult_1_r.
   pose proof (Z.gcd_divide_r (mj - mk) (k - j)) as H.
   destruct H as (u, Hu).
   rewrite <- Hg in Hu.
   rewrite Hu.
   rewrite Z_div_mult_full.
    pose proof (Z.gcd_divide_l (mj - mk) (k - j)) as H.
    destruct H as (v, Hv).
    rewrite <- Hg in Hv.
    rewrite Hv.
    rewrite Z_div_mult_full.
     rewrite Z2Pos.id.
      rewrite Z2Pos.id.
       rewrite Z.mul_shuffle0, Z.mul_assoc; reflexivity.

       rewrite <- Hu; assumption.

      remember Hkj as H; clear HeqH.
      rewrite Hu in H.
      eapply Zmult_lt_0_reg_r; [ idtac | eassumption ].
      destruct g.
       symmetry in Hg.
       rewrite Zmult_0_r in Hv.
       contradiction.

       apply Pos2Z.is_pos.

       pose proof (Z.gcd_nonneg (mj - mk) (k - j)) as Hgp.
       rewrite <- Hg in Hgp.
       apply Zle_not_lt in Hgp.
       exfalso; apply Hgp.
       apply Zlt_neg_0.
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
subst hsl.
remember (List.nth (Z.to_nat (Qnum j)) psl (an pol)) as jps.
eapply in_pts_in_pol in Heqjps; try eassumption.
 2: subst j; rewrite <- surjective_pairing.
 2: apply ini_fin_ns_in_init_pts; assumption.

 destruct Heqjps as (Hjps, Hjv).
 rewrite <- Heqαj in Hjv.
 apply Hi in Hjv; [ idtac | assumption ].
 destruct Hjv as (mj, Hαj).
 remember (List.nth (Z.to_nat (Qnum k)) psl (an pol)) as kps.
 eapply in_pts_in_pol in Heqkps; try eassumption.
  2: subst k; rewrite <- surjective_pairing.
  2: apply ini_fin_ns_in_init_pts; assumption.

  destruct Heqkps as (Hkps, Hkv).
  rewrite <- Heqαk in Hkv.
  apply Hi in Hkv; [ idtac | assumption ].
  destruct Hkv as (mk, Hαk).
  rewrite Hg.
  setoid_rewrite Hαj.
  setoid_rewrite Hαk.
  remember (Z.gcd (mj - mk) (Qnum k - Qnum j)) as g.
  exists ((mj - mk) / g)%Z.
  exists (Z.to_pos ((Qnum k - Qnum j) / g)).
  split.
   destruct k as (kn, kd).
   destruct j as (jn, jd).
   simpl.
   replace jd with 1%positive in Heqg |- * .
    replace kd with 1%positive in Heqg |- * .
     simpl in Heqg.
     apply yyy; assumption.
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
