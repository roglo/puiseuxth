(* $Id: Puiseux.v,v 1.1072 2013-08-12 09:41:26 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import ConvexHullMisc.
Require Import Field.
Require Import Fpolynomial.
Require Import Misc.
Require Import Newton.
Require Import Polynomial.
Require Import Puiseux_base.
Require Import Puiseux_series.
Require Import Series.
Require Import CharactPolyn.

Set Implicit Arguments.

(* *)

Definition ps_zero α (fld : field α) :=
  {| ps_terms := {| terms i := zero fld; stop := Some O |};
     ps_valnum := 0;
     ps_comden := 1 |}.

Definition ps_const α c : puiseux_series α :=
  {| ps_terms := {| terms i := c; stop := Some 1%nat |};
     ps_valnum := 0;
     ps_comden := 1 |}.

Definition ps_one α (fld : field α) := ps_const (one fld).

Definition x_power α (fld : field α) pow :=
  {| ps_terms := {| terms i := one fld; stop := Some 1%nat |};
     ps_valnum := Qnum pow;
     ps_comden := Qden pow |}.

Definition apply_poly_with_ps_poly α (fld : field α) pol :=
  apply_poly
    (λ ps, {| al := []; an := ps |})
    (λ pol ps, pol_add (ps_add fld) pol {| al := []; an := ps |})
    (pol_mul (ps_zero fld) (ps_add fld) (ps_mul fld))
    pol.

Definition pol_mul_x_power_minus α (fld : field α) p pol :=
  pol_mul (ps_zero fld) (ps_add fld) (ps_mul fld)
    {| al := []; an := x_power fld (Qopp p) |} pol.

Definition zero_is_root α fld (pol : polynomial (puiseux_series α)) :=
  match al pol with
  | [] => false
  | [ps … _] =>
      match series_head (fld_eq fld (zero fld)) 0 (ps_terms ps) with
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
  pol_mul_x_power_minus fld β pol.

(* *)

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

Fixpoint puiseux_comden α n cd (s : series (term α Q)) :=
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

Section field.

Variable α : Type.
Variable acf : algeb_closed_field α.
Let fld := ac_field acf.

(*
Axiom ps_eq : puiseux_series α → puiseux_series α → bool.
Axiom ps_eq_refl : ∀ ps, ps_eq ps ps = true.
Axiom ps_eq_comm : ∀ ps₁ ps₂, ps_eq ps₁ ps₂ = ps_eq ps₂ ps₁.
Axiom ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  ps_eq
    (ps_add fld (ps_add fld ps₁ ps₂) ps₃)
    (ps_add fld ps₁ (ps_add fld ps₂ ps₃)) = true.
*)

(*
Axiom ps_eq_add_comm : ∀ ps₁ ps₂,
  ps_eq (ps_add fld ps₁ ps₂) (ps_add fld ps₂ ps₁) = true.
cf Puiseux_series.ps_add_comm
*)

Definition ps_fld : field (puiseux_series α) :=
  {| zero := ps_zero _;
     one := ps_one fld;
     add := ps_add fld;
     mul := ps_mul fld;
     fld_eq := ps_eq;
     fld_eq_refl := ps_eq_refl;
     fld_eq_sym := ps_eq_sym;
     fld_add_comm := ps_eq_add_comm;
     fld_add_assoc := ps_add_assoc |}.

(* *)

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

 rewrite minus_diag; simpl.
 apply le_n_S, le_0_n.
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

Lemma jh_oppsl_eq_p_nq : ∀ pol ns j αj k αk h αh m,
  ns ∈ newton_segments fld pol
  → (j, αj) = ini_pt ns
    → (k, αk) = fin_pt ns
      → (h, αh) ∈ oth_pts ns
        → m = series_list_com_den (al pol ++ [an pol])
          → ∃ p q,
            (αj - αh) / (h - j) == p # (m * q) ∧
            (αj - αk) / (k - j) == p # (m * q) ∧
            Z.gcd p (' q) = 1%Z.
Proof.
intros pol ns j αj k αk h αh m Hns Hj Hk Hh Hm.
eapply gamma_eq_p_nq in Hm; [ idtac | eassumption ].
destruct Hm as (p, (q, H)).
exists p, q.
destruct H as (Hgamma, Hgcd).
split.
 setoid_rewrite  <- gamma_value_jh; eassumption.

 split; [ idtac | assumption ].
 setoid_rewrite  <- gamma_value_jk; try eassumption.
Qed.

Lemma list_pad_app : ∀ n v cl,
  list_eq (fld_eq fld) (list_pad n v cl) (list_pad n v [] ++ cl) = true.
Proof.
intros n v cl.
revert v cl.
induction n; intros; simpl.
 apply list_eq_refl.

(*
 rewrite fld_eq_refl; apply IHn.
*)
 apply IHn.
qed.

Lemma empty_padded : ∀ n v c,
  c ∈ list_pad n v []
  → fld_eq fld c v = true.
Proof.
intros n v c H.
induction n; [ contradiction | idtac ].
destruct H as [H| H].
 subst v; reflexivity.

 apply IHn, H.
Qed.

Lemma padded : ∀ n v c cl,
  list_pad n v [] = [c … cl]
  → fld_eq fld c v = true.
Proof.
intros n v c cl H.
destruct n; [ discriminate H | simpl in H ].
injection H; clear H; intros; subst c cl.
reflexivity.
Qed.

Lemma list_nth_pad_ge : ∀ i s (v : α) cl d,
  (s ≤ i)%nat
  → List.nth i (list_pad s v cl) d = List.nth (i - s) cl d.
Proof.
intros i s v cl d Hsi.
symmetry.
rewrite <- list_nth_plus_pad with (s := s) (v := v).
f_equal.
rewrite plus_comm.
symmetry.
apply le_plus_minus; assumption.
Qed.

Lemma make_char_pol_S : ∀ pow t tl k,
  (pow < power t)%nat
  → make_char_pol fld pow [t … tl] k =
    [zero fld … make_char_pol fld (S pow) [t … tl] k].
Proof.
intros pow t tl k Hpow.
simpl.
rewrite <- Nat.sub_succ.
rewrite <- minus_Sn_m; [ reflexivity | assumption ].
Qed.

Lemma nth_S_pad_S : ∀ i n v tl (d : α),
  List.nth (S i) (list_pad (S n) v tl) d =
  List.nth i (list_pad n v tl) d.
Proof. reflexivity. Qed.

Lemma list_pad_length : ∀ n (v : α) tl,
  List.length (list_pad n v tl) = (n + List.length tl)%nat.
Proof.
intros n v tl.
induction n; [ reflexivity | simpl; rewrite IHn; reflexivity ].
Qed.

Lemma nth_minus_char_pol_plus_nil : ∀ i j s k d,
  s ≤ i
  → j + s ≤ k
    → List.nth (i - s) (make_char_pol fld (j + s) [] k) d =
      List.nth i (make_char_pol fld j [] k) d.
Proof.
intros i j s k d Hsi Hjsk.
revert i j k d Hsi Hjsk.
induction s; intros.
 rewrite plus_0_r, Nat.sub_0_r; reflexivity.

 symmetry.
 rewrite <- IHs.
  destruct i.
   exfalso; revert Hsi; apply le_Sn_0.

   apply le_S_n in Hsi.
   rewrite Nat.sub_succ.
   rewrite <- minus_Sn_m; [ idtac | assumption ].
   rewrite <- plus_n_Sm.
   simpl.
   remember (S (i - s)) as x.
   rewrite <- Nat.sub_succ; subst x.
   rewrite <- minus_Sn_m; [ apply nth_S_pad_S | idtac ].
   rewrite plus_n_Sm; assumption.

  apply lt_le_weak; assumption.

  rewrite <- plus_n_Sm in Hjsk.
  apply lt_le_weak; assumption.
Qed.

(* *)

(*
Delimit Scope ps with puiseux_series.
Notation "x * y" := (ps_mul fld x y) : ps.

Open Scope ps.
*)

Definition abar (pol : polynomial (puiseux_series α)) h :=
  List.nth h (al pol) (an pol).

Definition ps_pol_add := pol_add (add ps_fld).
Definition ps_pol_mul := pol_mul (zero ps_fld) (add ps_fld) (mul ps_fld).

Fixpoint ps_pol_power pol n :=
  match n with
  | O => {| al := []; an := one ps_fld |}
  | S n₁ => ps_pol_mul pol (ps_pol_power pol n₁)
  end.

Lemma normal_terms_end : ∀ n cd, normal_terms fld n cd (End α) = End α.
Proof.
intros n cd.
symmetry.
rewrite series_eta.
reflexivity.
Qed.

Lemma normal_terms_0 : ∀ s, normal_terms fld 0 0 s = s.
Proof.
intros s.
apply ext_eq_ser with (fld := fld).
revert s.
cofix IHs; intros.
destruct s as [t s| ].
 eapply eq_ser_term; [ idtac | reflexivity | reflexivity | apply IHs ].
 symmetry; rewrite series_eta; reflexivity.

 apply eq_ser_end; [ idtac | reflexivity ].
 symmetry; rewrite series_eta; reflexivity.
Qed.

Lemma series_add_end_l : ∀ s, series_add fld (End α) s = s.
Proof.
intros s.
symmetry.
rewrite series_eta.
simpl.
destruct s; reflexivity.
Qed.

Lemma ps_add_0_r : ∀ ps, ps_add fld ps (ps_zero α) = ps.
Proof.
intros ps.
rewrite ps_add_comm.
unfold ps_add.
rewrite Zminus_0_r.
rewrite Plcm_1_l.
rewrite Nat.div_same.
 rewrite Nat.div_1_r.
 simpl.
 rewrite Zmult_1_r.
 rewrite normal_terms_end.
 rewrite series_add_end_l.
 remember (ps_valnum ps) as v.
 symmetry in Heqv.
 destruct v as [| n| n].
  destruct ps; simpl in Heqv |- *; rewrite Heqv.
  f_equal.
  apply normal_terms_0.

  rewrite series_add_end_l.
  destruct ps; simpl in Heqv |- *; rewrite Heqv.
  rewrite normal_terms_0.
bbb.

Lemma zzz : ∀ pol pts ns cpol c₁ r₁,
  pts = points_of_ps_polynom fld pol
  → ns ∈ newton_segments fld pol
    → cpol = characteristic_polynomial fld pol ns
      → ac_root acf cpol = (c₁, r₁)
        → f₁ fld pol (β ns) (γ ns) c₁
          = pol_mul_x_power_minus fld (β ns)
              (List.fold_right
                 (λ ips accu,
                    ps_pol_add
                      (ps_pol_mul
                         {| al := [];
                            an :=
                              ps_mul fld (snd ips)
                                (x_power fld (Qnat (fst ips) * γ ns)%Q) |}
                      (ps_pol_power
                         {| al := [ps_const c₁]; an := ps_one fld |}
                         (fst ips)))
                      accu)
                 {| al := []; an := ps_zero _ |}
                 (power_list O (al pol) (an pol))).
Proof.
intros pol pts ns cpol c₁ r₁ Hpts Hns Hcpol Hcr.
unfold poly_eq; simpl.
unfold f₁.
unfold apply_poly_with_ps_poly, apply_poly.
unfold ps_one, abar.
unfold newton_segments in Hns.
rewrite <- Hpts in Hns.
unfold points_of_ps_polynom in Hpts.
unfold characteristic_polynomial, term_of_point in Hcpol.
simpl in Hcpol.
remember (an pol) as cn; clear Heqcn.
remember (al pol) as cl; clear Heqcl.
unfold nofq in Hcpol.
clear pol cpol Hcpol Hcr r₁.
unfold ps_pol_mul, ps_fld; simpl.
unfold ps_pol_add.
remember 0%nat as n; clear Heqn.
revert pts ns c₁ cn n Hpts Hns.
induction cl as [| c]; intros.
 simpl.
 unfold pol_add; simpl.
 unfold pol_mul; simpl.
 destruct n.
  simpl.
(*
  rewrite andb_true_r.
*)
  unfold x_power; simpl.
  Focus 1.
bbb.

(*
Theorem has_neg_slope : ∀ pol ns cpol (c : α) r pol₁,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial fld pol ns
    → (c, r) = ac_root acf cpol
      → pol₁ = f₁ fld pol (β ns) (γ ns) c
        → ∃ ns₁, ns₁ ∈ newton_segments fld pol₁ → γ ns₁ > 0.
Proof.
bbb.
*)

End field.
