(* $Id: Ps_div.v,v 1.7 2013-12-11 18:11:35 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Nbar.
Require Import Series.
Require Import Puiseux_series.
Require Import Ps_mul.

Set Implicit Arguments.

Definition ps_inv ps :=
  match null_coeff_range_length rng (ps_terms ps) O with
  | fin n =>
      {| ps_terms := series_inv (series_shift n (ps_terms ps));
         ps_valnum := Z.of_nat n - ps_valnum ps;
         ps_comden := ps_comden ps |}
  | ∞ =>
      ps
  end.

Lemma series_left_shift_0 : ∀ s, (series_left_shift 0 s = s)%ser.
Proof.
intros s.
unfold series_left_shift.
rewrite Nbar.sub_0_r; simpl.
destruct s; reflexivity.
Qed.

Lemma series_shrink_1 : ∀ s, (series_shrink 1 s = s)%ser.
Proof.
intros s.
unfold series_shrink; simpl.
rewrite Nbar.fold_sub.
rewrite Nbar.add_sub; [ idtac | intros H; discriminate H ].
remember (stop s) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ].
 rewrite divmod_div.
 rewrite Nat.div_1_r.
 constructor; intros n.
 unfold series_nth; simpl.
 rewrite Nat.mul_1_r.
 rewrite Hst; reflexivity.

 constructor; intros n.
 unfold series_nth; simpl.
 rewrite Nat.mul_1_r.
 rewrite Hst; reflexivity.
Qed.

Lemma canonic_ps_1 : canonic_ps 1%ps ≐ 1%ps.
Proof.
remember (null_coeff_range_length rng (ps_terms 1%ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 destruct n.
  Focus 2.
  apply null_coeff_range_length_iff in Hn; simpl in Hn.
  destruct Hn as (_, Hn).
  unfold series_nth in Hn.
  simpl in Hn.
  exfalso; apply Hn.
  destruct (Nbar.lt_dec (fin (S n)) 1) as [H₁| H₁].
   apply Nbar.nle_gt in H₁.
   exfalso; apply H₁.
   apply Nbar.fin_le_mono.
   apply le_n_S, Nat.le_0_l.

   reflexivity.

  constructor; simpl.
   erewrite ps_valnum_canonic; try reflexivity; try eassumption.
   simpl.
   rewrite Pos2Z.inj_gcd.
   rewrite Z.gcd_1_l.
   rewrite Z.div_1_r.
   reflexivity.

   erewrite ps_comden_canonic; try reflexivity; try eassumption.
   reflexivity.

   erewrite ps_terms_canonic; try reflexivity; try eassumption.
   remember Z.to_pos as f; simpl; subst f.
   rewrite Pos2Z.inj_gcd.
   rewrite Z.gcd_1_l.
   unfold canonify_series; simpl.
   rewrite series_shrink_1.
   rewrite series_left_shift_0; reflexivity.

 apply null_coeff_range_length_inf_iff in Hn.
 exfalso; revert Hn; apply ps_neq_1_0.
Qed.

(* faux car ne peut s'appliquer que sur les séries non nulles...
Add Parametric Morphism : series_inv
  with signature eq_series ==> eq_series
  as series_inv_morph.
Proof.
intros a b Hab.
constructor; intros i.
inversion Hab; subst.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) ∞) as [H₁| ]; [ idtac | reflexivity ].
clear H₁.
induction i; intros.
 simpl.
bbb.
rewrite H.

 pose proof (H O) as H₀.
 unfold series_nth; simpl.
 unfold series_nth in H₀.
 destruct (Nbar.lt_dec 0 (stop a)) as [H₁| H₁].
  destruct (Nbar.lt_dec 0 (stop b)) as [H₂| H₂].
   simpl.
bbb.
*)

(*
Lemma zzz : ∀ a,
  (a ≠ 0)%ser
  → (series_inv (series_shift 0 a) = a)%ser.
Proof.
intros a Ha.
bbb.
*)

(* do not work with Add Morphism 'cause a must be non null:
   is it possible to add a morphism with a condition?
Lemma xxx : ∀ a b i,
  (a ≠ 0)%ser
  → (a = b)%ser
    → (term_inv i a i = term_inv i b i)%rng.
Proof.
intros a b i Ha Hab.
bbb.
(* mmm... *)
induction i.
 simpl.
 unfold series_nth; simpl.
 destruct (Nbar.lt_dec 0 (stop a)) as [H₁| H₁].
  destruct (Nbar.lt_dec 0 (stop b)) as [H₂| H₂].
   inversion Hab; subst.
   pose proof (H O) as HH.
   apply Lfield.inv_compat.
    intros HHH; apply Ha.
    constructor; intros i.
    rewrite series_nth_series_0.
    rewrite H.
bbb.
*)

Lemma yyy : ∀ a b,
  (a ≠ 0)%ser
  → (a = b)%ser
    → (series_inv a = series_inv b)%ser.
Proof.
intros a b Ha Hab.
apply series_mul_compat_l with (c := series_inv a) in Hab.
apply series_mul_compat_r with (c := series_inv b) in Hab.
bbb.

intros a b Ha Hab.
constructor; intros i.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) ∞) as [H₁| ]; [ idtac | reflexivity ].
bbb.

Theorem ps_mul_inv_l : ∀ ps, (ps ≠ 0)%ps → (ps_inv ps * ps = 1)%ps.
Proof.
intros ps Hps.
unfold ps_inv; simpl.
remember (null_coeff_range_length rng (ps_terms ps) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ].
 destruct n.
bbb.
rewrite yyy.

intros ps Hps.
remember (ps_terms (ps_inv ps * ps)%ps) as s.
remember (null_coeff_range_length rng s 0) as n eqn:Hn ; subst s.
symmetry in Hn.
destruct n as [n| ].
 destruct n.
  constructor; constructor; simpl.
   erewrite ps_valnum_canonic; try reflexivity; try eassumption.
   pose proof canonic_ps_1 as H.
   inversion H; subst.
   rewrite H0; simpl.
   clear H H0 H1 H2.
   rewrite Z.mul_opp_l, Z.add_opp_diag_l; simpl.
   rewrite Z.div_0_l; [ reflexivity | apply Pos2Z_ne_0 ].

   erewrite ps_comden_canonic; try reflexivity; try eassumption.
   pose proof canonic_ps_1 as H.
   inversion H; subst.
   rewrite H1.
   clear H H0 H1 H2.
   remember Z.gcd as f; simpl; subst f.
   unfold cm, cm_factor.
   remember Z.gcd as f; simpl; subst f.
bbb.
