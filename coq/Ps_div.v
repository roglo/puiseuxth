(* $Id: Ps_div.v,v 1.3 2013-12-10 23:18:13 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Nbar.
Require Import Series.
Require Import Puiseux_series.
Require Import Ps_mul.

Set Implicit Arguments.

(* à revoir !!! il faut que le premier coefficient ne soit pas nul;
   donc utiliser null_coeff_range_length pour shifter la série de
   Puiseux d'abord *)
bbb.

Fixpoint term_inv c s n :=
  if zerop n then Lfield.inv fld (series_nth rng O s)
  else
    match c with
    | O => Lfield.zero rng
    | S c₁ =>
        (- Lfield.inv fld (series_nth rng 0 s) *
         Σ (i = 1, n)   series_nth rng i s * term_inv c₁ s (n - i)%nat)%rng
    end.

Definition series_inv s :=
  {| terms i := term_inv i s i;
     stop := ∞ |}.

Definition ps_inv ps :=
  {| ps_terms := series_inv (ps_terms ps);
     ps_valnum := - ps_valnum ps;
     ps_comden := ps_comden ps |}.

Lemma eq_strong_eq : ∀ ps₁ ps₂, ps₁ ≐ ps₂ → (ps₁ = ps₂)%ps.
Proof.
intros ps₁ ps₂ Heq.
constructor.
rewrite Heq.
reflexivity.
Qed.

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

Theorem ps_mul_inv_l : ∀ ps, (ps ≠ 0)%ps → (ps_inv ps * ps = 1)%ps.
Proof.
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
