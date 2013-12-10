(* $Id: Ps_div.v,v 1.1 2013-12-10 21:41:13 deraugla Exp $ *)

Require Import Utf8.
Require Import ZArith.

Require Import Nbar.
Require Import Series.
Require Import Puiseux_series.
Require Import Ps_mul.

Set Implicit Arguments.

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

Theorem ps_mul_inv_l : ∀ ps, (ps ≠ 0)%ps → (ps_inv ps * ps = 1)%ps.
Proof.
intros ps Hps.
remember (ps_terms (ps_inv ps * ps)%ps) as s.
remember (null_coeff_range_length rng s 0) as n eqn:Hn ; subst s.
symmetry in Hn.
destruct n as [n| ].
 constructor; constructor; simpl.
  erewrite ps_valnum_canonic; try reflexivity; try eassumption.
  remember (null_coeff_range_length rng 1%ser 0) as m eqn:Hm .
  symmetry in Hm.
  destruct m as [m| ].
   erewrite ps_valnum_canonic; try reflexivity; try eassumption.
   simpl.
bbb.
