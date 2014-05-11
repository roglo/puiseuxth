(* Puiseux.v *)

Require Import Utf8.
Require Import QArith.

Require Import Misc.
Require Import Field.
Require Import Fpolynomial.
Require Import Newton.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Puiseux_base.
Require Import AlgCloCharPol.
Require Import CharactPolyn.
Require Import F1Eq.
Require Import F1Prop.

Set Implicit Arguments.

(*
Fixpoint root_loop α {R : ring α} {K : field R} {acf : algeb_closed_field K}
    (pol : polynomial (puiseux_series α)) ns c₁ γ_sum :=
  let f₁ := pol₁ pol (β ns) (γ ns) c₁ in
  match newton_segments f₁ with
  | [] => 0%ps
  | [ns₁ … _] =>
      let c₂ := ac_root (Φq f₁ ns₁) in
      let t₂ := ps_monom c₂ (γ_sum + γ ns₁) in
      (t₂ + root_loop pol ns c₂ (γ_sum + γ ns₁)%Q)%ps
  end.

Definition root α {R : ring α} {K : field R} {acf : algeb_closed_field K}
    (pol : polynomial (puiseux_series α)) :=
  match newton_segments pol with
  | [] => 0%ps
  | [ns … _] =>
      let c₁ := ac_root (Φq pol ns) in
      let t₁ := ps_monom c₁ (γ ns) in
      (t₁ + root_loop pol ns c₁ (γ ns))%ps
  end.
*)
