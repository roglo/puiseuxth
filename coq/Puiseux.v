(* Puiseux.v *)

Require Import Utf8.

Require Import Misc.
Require Import Field.
Require Import Fpolynomial.
Require Import Puiseux_series.
Require Import Puiseux_base.
Require Import AlgCloCharPol.
Require Import CharactPolyn.
Require Import Newton.
Require Import F1Prop.

Set Implicit Arguments.

Definition root α {R : ring α} {K : field R} {acf : algeb_closed_field K}
    (pol : polynomial (puiseux_series α)) :=
  match newton_segments pol with
  | [] => 0%ps
  | [ns … _] => ps_monom (ac_root (Φq pol ns)) (γ ns)
  end.
