(* Puiseux.v *)

Require Import Utf8.

Require Import Misc.
Require Import Field.
Require Import Fpolynomial.
Require Import Puiseux_series.
Require Import Puiseux_base.
Require Import F1Prop.

Set Implicit Arguments.

Definition root α {R : ring α} (pol : polynomial (puiseux_series α)) :=
  match newton_segments pol with
  | [] => 0%ps
  | [ns … _] => 0%ps
  end.
