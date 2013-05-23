(* $Id: Series.v,v 1.1 2013-05-23 23:40:22 deraugla Exp $ *)

Require Import Utf8.

Set Implicit Arguments.

CoInductive series α := Term : α → series α → series α | End : series α.

Definition ser_hd α (s : series α) :=
  match s with
  | Term a _ => Some a
  | End => None
  end.

Definition ser_tl α (s : series α) : option (series α) :=
  match s with
  | Term _ t => Some t
  | End => None
  end.
