(* $Id: Series.v,v 1.4 2013-06-01 02:15:53 deraugla Exp $ *)

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

Fixpoint ser_nth_tl α (n : nat) (s : series α) : option (series α) :=
  match n with
  | O => Some s
  | S m =>
      match ser_tl s with
      | None => None
      | Some t => ser_nth_tl m t
      end
  end.

Definition ser_nth α (n : nat) (s : series α) : option α :=
  match ser_nth_tl n s with
  | None => None
  | Some t => ser_hd t
  end.

CoFixpoint ser_map α β (f : α → β) s :=
  match s with
  | Term a t => Term (f a) (ser_map f t)
  | End => End _
  end.
